// envelope-header-filter.cpp
// vi:set et ts=2 sw=2:
//
// An OpenSMTPD "proc" filter (see smtpd-filters(7)) that runs early in a
// filter chain and, for every message accepted into the DATA phase:
//
//   1. Renames any pre-existing header that matches the filter's target
//      names -- X-Envelope-To / X-Envelope-From by default -- by
//      prepending one more "X-", preserving nesting:
//
//          X-Envelope-To      -> X-X-Envelope-To
//          X-X-Envelope-To    -> X-X-X-Envelope-To
//          X-X-X-Envelope-To  -> X-X-X-X-Envelope-To
//          (and likewise for Envelope-From)
//
//   2. Inserts new X-Envelope-From / X-Envelope-To headers at the top of
//      the header block, carrying the SMTP envelope's MAIL FROM address
//      and RCPT TO address(es), without the surrounding "<" / ">" -- except
//      that a null sender (MAIL FROM:<>) yields an empty header value.
//
// The intent is that a later filter or sieve script can rely on these
// headers for sorting, without a spoofed/forwarded copy of the same header
// name confusing it -- hence the "push down" renaming instead of an
// overwrite.
//
// To build:
//   c++ -std=c++23 -O2 -Wall -Wextra \
//     -o opensmtpd-filter-envelope-headers envelope-header-filter.cpp
//
// To use:
// Add to smtpd.conf as a filter:
//   filter "envhdr" proc-exec \
//     "/usr/local/libexec/opensmtpd/opensmtpd-filter-envelope-headers"
// (optional) Add to a filter chain:
//   filter "fc_inbound" chain {"envhdr", "rspamd"}
// Add to `listen` statements:
//   listen on all filter "fc_inbound"
//
// Implementation notes:
// - Only the "smtp-in" subsystem exists in the current filter API.
// - Envelope data is gathered from the lightweight *report* stream
//   (tx-mail / tx-rcpt), which needs no reply, rather than the *filter*
//   stream, per the pattern recommended by smtpd-filters(7). Only
//   "data-line" is registered as an actual filter, since that's the only
//   phase where message content can be rewritten.
// - Session state is keyed by OpenSMTPD's session id, which is shared
//   between report events and filter requests for that connection.
// - stdin/stdout is used with simple blocking reads. Since every
//   response is produced synchronously in reaction to the single line
//   that triggered it, and OpenSMTPD serializes requests on the same
//   stream, this does not deadlock -- there is never a reason for this
//   filter to wait on anything other than its next input line.
// - The protocol allows "|" to appear only in a payload's last field.
//   Fields are therefore parsed by popping the known fixed fields off
//   the front and treating whatever remains as the final field verbatim
//   (important for header lines during "data-line", which may
//   legitimately contain "|").

#include <cctype>
#include <cstdio>
#include <iostream>
#include <print>
#include <string>
#include <string_view>
#include <unordered_map>
#include <vector>

namespace {
// The filter adds headers named "X-" + these, and renames any pre-existing
// header matching (X-)+<name> (case-insensitive, any nesting depth) by
// prepending one more "X-". Must not contain ':'.
constexpr std::string_view envelope_from_header = "Envelope-From";
constexpr std::string_view envelope_to_header = "Envelope-To";

enum class RecipientFormat {
  CommaSeparated, // One "X-Envelope-To" header, addresses joined by ", ".
  OneHeaderPerRecipient // One "X-Envelope-To" header line per recipient.
};

// Active choice for how multiple RCPT TO recipients are represented.
constexpr RecipientFormat header_style
  = RecipientFormat::OneHeaderPerRecipient;

// Pops the substring before the next `delim` off the front of `input` and
// returns it, advancing `input` past the delimiter. If `delim` does not occur,
// the entire remaining `input` is returned and `input` is left empty
std::string_view PopField(std::string_view& input, char delim='|') {
  size_t pos = input.find(delim);
  if (pos == std::string_view::npos) {
    std::string_view field = input;
    input = std::string_view();
    return field;
  }
  std::string_view field = input.substr(0, pos);
  input.remove_prefix(pos + 1);
  return field;
}

// Compare lhs and rhs, case-insensitively (ascii case, anyway)
bool EqualNoCase(std::string_view lhs, std::string_view rhs) {
  if (lhs.size() != rhs.size()) return false;
  for (size_t ii=0; ii<lhs.size(); ++ii) {
    if (std::tolower(static_cast<unsigned char>(lhs[ii]))
        != std::tolower(static_cast<unsigned char>(rhs[ii])))
    {
      return false;
    }
  }
  return true;
}

// True if `name` is exactly one-or-more literal "X-" prefixes followed by
// `base`, compared case-insensitively -- e.g. for base "Envelope-To":
// "X-Envelope-To", "x-X-Envelope-To", "X-X-X-Envelope-To", ...
bool MatchesEnvelopeHeader(std::string_view name, std::string_view base) {
  if (name.size() <= base.size()) {
    return false;
  }
  const size_t prefix_len = name.size() - base.size();
  if ((prefix_len % 2) != 0) {
    return false;
  }
  if (! EqualNoCase(name.substr(prefix_len), base)) {
    return false;
  }
  for (size_t ii=0; ii<prefix_len; ii+=2) {
    if (! ((name[ii] == 'x' || name[ii] == 'X') && name[ii + 1] == '-')) {
      return false;
    }
  }
  return true;
}

// Strips a single pair of surrounding '<' '>' if both are present.
[[maybe_unused]]
std::string StripAngleBrackets(std::string_view input) {
  if ((input.size() >= 2) && (input.front() == '<') && (input.back() == '>')) {
    return std::string(input.substr(1, input.size() - 2));
  }
  return std::string(input);
}

// Add the leading X- and produce the header line
std::string MakeHeaderLine(std::string_view base_name, std::string_view value) {
  std::string line = "X-";
  line += base_name;
  line += ": ";
  line += value;
  return line;
}

// Envelope information gathered from the report stream for one SMTP
// session. Reset appropriately as new transactions occur.
struct EnvelopeState {
  std::vector<std::string> rcpt_to;
  std::string mail_from;
  bool has_mail_from = false;
};

// State for an in-progress "data-line" rewrite for one session.
// The whole header block is buffered (rather than streamed line-by-line)
// so new X-Envelope-* headers can be put up at the top of the block,
// ahead of every existing (possibly renamed) header
struct DataLineState {
  // A header may span multiple lines, so this is the accumulating, in-flight
  // header. It gets moved to finalized_headers.
  std::vector<std::string> pending_header;
  // Every header line, in original order, renamed when applicable
  // (folded/multi-line headers are still multiple elements of the vector)
  std::vector<std::string> finalized_headers;
  bool headers_done = false;
};

// Global state
std::unordered_map<std::string, EnvelopeState> g_envelopes;
std::unordered_map<std::string, DataLineState> g_datalines;

void EmitDataLine(std::string_view session, std::string_view token,
    std::string_view content)
{
  std::println("filter-dataline|{}|{}|{}", session, token, content);
}

void EmitNewEnvelopeHeaders(const EnvelopeState& env, std::string_view session,
    std::string_view token)
{
  const std::string& mail_from
    = env.has_mail_from ? env.mail_from : std::string("<>");
  EmitDataLine(session, token,
      MakeHeaderLine(envelope_from_header, mail_from));

  if (! env.rcpt_to.empty()) {
    if (header_style == RecipientFormat::CommaSeparated) {
      std::string joined_rcpts;
      bool first = true;
      for (const auto& rcpt : env.rcpt_to) {
        if (first) {
          first = false;
        }
        else {
          joined_rcpts += ", ";
        }
        joined_rcpts += rcpt;
      }
      EmitDataLine(session, token,
          MakeHeaderLine(envelope_to_header, joined_rcpts));
    }
    else { // RecipientFormat::OneHeaderPerRecipient
      for (const auto& rcpt : env.rcpt_to) {
        EmitDataLine(session, token, MakeHeaderLine(envelope_to_header, rcpt));
      }
    }
  }
}

// Finalizes the currently-accumulating header (if any) by
// renaming it if necessary, and moving it to finalized_headers
void FinalizeCurrentHeader(DataLineState& state) {
  if (state.pending_header.empty()) {
    return;
  }

  std::string& first = state.pending_header.front();
  size_t colon_pos = first.find(':');
  if (colon_pos != std::string::npos) {
    std::string_view name(first.data(), colon_pos);
    if (MatchesEnvelopeHeader(name, envelope_from_header)
        || MatchesEnvelopeHeader(name, envelope_to_header))
    {
      first.insert(0, "X-");
    }
  }

  for (auto& header_line : state.pending_header) {
    state.finalized_headers.push_back(std::move(header_line));
  }
  state.pending_header.clear();
}

// Emits the new X-Envelope-* headers followed by every finalized (and
// possibly renamed) original header, in that order
void FlushHeaderBlock(DataLineState& state, const EnvelopeState& env,
    std::string_view session, std::string_view token)
{
  EmitNewEnvelopeHeaders(env, session, token);
  for (const auto& header_line : state.finalized_headers) {
    EmitDataLine(session, token, header_line);
  }
  state.finalized_headers.clear();
}

void ProcessDataLine(const std::string& session, const std::string& token,
                      std::string_view line)
{
  DataLineState& state = g_datalines[session];
  EnvelopeState& env = g_envelopes[session];

  const bool is_data_end = (line == ".");
  const bool is_continuation = (! line.empty())
    && (line.front() == ' ' || line.front() == '\t');

  if (! state.headers_done) {
    if (line.empty() || is_data_end) {
      // end of headers
      FinalizeCurrentHeader(state);
      FlushHeaderBlock(state, env, session, token);
      state.headers_done = true;
      EmitDataLine(session, token, line); // emit current line
    }
    else if (is_continuation) {
      // Continuation of the header currently being accumulated.
      state.pending_header.emplace_back(line);
    }
    else {
      // Start of a new header field; the previous one (if any) is complete.
      FinalizeCurrentHeader(state);
      state.pending_header.emplace_back(line);
    }
  }
  else {
    // Body line: pass through without modification
    EmitDataLine(session, token, line);
  }

  if (is_data_end) {
    g_datalines.erase(session);
  }
}

void ProcessReport(std::string_view report) {
  PopField(report, '|');  // version
  PopField(report, '|');  // timestamp
  PopField(report, '|');  // subsystem
  std::string_view event = PopField(report, '|');
  std::string session(PopField(report, '|'));

  if (event == "tx-mail") {
    PopField(report, '|');  // message-id
    std::string_view result = PopField(report, '|');
    std::string_view address = report;  // final field
    if (result == "ok") {
      // OpenSMTPD has already stripped < and >
      EnvelopeState& env = g_envelopes[session];
      env.mail_from = address;
      env.has_mail_from = true;
      env.rcpt_to.clear();
    }
  }
  else if (event == "tx-rcpt") {
    PopField(report, '|');  // message-id
    std::string_view result = PopField(report, '|');
    std::string_view address = report;  // final field
    if (result == "ok") {
      // OpenSMTPD has already stripped < and >
      g_envelopes[session].rcpt_to.emplace_back(address);
    }
  }
  else if (event == "link-disconnect") {
    g_envelopes.erase(session);
    g_datalines.erase(session);
  }
  // Other (unregistered) events are never delivered to us.
}

void ProcessFilter(std::string_view report) {
  PopField(report, '|');  // version
  PopField(report, '|');  // timestamp
  PopField(report, '|');  // subsystem
  std::string_view phase = PopField(report, '|');
  std::string session(PopField(report, '|'));
  std::string token(PopField(report, '|'));
  if (phase != "data-line") {
    // We only ever registered for "data-line", so this shouldn't happen.
    return;
  }
  std::string_view line = report;  // final field, may itself contain '|'
  ProcessDataLine(session, token, line);
}

void ProcessProtocolLine(std::string_view line) {
  std::string_view report = line;
  std::string_view stream = PopField(report, '|');
  if (stream == "report") {
    ProcessReport(report);
  }
  else if (stream == "filter") {
    ProcessFilter(report);
  }
  // else: ignore
}
}  // end anonymous namespace

int main() {
  std::ios::sync_with_stdio(false);
  std::string line;

  // Handshake: consume "config|..." lines until "config|ready".
  // We don't need any of the announced configuration values.
  while (std::getline(std::cin, line).good()) {
    if (line == "config|ready") {
      break;
    }
  }

  std::print(
      "register|report|smtp-in|tx-mail\n"
      "register|report|smtp-in|tx-rcpt\n"
      "register|report|smtp-in|link-disconnect\n"
      "register|filter|smtp-in|data-line\n"
      "register|ready\n");
  std::fflush(stdout);

  while (std::getline(std::cin, line).good()) {
    ProcessProtocolLine(line);
    std::fflush(stdout);
  }

  return 0;
}
