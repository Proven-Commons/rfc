// RFC 9557 in Node's Temporal, for tests/cross_check.py. Run with
// `node --harmony-temporal`. Reads one hex-encoded UTF-8 string per line
// and prints OK when Temporal.Instant.from reads it, or ERR.
const readline = require("readline");
const out = [];
readline.createInterface({ input: process.stdin }).on("line", (line) => {
  const s = Buffer.from(line, "hex").toString("utf8");
  try {
    Temporal.Instant.from(s);
    out.push("OK");
  } catch (e) {
    out.push("ERR");
  }
}).on("close", () => process.stdout.write(out.map((l) => l + "\n").join("")));
