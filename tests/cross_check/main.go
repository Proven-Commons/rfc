// Reads one hex-encoded string per line and prints how Go's time.Parse
// reads it with the time.RFC3339Nano layout: "OK", the Unix seconds and
// the nanoseconds, or "ERR". Used by tests/cross_check.py.
package main

import (
	"bufio"
	"encoding/hex"
	"fmt"
	"os"
	"time"
)

func main() {
	in := bufio.NewScanner(os.Stdin)
	in.Buffer(make([]byte, 1<<20), 1<<20)
	out := bufio.NewWriter(os.Stdout)
	defer out.Flush()
	for in.Scan() {
		b, err := hex.DecodeString(in.Text())
		if err != nil {
			fmt.Fprintln(out, "BADHEX")
			continue
		}
		t, err := time.Parse(time.RFC3339Nano, string(b))
		if err != nil {
			fmt.Fprintln(out, "ERR")
			continue
		}
		fmt.Fprintf(out, "OK\t%d\t%d\n", t.Unix(), t.Nanosecond())
	}
}
