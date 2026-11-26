// mkpins writes the pins file an executable is built with.
//
//	go run ./cmd/mkpins REPO_ROOT FORK COMMIT > cmd/pnp-check/pins.json
package main

import (
	"encoding/json"
	"fmt"
	"os"

	"github.com/addison-jpg/pnp-general/tools/pnp-check/internal/pins"
)

func main() {
	if len(os.Args) != 4 {
		fmt.Fprintln(os.Stderr, "usage: mkpins REPO_ROOT FORK COMMIT")
		os.Exit(3)
	}
	p, err := pins.Make(os.Args[1], os.Args[2], os.Args[3])
	if err != nil {
		fmt.Fprintln(os.Stderr, "mkpins:", err)
		os.Exit(1)
	}
	b, _ := json.MarshalIndent(p, "", "  ")
	fmt.Println(string(b))
}
