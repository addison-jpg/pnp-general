# windows: raw commands on the bus

The method. Each raw Windows command is one `record` line in `methods.ath`. The record names the exact PowerShell text. It goes into bus memory (`findings.jsonl`) with a direction: OUT runs a program and writes to memory; IN reads memory back up. This follows `workshop/bus/README.md`.

Every record is labelled open. One literal claim (`claim 2 = 2`) supports them, because asteroid refuses a record without a claim. That claim says nothing about Windows.

None of these commands was run here. This machine is Linux. The Windows path is untested.

Run: `bin/asteroid --no-lean workshop/windows/methods.ath`
