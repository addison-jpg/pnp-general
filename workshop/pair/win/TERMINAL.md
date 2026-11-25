# The terminal, formally (proposed, 2026-11-25)

A terminal is a prompt and a finite map from commands to programs.

- **Commands:** a finite set C = {hello, big, bus, quit}.
- **Programs:** a map P from each command to one `.ath` file: hello -> hello.ath, big -> big.ath, bus -> workshop/bus/bus.ath.
- **Engine:** one program E that runs a `.ath` file and returns its exit code. On Linux E is the asteroid binary; on Windows E is asteroid.exe, or ast.exe for the native subset.
- **Behaviour:** on a line l in C, the terminal runs E on P(l) and prints the exit code. On `quit` it stops. Any other line prints the list of commands.

Checked by construction: the map is total on C (every command has exactly one program), and the terminal does nothing else. The terminal holds no logic of its own. All checks live in the `.ath` files.

Not claimed: that the Windows engine runs big.ath (asteroid.exe is not built yet), or that a Windows terminal has been run on Windows.
