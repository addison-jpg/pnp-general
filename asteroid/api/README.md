# asteroid API

Read-only JSON over the repository's verified state, a guarded `/check`, and the Discord endpoint, in one standard-library server.

Run: `REPO_DIR=<checkout> PORT=8080 python3 -I asteroid/api/api.py`

| route | what |
|---|---|
| `GET /health` | liveness |
| `GET /capabilities` | what asteroid is, its local operations, and explicit limits |
| `GET /status` | verified count, by label and by program |
| `GET /results?program=P` | verified findings (id, program, label, text, rerun command) |
| `GET /frames?status=OPEN` | frames by score, highest first |
| `GET /programs` | the top-level `.ath` programs `/check` accepts |
| `POST /check {"program": "gravity.ath"}` | run one allowlisted program with `--no-lean`; one at a time (429 otherwise) |
| `POST /interactions` | Discord slash commands (`DISCORD_PUBLIC_KEY`; see `../discord`) |

Set `API_KEY` to require the header `X-API-Key` on `/check`. The API writes nothing to the repository, except that an allowlisted program may record findings the way it always does when run.

asteroid is repository-local software, not an agent with preferences. The API does not control brains,
satellites, vehicles, external services, or physical systems, and it makes no physical or consciousness
claims. `/capabilities` exposes those operational limits as JSON.

Tests: `python3 -I asteroid/api/test_api.py`.
