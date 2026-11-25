"""Register asteroid's slash commands with Discord, once.
Reads the bot token from the environment, never from a file:
    DISCORD_BOT_TOKEN=<token> python3 -I asteroid/discord/register.py <APPLICATION_ID>
Safe to rerun: it replaces the application's global commands with exactly these two."""
import json, os, sys, urllib.request

COMMANDS = [
    {"name": "status", "description": "How many results asteroid has verified", "type": 1},
    {"name": "check", "description": "Run one asteroid program and report TRUE/FALSE", "type": 1,
     "options": [{"name": "program", "description": "a top-level .ath program, e.g. gravity.ath", "type": 3, "required": True}]},
]

def main(argv, env=os.environ):
    if len(argv) != 2 or not argv[1].isdigit():
        sys.exit("usage: DISCORD_BOT_TOKEN=... register.py <APPLICATION_ID>")
    token = env.get("DISCORD_BOT_TOKEN")
    if not token: sys.exit("set DISCORD_BOT_TOKEN in the environment")
    req = urllib.request.Request(f"https://discord.com/api/v10/applications/{argv[1]}/commands", data=json.dumps(COMMANDS).encode(),
                                 method="PUT", headers={"Authorization": f"Bot {token}", "Content-Type": "application/json", "User-Agent": "asteroid-register"})
    out = json.loads(urllib.request.urlopen(req, timeout=20).read())
    print("registered:", ", ".join("/" + c["name"] for c in out))

if __name__ == "__main__":
    main(sys.argv)
