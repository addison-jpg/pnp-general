# Plugins, in the right order

Order for anything that needs a secret (a model key, a token, a password):

1. **Enable Env Protector: Secret Scanner** from its install card. Only the user can enable a plugin; the assistant cannot.
2. **Confirm it is active** (ListPlugins). Do not continue until it shows as enabled.
3. **Add the secret through the secure form** (request_credential). The key goes into the form only. It never goes into chat, a file, a commit or a command line.
4. **Before any commit**, scan the staged files (the Env Protector scan). A secret found there stops the commit.
5. **Use the key** only for the call it was added for. Nothing is written to the repo.

If the secure form is cancelled or aborted, stop and ask the user. Do not retry in a loop, and do not look for the key anywhere else.
