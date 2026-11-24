from lift import *
cs=[(n,c) for n,c in allcirc() if 9<c['n']<=12]
print(len(cs))
for name,c in cs:
    print(name,c['n'],round(run(name,c),4),flush=True)
