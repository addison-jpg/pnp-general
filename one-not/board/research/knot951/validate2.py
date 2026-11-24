"""Functional validation: NOT gates really work in the encoder (general targets), and E4 (essential single NOT)."""
import sys, json
sys.path.insert(0,'/home/user/ku951')
import knot
T=knot.tables
def mn(n,tts,k,sym=True,full=False,smax=14):
    for s in range(1,smax+1):
        if knot.solve(n,[],s,k,targets=tts,sym=sym,full=full) is not None: return s
    return None
x=T(2,[]); xor2=x[0]^x[1]
y=T(3,[]); par3=y[0]^y[1]^y[2]; F=(1<<8)-1
res={}
for sym in (True,False):
  for full in (True,False):
    r=dict(xor2_k0=mn(2,[xor2],0,sym,full,6), xor2_k1=mn(2,[xor2],1,sym,full), xor2_k2=mn(2,[xor2],2,sym,full),
           nx0=mn(2,[15^x[0]],1,sym,full), nand=mn(2,[15^(x[0]&x[1])],1,sym,full),
           inv2_k1=mn(2,[15^x[0],15^x[1]],1,sym,full,6), inv2_k2=mn(2,[15^x[0],15^x[1]],2,sym,full,6),
           par3_k1=mn(3,[par3],1,sym,full,9), par3_k2=mn(3,[par3],2,sym,full,10), par3_k3=mn(3,[par3],3,sym,full,10))
    print(sym,full,r,flush=True); res[str((sym,full))]=r
vals=list(res.values()); assert all(v==vals[0] for v in vals)
e=vals[0]
assert e['xor2_k0'] is None and e['xor2_k1']==4 and e['nx0']==1 and e['nand']==2 and e['inv2_k1'] is None and e['inv2_k2']==2 and e['xor2_k2']==4
assert e["par3_k1"]==9 and e["par3_k2"]==8  # Markov: parity3 needs only 1 negation; 4(n-1)=8 with free count
json.dump(res,open('/home/user/ku951/validate2_out.json','w'),indent=1)
print('OK')
