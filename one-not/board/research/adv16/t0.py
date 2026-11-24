from enc import *
for n,sets,ng,exp in [(3,[[0,1],[1,2]],6,True),(3,[[0,1],[1,2]],5,False),(5,[[0,1,2],[0,3,4],[1,3],[2,4]],10,True),(5,[[0,1,2],[0,3,4],[1,3],[2,4]],9,None)]:
    E=Enc(n,sets,ng); ok,res,t=E.solve(); print(n,sets,ng,ok,exp,round(t,2), res and verify(res), res and res['gates'])
