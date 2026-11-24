import sys,re
src=open('/home/claude/scripts/inj951.py').read().split('def make_instance')[0]
exec(src)
# vars: c=0,c'=1,x1..x6=2..7 ; n=8
c,cp=0,1; x=lambda i:1+i
n=8
sets=[[c,x(1),x(2)],[c,x(3),x(4)],[cp,x(1),x(5)],[cp,x(3),x(6)],[x(1),x(3)]]
G=[]
def add(op,a,b): G.append((op,a,b)); return n+len(G)-1
h=add('or',x(1),x(3)); g=add('or',h,c); gp=add('or',h,cp)
add('or',x(1),x(2)); add('or',x(3),x(4)); add('or',x(1),x(5)); add('or',x(3),x(6))
p=len(G); add('not',h,h)
print(analyse(n,sets,G,p))
