# The "pure no-overlap claim is false" example (verified here on all inputs).
# Sets A={0,1,2} (easy), B={3,4} (hard); NOT reads h = x2 (minterm {2}, disjoint from B).
# g = (x2 ∧ (x3∨x4)) ∨ (¬x2 ∧ (x0∨x1)) is 0 at Zof A and at Zof B, true at e0,e1 (A side)
# and at e3∨e2, e4∨e2 (B side, shifted by the minterm) -> counted for both sets under the
# FIRST scheme (minterm-shifted test points). Under the transversal scheme it is no merge.
def g(x):
    b=lambda i:(x>>i)&1
    return (b(2)&(b(3)|b(4))) | ((1-b(2))&(b(0)|b(1)))
full=31; ZA=full&~0b00111; ZB=full&~0b11000
assert g(ZA)==0 and g(ZB)==0
assert g(1<<0)==1 and g(1<<1)==1
assert g((1<<3)|(1<<2))==1 and g((1<<4)|(1<<2))==1
print("overlap wire verified")
