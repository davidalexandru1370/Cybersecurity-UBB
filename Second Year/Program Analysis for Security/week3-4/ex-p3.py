from z3 import *
x, y = Bools('x y')

s = Solver()

s.add( Implies(x, y) )
s.add( Implies(y, x) )

print( s.check() )
print( s.model() )

s.add( x )

print( s.check() )
print( s.model() )

s.add( Not(y) )

print( s.check() )
