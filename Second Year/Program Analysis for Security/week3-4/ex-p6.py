from z3 import *

s = Solver()

if s.check() == sat:
    model = s.model()
    print( model )
