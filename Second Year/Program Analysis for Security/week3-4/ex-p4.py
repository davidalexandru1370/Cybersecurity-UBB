from z3 import *

# declare variables
X = Bool('X')
Y = Bool('Y')
Z = Bool('Z')

# define formula
F = And( Implies(X, Implies(Y, Z)), X)

print(F)

solve(F) # find a model for F

# find a counterexample for F
solve(Not(F))
