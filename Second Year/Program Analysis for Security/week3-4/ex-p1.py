from z3 import *

x = Bool('x')
y = Bool('y')
z = Bool('z')


F = Implies(x, y)
F = And(F, Implies(z,z))

print(F)

solve(F)

solve(Not(F))

