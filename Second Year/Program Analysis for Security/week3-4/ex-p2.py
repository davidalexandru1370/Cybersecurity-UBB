from z3 import *

x = Bool('x')
y = Bool('y')

F = Not(And(x, y)) == Or(Not(x), Not(y))

print(F)

solve(F)

solve(Not(F))

