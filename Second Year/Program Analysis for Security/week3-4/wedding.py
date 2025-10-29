from z3 import *
xal, xam, xar, xbl, xbm, xbr, xcl, xcm, xcr = Bools('xal xam xar xbl xbm xbr xcl xcm xcr')
s = Solver()

# Alice does not sit next to Charlie
s.add( And( Implies( Or(xal, xar), Not(xcm) ), Implies( xam, And( Not(xcl), Not(xcr)))))

# Alice does not sit on the leftmost chair
s.add( Not(xal) )

# Bob does not sit to the right of Charlie

s.add(And(
    Implies(xcl, Not(xbm)),
    Implies(xcm, Not(xbr))
))
# Each person gets a chair
s.add(Or(xal, xam, xar))
s.add(Or(xbl, xbm, xbr))
s.add(Or(xcl, xcm, xcr))
# Every person gets at most one chair
s.add(AtMost(xal, xam, xar, 1))
s.add(AtMost(xbl, xbm, xbr, 1))
s.add(AtMost(xcl, xcm, xcr, 1))
# Every chair gets at most one person
s.add(AtMost(xal, xbl, xcl, 1))  # left chair
s.add(AtMost(xam, xbm, xcm, 1))  # middle chair
s.add(AtMost(xar, xbr, xcr, 1))  # right chair




result = s.check()
print( result )

if result == sat:
    m = s.model()
    print("Valid seating arrangement:")
    for v in [xal, xam, xar, xbl, xbm, xbr, xcl, xcm, xcr]:
        print(f"{v} = {m[v]}")

