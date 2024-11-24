from math import sqrt

n: int = 8007
t0: int = int(sqrt(n))

for index in range(1, 21):
    t: int = t0 + index
    result: int = t * t - n
    t_sqrt: int = int(sqrt(result))
    is_perfect_square: bool = (t_sqrt * t_sqrt) == result
    print(f"Iteration {index}: t = {t}; t * t - n <=> {t * t} - {n} = {result} is perfect square {is_perfect_square}")
    if is_perfect_square == True:
        s = t_sqrt
        res = (t-s)*(t+s)
        print(f"(t - s)(t + s) <=> ({t - s})({t + s}) = {res}")
        print(f"s={s} t={t}")
        break
else:
    print('not enough iterations')

