from math import gcd

n:int = 9353

x0 = 2

is_between_1_n = lambda x: 1 < x < n
results = {}
results[0] = x0
for x in range(1, 30):
    results[x] = (results[x - 1] * results[x - 1] + 1) % n
    print(f"x{x} = {results[x]}")
for index in range(1, 21):
    double_index = 2 * index
    iteration = abs(results[double_index] - results[index])
    iteration_gcd = gcd(n, iteration)
    print(f"gcd(x{double_index} - x{index}, {n}) = {iteration_gcd}")
    if is_between_1_n(iteration_gcd):
        print(f"Obtained factors: {iteration_gcd}, {n//iteration_gcd}")
        break
