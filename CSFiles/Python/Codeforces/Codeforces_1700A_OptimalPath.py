numTest = int(input())

for t in range(numTest):
    n, m = [int(x) for x in input().split()]
    cost = 0
    cost += m*(m+1)//2
    for i in range(2, n+1):
        cost += i*m
    print(cost)
