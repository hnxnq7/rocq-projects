t = int(input())

for i in range(t):
    n = int(input())
    nums = [int(x) for x in input().split()]
    if sum(nums) == 0:
        print('YES')
    else:
        print('NO')