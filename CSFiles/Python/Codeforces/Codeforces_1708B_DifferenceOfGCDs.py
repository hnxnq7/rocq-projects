numCases = int(input())

for i in range(numCases):
    final_array = {}
    n, l, r = [int(x) for x in input().split()]
    count = 0
    
    for i in range(1, n+1):
        if l%i == 0:
            num = l
        else:
            num = l + (i - l%i)
        
        if num <= r:
            final_array[i] = num
            count += 1
    
    if count < n:
        print('NO')
        continue
    else:
        print('YES')
        for i in range(n):
            print(final_array[i+1], end = " ")
        print('\n', end = "")
