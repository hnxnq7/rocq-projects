numCows = int(input())
prefTemp = [int(x) for x in input().split()]
curTemp = [int(x) for x in input().split()]
diff = [(prefTemp[x] - curTemp[x]) for x in range(numCows)]

rel_diff = [abs(diff[0])]
for i in range(1, numCows):
    if (diff[i] > 0 and diff[i-1] < 0) or (diff[i] < 0 and diff[i-1] > 0):
        rel_diff.append(abs(diff[i]))
    elif diff[i] <= 0 and diff[i-1] <= 0:
        rel_diff.append(abs(diff[i]) - abs(diff[i-1]))
    else:
        rel_diff.append(diff[i] - diff[i-1])

total = 0
for i in rel_diff:
    if i > 0:
        total += i

print(total)