import sys

sys.stdin = open("factory.in", "r")
sys.stdout = open("factory.out", "w")

n = int(input())
ends = {}
alls = []

for r in range(n-1):
    start, end = [int(x) for x in input().split()]
    
    if start not in alls:
        alls.append(start)
    
    if end in ends.keys():
        ends[end].append(start)
    else:
        ends[end] = [start]

print(alls)
print(ends)


minimum = -1
for end in ends.keys():
    if end in alls:
        alls.pop(alls.index(end))
    if sorted(ends[end]) == sorted(alls):
        minimum = end
    alls.append(end)

print(minimum)