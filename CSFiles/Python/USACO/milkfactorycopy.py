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
    if end not in alls:
        alls.append(end)
    
    if end in ends.keys():
        ends[end].append(start)
    else:
        ends[end] = [start]
    
    for e in ends[end]:
        if e in ends.keys():
            for n in ends[e]:
                if n not in ends[end]:
                    ends[end].append(n)

s = []
for end in ends.keys():
    ends[end].append(end)
    if sorted(ends[end]) == sorted(alls):
        s.append(end)


if s == []:
    print(-1)
else:
    print(list(sorted(s))[0])