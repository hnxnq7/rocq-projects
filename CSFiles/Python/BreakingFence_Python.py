numFence = int(input())
fences = []
for i in range(numFence):
    fences.append([int(x) for x in input().split()])
fences = sorted(fences, key = lambda x: x[1])
print(fences)

area = 0
for f in range(1, numFence):
    r = f
    l = f-1
    prevdist = 0
    dist = 1
    cannotbreak = False
    
    while True:
        if l < 0 or r >= numFence:
            break
        elif prevdist == dist:
            cannotbreak = True
            break
        
        dist = fences[r][1]-fences[l][1]
        if dist > fences[r][0]:
            r += 1
            continue
        if dist > fences[l][0]:
            l -= 1
            continue
        
        prevdist = dist
    
    if cannotbreak == True:
        area += fences[f][1]-fences[f-1][1]

print(area)