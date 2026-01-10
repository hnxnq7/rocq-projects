numFlower = int(input())
pedals = [int(x) for x in input().split()]

numAvg = 0

for i in range(numFlower):
    for j in range(i, numFlower):
        sumPedal = 0
        for idx in range(i, j+1):
            sumPedal += pedals[idx]
        num = j-i+1
        
        if sumPedal%num == 0:
            average = sumPedal//num
        else:
            continue
        
        for idx in range(i, j+1):
            if pedals[idx] == average:
                numAvg += 1
                break

print(numAvg)