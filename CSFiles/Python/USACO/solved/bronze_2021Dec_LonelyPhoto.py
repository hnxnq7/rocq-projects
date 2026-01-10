numCows = int(input())
cows = input()

consList = []
cons = 0
prevCow = cows[0]

for i in range(numCows):
    if cows[i] == prevCow:
        cons += 1
    else:
        consList.append(cons)
        cons = 1
    prevCow = cows[i]

consList.append(cons)

count = 0
for i in range(1, len(consList)):
    if i >= 2 and consList[i-1] == 1:
        count += consList[i-2]*consList[i]
    count += consList[i-1] + consList[i] - 2

print(count)