guess = []
answer = []
for i in range(3):
    s = input()
    for e in s:
        guess.append(e)
for i in range(3):
    s = input()
    for e in s:
        answer.append(e)


green = 0
yellow = 0
for i in range(9):
    l = guess[i]
    if l == answer[i]:
        green += 1
        answer[i] = 0
        guess[i] = 1

for i in range(9):
    l = guess[i]
    if l in answer:
        yellow += 1
        answer[answer.index(l)] = 0

print(green)
print(yellow)
            
