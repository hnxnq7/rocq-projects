import sys

sys.stdin = open("hoofball.in", "r")
sys.stdout = open("hoofball.out", "w")

numCows = int(input())
distances = []
rel_dist = []
direction = []
num_ball = 0

for i in input().split():
   distances.append(int(i))
distances = sorted(distances)

for i in range(1, numCows):
    rel_dist.append(distances[i] - distances[i-1])

direction = ['right']
for i in range(1, numCows-1):
    if rel_dist[i] < rel_dist[i-1]:
        direction.append('right')
    else:
        direction.append('left')
direction.append('left')

for i in range(numCows):
    if direction[i] == 'right':
        if direction[i+1] == 'left':
            num_ball += 1
            if i!= 0 and i+2 < len(direction) and direction[i-1] == 'right' and direction[i+2] == 'left':
                num_ball += 1

print(num_ball)