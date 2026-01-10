# a = input().split()
# for i in range(len(a)):
#     a[i] = int(a[i])

a = [int(x) for x in a]
a = [1, 2, 3, 4, 5, 6, 2, 333, 2]

largest = 0
frequency = {}
for e in a:
    if e in frequency:
        frequency[e] += 1
    else:
        frequency[e] = 1
    if frequency[e] > largest:
        largest = frequency[e]

print(frequency)

print(largest)
    