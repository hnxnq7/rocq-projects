cases = int(input())

for i in range(cases):
    field = [int(x) for x in input().split()]
    for i in [int(x) for x in input().split()]:
        field.append(i)

    grasscount = 0
    for i in field:
        if i == 1:
            grasscount += 1

    count = 0
    if grasscount == 0:
        print(0)
    elif grasscount == 4:
        print(2)
    else:
        print(1)
