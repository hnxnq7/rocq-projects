print("Enter the number of boxes:")
n = int(input())

print("Enter pennies in each box:", end = "\n")
a = input().split()
for i in range(n):
    a[i] = int(a[i])

player1Score = 0
player2Score = 0

l = 0
r = n-1

player1Steps = []
player2Steps = []
currentPlayer = 1
move = 0

player = []

while True:
    print("\nBoxes:")
    for i in range(l, r):
        print(a[i], end = " ")
    print(a[r])
    print("Player 1 score:",player1Score)
    print("Player 2 score:",player2Score)
    print("Enter player", currentPlayer, "move (1 for leftmost,2 for rightmost,3 for undo):", end = "\n")
    move = int(input())
    if move == 1:
        if currentPlayer == 1:
            player1Score += a[l]
            player1Steps.append(1)
        elif currentPlayer == 2:
            player2Score += a[l]
            player2Steps.append(1)
        l += 1
        player.append(currentPlayer)
        currentPlayer = 3 - currentPlayer
    elif move == 2:
        if currentPlayer == 1:
            player1Score += a[r]
            player1Steps.append(2)
        elif currentPlayer == 2:
            player2Score += a[r]
            player2Steps.append(2)
        r -= 1
        player.append(currentPlayer)
        currentPlayer = 3 - currentPlayer
    elif move == 3:
        if len(player) == 0:
            print("Invalid move!")
        else:
            if player[-1] == 1:
                if len(player1Steps) == 0:
                    print("Invalid move!")
                else:
                    if player1Steps[-1] == 1:
                        l -= 1
                        player1Score -= a[l]
                    elif player1Steps[-1] == 2:
                        r += 1
                        player1Score -= a[r]
                    player.pop(-1)
                    player1Steps.pop(-1)
            elif player[-1] == 2:
                if len(player2Steps) == 0:
                    print("Invalid move!")
                else:
                    if player2Steps[-1] == 1:
                        l -= 1
                        player2Score -= a[l]
                    elif player2Steps[-1] == 2:
                        r += 1
                        player2Score -= a[r]
                    player.pop(-1)
                    player2Steps.pop(-1)
            currentPlayer = 3 - currentPlayer
    else:
        print("Invalid move!")
    if l > r:
        break


print("Player 1 score:",player1Score)
print("Player 2 score:",player2Score)
if player1Score > player2Score:
    print("Player 1 won!")
elif player2Score > player1Score:
    print("Player 2 won!")
elif player1Score == player2Score:
    print("It's a tie!")