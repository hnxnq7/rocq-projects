import turtle
window = turtle.Screen()

mio = turtle.Turtle()
mio.shape("circle")

for i in range(100):
    mio.stamp()
    mio.forward(i*2+5)
    mio.right(24)

window.exitonclick()