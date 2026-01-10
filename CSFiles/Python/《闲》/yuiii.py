import turtle
window = turtle.Screen()

yui = turtle.Turtle()
yui.shape("turtle")
yui.up()

for i in range(100):
    yui.stamp()
    yui.forward(i*2+5)
    yui.right(24)

window.exitonclick()