import turtle
window = turtle.Screen()
window.bgcolor("CornflowerBlue")

snowflake = turtle.Turtle()
snowflake.shape("circle")
snowflake.color("white")

snowflake.stamp()

for i in range(10):
    snowflake.forward(180)
    
    snowflake.forward(-60)
    snowflake.left(24)
    snowflake.forward(60)
    snowflake.right(48)
    snowflake.forward(60)
    snowflake.right(132)
    snowflake.forward(60)
    snowflake.right(48)
    snowflake.forward(60)
    snowflake.right(156)

    snowflake.forward(-60)
    snowflake.left(108)
    snowflake.forward(20)
    snowflake.forward(-20)
    snowflake.right(216)
    snowflake.forward(20)
    snowflake.forward(-20)
    snowflake.left(108)
    
    snowflake.forward(-60)
    
    snowflake.right(36)

window.exitonclick()