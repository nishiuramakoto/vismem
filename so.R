p1 <- ggplot(mtcars, aes(factor(cyl))) + geom_bar()
p2 <- ggplot(mtcars, aes(wt, mpg)) + geom_point()
p3 <- p2 + geom_line()

pushViewport(viewport(layout = grid.layout(2, 2)))
print(p1 + opts(title = "bar"),
  vp = viewport(layout.pos.row = 1, layout.pos.col = 1))
print(p2 + opts(title = "point"),
  vp = viewport(layout.pos.row = 1, layout.pos.col = 2))
print(p3 + opts(title = "point and line"),
  vp = viewport(layout.pos.row = 2, layout.pos.col = 1:2))
