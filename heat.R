mydata <- mtcars[, c(1,3,4,5,6,7)]
cormat <- round(cor(mydata),2)

library(reshape2)
melted.cormat <- melt(cormat)

library(ggplot2)
ggplot(data = melted.cormat, aes(x=Var1, y=Var2, fill=value)) +
    geom_tile()

##ggplot(faithful, aes(x=waiting, y=eruptions)) + geom_raster(aes(fill = density))
ggplot(faithful, aes(x=waiting, y=eruptions)) + geom_raster(aes())



# If you want to draw arbitrary rectangles, use geom_tile() or geom_rect()
df <- data.frame(
  x = rep(c(2, 5, 7, 9, 12), 2),
  y = rep(c(1, 2), each = 5),
  z = factor(rep(1:5, each = 2)),
  w = rep(diff(c(0, 4, 6, 8, 10, 14)), 2)
)
ggplot(df, aes(x, y)) +
  geom_tile(aes(fill = z))
