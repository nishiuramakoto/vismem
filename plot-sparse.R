# sudo apt-get install

library(reshape2)
library(ggplot2)

set.seed(7)
m <- matrix(0, 100, 100)
n <- 1000
m[sample(length(m), size = n)] <- rep(-1:1, length=n)
m

ggplot(melt(m), aes(Var1,Var2, fill=value)) +
    geom_raster() +
        scale_fill_gradient2(low='red', high='black', mid='white') + theme_bw() + xlab("x1") + ylab("x2")
