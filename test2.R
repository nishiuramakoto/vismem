library(ggplot2)
library(grid)


test3 <- function() {
    x <- 1:10
    y <- x^3
    qplot(x, y)

    ##downViewport('panel-3-4')
    pushViewport(dataViewport(x,y))
    for (i in 1:10) {
        tmp    <- grid.locator('in')
        tmp.n  <- as.numeric(tmp)
        tmp2.x <- as.numeric(convertX( unit(x,'native'), 'in' ))
        tmp2.y <- as.numeric(convertY( unit(y,'native'), 'in' ))

        w <- which.min( (tmp2.x-tmp.n[1])^2 + (tmp2.y-tmp.n[2])^2 )
        ## grid.text(w, tmp$x, tmp$y )
        cat("tmp:\n")
        print(tmp)
        cat("tmp2.x:\n")
        print(tmp2.x)
        cat("tmp2.y:\n")
        print(tmp2.y)
    }
}
