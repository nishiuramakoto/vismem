
read.matrix <- function(description) {
    con <- file(description, "r")

    dim <- scan(con, what = integer(), n = 2, comment.char = "#")
    nrow  <- dim[1]
    ncol  <- dim[2]

    row.names <- scan(con, what = integer(), n = nrow, comment.char = "#")
    col.names <- scan(con, what = integer(), n = ncol, comment.char = "#")

    M <- matrix(scan(con, what = integer(), n = nrow * ncol, comment.char = "#"),
                nrow = nrow, ncol = ncol, byrow = TRUE)

    close(con)

    ret <- list("rows" = row.names,
                "cols" = col.names,
                "matrix" = M
                )
    return(ret)
}

library(ggplot2)
library(cluster)

# R treats this as a double(52bit mantissa+exp)
mmap.sprint.page <- function(page) {

    page1 <- page
    page1[is.na(page)] <- 0

    # addr = page * 2^12
    high <- floor(page1 / 2^20)                # upper 32bit part
    low  <- floor(page1 - high * 2^20)         # lower 32bit part - last 3 zeros

    ret <- sprintf("%08x%05x000", high, low)

    return(ret)
}


ncluster <- function(M) {
    c  <- clusGap(M, kmeans, 8, B = 100) # Doc says 500 is good
    ret <- maxSE( c$Tab[,3] , c$Tab[,4], SE.factor=1)
    return(ret)
}


mmap.read <- function(description) {
    con <- file(description, "r")

    data    <- read.table(con, header = TRUE, allowEscape = TRUE)

    close(con)

    return(data)
}

mmap.cluster <- function(mmap) {

    ps <- matrix(unique(sort(mmap$from)), ncol=1)
    nc <- ncluster(ps)
    fit  <- kmeans(ps, nc)

    # Representative values for each cluster
    representatives <- ps[match(1:nc, fit$cluster)]
    cluster.perm    <- match(1:nc, order(-representatives))
    cluster.sorted  <- cluster.perm[fit$cluster]
    from.cluster    <- cluster.sorted[match(mmap$from, ps)]

    cat(mmap.sprint.page(representatives),"\n")
    cat(representatives,"\n")
    cat(fit$cluster,"\n")
    cat(cluster.sorted,"\n")
    cat(cluster.perm,"\n")
#    tmp <- from.cluster[order(mmap$from)]
#    stopifnot(all(diff(tmp) >= 0))

    mmap.clus <- data.frame(
        t    = mmap$t,
        from = mmap$from,
        to   = mmap$to,
        v    = mmap$v,
        cluster = from.cluster
        )

#    stopifnot(all(is.finite(mmap.clus$from)))
#    stopifnot(all(is.finite(mmap.clus$cluster)))
#    stopifnot(all(diff(mmap.clus$cluster[order(mmap.clus$from)] ) >= 0))

    return (mmap.clus)
}

test2 <- function() {
    cat("test")
    return(0)
}

test <- function() {
    mmap      <- mmap.read("out.data")
    mmap.clus <- mmap.cluster(mmap)
    sizes     <- mmap.cluster.size(mmap.clus)
    labeller  <- function(variable,value) sprintf("%dM", floor(sizes[value]/256))
    myplot.cluster(mmap.clus, labeller = labeller)
}

mmap.cluster.size <- function(mmap.cluster) {
    nc <- max(mmap.cluster$cluster)
    ret <- 1:nc
    for(i in 1:nc) {
        ms <- mmap.cluster[ mmap.cluster$cluster == i ,]
        a <- min(ms$from)
        b <- max(ms$to)
        ret[i] <- b - a
    }
    return(ret)
}

myplot.cluster <- function(frame, labeller = "label_value") {
    g <- myplot(frame)
    size <- mmap.cluster.size(frame)
    ret <- g + facet_grid(cluster ~ . , scales="free_y", labeller = labeller)
    return(ret)
}

myplot <- function(frame) {
    g <- ggplot(frame, aes(x=t, y=from, xmin= t-0.5, xmax = t+0.5, ymin = from, ymax = to, fill=v)) +
        geom_rect()

    ret <- g +
        scale_x_discrete() +
            scale_y_continuous(labels = mmap.sprint.page) +
                scale_fill_gradientn(colours = rainbow(7))
    return(ret)
}

scale.mmap <- function(mmap) {
    ret <- data.frame (
        t <- mmap$t,
        from <- log2(mmap$from),
        to   <- log2(mmap$to) + 1,
        v    <- mmap$v
    )
    return (ret)
}

#mmap <- read.mmap("out.data")

len    <- 1000
region <- 100
mmap.test <- data.frame(
    t    <- rep(1:len, each=region),
    from <- rep(seq(from=0, by = 100, length.out= region), len),
    to   <- rep(seq(from=0, by = 100, length.out= region), len) + 80,
    v    <- runif(len*region)
    )
