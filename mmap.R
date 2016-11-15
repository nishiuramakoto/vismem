library(ggplot2)
library(cluster)

## Optional
library(shiny)

# options("download.file.method" )

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

mmap.read <- function(description) {
    con    <- file(description, "r")
    data   <- read.table(con, header = TRUE, allowEscape = TRUE, stringsAsFactors = FALSE)
    close(con)
    return(data)
}



# R treats this as a double(52bit mantissa+exp)
# Assume page_shift == 12
mmap.sprint.page <- function(page) {

    page1 <- page
    page1[is.na(page)] <- 0

    high <- floor(page1 / 2^20)                # upper 32bit part (32-12==20)
    low  <- floor(page1 - high * 2^20)         # lower 32bit part - last 3 zeros

    ret <- sprintf("%08x%05x000", high, low)

    return(ret)
}


ncluster <- function(M) {
    c   <- clusGap(M, kmeans, 8, B = 100) # Doc says 500 is good
    ret <- maxSE( c$Tab[,3] , c$Tab[,4], SE.factor=1)
    return(ret)
}


mmap.cluster <- function(mmap) {

    ps <- matrix(unique(sort(mmap$from)), ncol=1)
    nc <- ncluster(ps)
    fit  <- kmeans(ps, nc)

    # Modify the cluster numbers to reflect the base address

    # Representative values for each cluster
    representatives <- ps[match(1:nc, fit$cluster)]
    cluster.perm    <- match(1:nc, order(-representatives))
    cluster.sorted  <- cluster.perm[fit$cluster]
    from.cluster    <- cluster.sorted[match(mmap$from, ps)]

#    tmp <- from.cluster[order(mmap$from)]
#    stopifnot(all(diff(tmp) >= 0))

    mmap.clus <- data.frame(
        t        = mmap$t,
        from     = mmap$from,
        to       = mmap$to,
        v        = mmap$v,
        trace_id = mmap$trace_id,
        cluster  = from.cluster
        )

#    stopifnot(all(is.finite(mmap.clus$from)))
#    stopifnot(all(is.finite(mmap.clus$cluster)))
#    stopifnot(all(diff(mmap.clus$cluster[order(mmap.clus$from)] ) >= 0))

    return (mmap.clus)
}


mmap.cluster.size <- function(mmap.cluster) {
    nc <- max(mmap.cluster$cluster)
    ret <- 1:nc

    ## @tbd: How to vectorize this?
    for(i in 1:nc) {
        ms <- mmap.cluster[ mmap.cluster$cluster == i ,]
        a <- min(ms$from)
        b <- max(ms$to)
        ret[i] <- b - a
    }
    return(ret)
}


mmap.loop <- function(graph) {
    ## Doesn't work for ggplot
    ## pos <- identify(graph)
    ## cat(pos,"\n")
}

myplot.cluster <- function(frame, labeller = "label_value") {
    g    <- myplot(frame)
    ret  <- g + facet_grid(cluster ~ . , scales="free_y", labeller = labeller)
    ret
    mmap.loop(ret)
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


test2 <- function() {
    cat("test")
    return(0)
}

mmap.plot <- function(file) {
    mmap      <- mmap.read(file)
    mmap.clus <- mmap.cluster(mmap)
    sizes     <- mmap.cluster.size(mmap.clus)
    labeller  <- function(variable,value) sprintf("%dM", ceiling(sizes[value]/256))
    g         <- myplot.cluster(mmap.clus, labeller = labeller)
    return(list(plot=g, mmap = mmap.clus))
}

find.trace_id <- function(mmap, t, p) {
    matched <- mmap[ mmap$t == as.integer(t) & mmap$from <= p & p < mmap$to , ]
    return(matched$trace_id[1])
}

find.trace <- function(g, t, p) {
    trace.id <- find.trace_id(g$mmap,t,p)
    ts       <- g$trace$trace[ g$trace$trace_id == trace.id ]
    return(ts[1])
}


mmap.init <- function(matrix.file, trace.file) {
    g       <- mmap.plot(matrix.file)
    g$trace <- mmap.read(trace.file)
    return(g)
}

test <- function() {
    g <- mmap.init("out.data","trace.data")
    print(g$plot)
    return(g)
}



### Shiny server

ui <- basicPage(
  plotOutput("plot1", click = "plot_click"),
  verbatimTextOutput("info")
)

server <- function(input, output) {
    g <- mmap.init("out.data", "trace.data")

    output$plot1 <- renderPlot({
        return(g$plot)
    })

    output$info <- renderText({
        t    <- input$plot_click$x
        page <- input$plot_click$y
        p    <- mmap.sprint.page(page)
        trace <- find.trace(g,t,page)
        cat("t=",t , "\np=", p, "\ntrace:\n", trace,"\n")
        paste0("t=",t , "\np=", p, "\ntrace:", trace)
    })
}


shiny <- function () {
    shinyApp(ui, server)
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
