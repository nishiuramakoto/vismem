library(ggplot2)
library(cluster)
library(shiny)

# Generic file data frame reader
mmap.read <- function(description, nrows=-1) {
    con    <- file(description, "r")
    data   <- read.table(con,
                         header = TRUE,
                         allowEscape = TRUE,
                         stringsAsFactors = FALSE,
                         nrows=nrows)
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


# Estimate the number of clusters.
ncluster <- function(M, n=8, B=100) {
    k <- dim(M)[1]
    if (k <= n) {
        return(k-1)
    } else {
        c   <- clusGap(M, kmeans, 8, B = B) # Doc says 500 is good
        ret <- maxSE( c$Tab[,3] , c$Tab[,4], SE.factor=1)
        return(ret)
    }
}

iv.intersects <- function(i,j) {
    return (i[1] <= j[1] && j[1] <= i[2]) || (j[1] <= i[1] && i[1] <= j[2])
}

iv.union <- function(i,j) {
    return (c(min(i[1],j[1]), max(i[2],j[2])))
}

# @tbd is there a faster way?
disjoint.intervals <- function(mmap) {
    ivs <- unique(cbind(mmap$from, mmap$to)[order(mmap$from),])

    disivs <- ivs

    j <- 1
    for (i in 1:dim(ivs)[1]) {
        crow <- disivs[j,]
        row  <- ivs[i,]

        if (iv.intersects(crow,row)) {
            disivs[j,] <- iv.union(crow,row)
        } else {
            j <- j+1
            disivs[j,] <- row
        }

    }

    disivs <- matrix(disivs[1:j,],ncol=2)
    return(disivs)
}

# Add cluster numbers sorted according to the base address
mmap.cluster <- function(mmap, B=100) {
    ivs <- disjoint.intervals(mmap)
    ps  <- matrix(sort(as.vector(ivs[,1])), ncol=1)
    nc  <- ncluster(ps, B=B)
    fit <- kmeans(ps, nc)

    # Representative values for each cluster
    representatives <- ps[match(1:nc, fit$cluster)]
    cluster.perm    <- match(1:nc, order(-representatives))
    cluster.sorted  <- cluster.perm[fit$cluster]

    #from.cluster    <- cluster.sorted[match(mmap$from, ps)]
    from.cluster    <- cluster.sorted[findInterval(mmap$from,ps)]

    mmap.clus <- data.frame(
        t        = mmap$t,
        from     = mmap$from,
        to       = mmap$to,
        v        = mmap$v,
        trace_id = mmap$trace_id,
        cluster  = from.cluster
        )

    return (mmap.clus)
}


# Compute the sizes of the clusters (i.e. max(cluster)-min(cluster)
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


# Plot with cluster info
myplot.cluster <- function(frame, labeller = "label_value") {
    g    <- myplot(frame)
    ret  <- g + facet_grid(cluster ~ . , scales="free_y", labeller = labeller)
    ret
    return(ret)
}

# Plot without cluster info
myplot <- function(frame) {
    g <- ggplot(frame, aes(x=t, y=from, xmin= t-0.5, xmax = t+0.5, ymin = from, ymax = to, fill=v)) +
        geom_rect()

    ret <- g +
        scale_x_continuous() +
            scale_y_continuous(labels = mmap.sprint.page) +
                scale_fill_gradientn(colours = rainbow(7))
    return(ret)
}

label.cluster <- function(pid, sizes) {
    # Please don't mix non referential transparency and laziness!
    force(pid)
    force(sizes)
    l <- function(variable,value) sprintf("%dM", ceiling(sizes[value]/256))
    return(l)
}

# ggplot object without trace info
mmap.plot <- function(file, B=100) {
    ret   <- list()
    mmap  <- mmap.read(file)
    pids  <- unique(mmap$pid)

    i <- 1
    for (pid in pids) {
        curmap    <- mmap[mmap$pid == pid,]
        clus      <- mmap.cluster(curmap, B=B)
        sizes     <- mmap.cluster.size(clus)

        print(sprintf("cluster_sizes(pid=%d):",pid))
        cat(sizes/265)

        labeller  <- label.cluster(pid,sizes)
        g         <- myplot.cluster(clus, labeller = labeller)

        ret[[i]] <- list(pid=pid, plot=g, mmap = clus)
        i <- i+1
    }
    return(ret)
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

# ggplot object with trace info
mmap.plot.trace <- function(matrix.file, trace.file, B=100) {
    gs    <- mmap.plot(matrix.file, B=B)
    trace <- mmap.read(trace.file)

    for (i in 1:length(gs)) {
        gs[[i]]$trace <- trace
        gs[[i]]$plot.panel  <- sprintf("pid_%s", gs[[i]]$pid)
        gs[[i]]$trace.panel <- sprintf("trace_%s", gs[[i]]$pid)
    }
    return(gs)
}

test <- function () {
    datafile  = "build/data-2016-12-08_09h55m38s/frame.data"
    tracefile = "build/data-2016-12-08_09h55m38s/trace.data"
    gs <- mmap.plot(datafile)
    print(gs[[1]]$plot)
}


### A shiny server

ui.basic <- basicPage(
  plotOutput("plot1", click = "plot_click"),
  verbatimTextOutput("info")
)

shiny.make.tab <- function(g) {
    tabPanel(g$plot.panel,
             plotOutput(g$plot.panel, click = "plot_click"),
             verbatimTextOutput(g$trace.panel)
             )
}


shiny.ui.tabs <- function(gs) {

    tabs <- lapply(gs, shiny.make.tab)
    tabs$type="tabs"

    tabs.panel <- do.call(tabsetPanel, tabs)

    fluidPage(
        titlePanel("Memamps"),
        mainPanel( tabs.panel, width = 12)
        )
}

shiny.render.plot <- function(g) {
    ## Please please don't mix impurity and laziness in your language..
    force(g)
    print(g$pid)
    renderPlot({
        g$plot
    })
}

shiny.render.text <- function(g,input) {
    force(g)
    force(input)

    renderText({

        t     <- input$plot_click$x
        page  <- input$plot_click$y
        p     <- mmap.sprint.page(page)
        trace <- find.trace(g,t,page)

        ## Print to stdout. Useful for scripting or in multi-monitor setup
        cat("pid=",g$pid, "\nt=",t , "\np=", p, "\ntrace:\n", trace,"\n")

        ## Paste into the html
        paste0("t=",t , "\np=", p, "\ntrace:", trace)
    })
}

shiny.server <- function(gs) {
    force(gs)
    function(input, output) {
        force(gs)

        for (i in 1:length(gs)) {
            force(i)
            g    <- gs[[i]]
            plot <- gs[[i]]$plot

            force(g)
            force(plot)

            output[[gs[[i]]$plot.panel]]  <- shiny.render.plot(g)
            output[[gs[[i]]$trace.panel]] <- shiny.render.text(g,input)
        }
    }
}


shiny <- function (matrix.file, trace.file) {
    gs <- mmap.plot.trace(matrix.file, trace.file)
    shinyApp(shiny.ui.tabs(gs), shiny.server(gs))
}



## main

# Usage: command data_file_1 .. data_file_n trace_file_1 .. trace_file_n
# @tbd: Add options for Monte Carlo simulations, etc.
args = commandArgs(trailingOnly=TRUE)
stopifnot(length(args) %% 2 == 0)

n = length(args) %/% 2
data.files  = args[1:n]
trace.files = args[(n+1):length(args)]

cat("data.files=",data.files,"\n")
cat("trace.files=",trace.files,"\n")

options(shiny.port=5000)
shiny(data.files[1],trace.files[1])
