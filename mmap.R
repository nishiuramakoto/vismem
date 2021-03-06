library(ggplot2)
library(cluster)
library(shiny)

is.string <- function(s) {
    is.character(s) &&  !is.na(s)  && length(s) > 0
}

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

find.next <- function(t) {
    u <- unique(sort(t))
    i <- findInterval(t,u)
    l <- length(u)
    v <- c(u,u[l] + u[l]-u[l-1])
    return(v[i+1])
}


# Estimate the number of clusters.
ncluster <- function(M, n=8, B=100) {
    k <- dim(M)[1]
    n <- min(n,k-1)

    if (n <= 1) {
        return(1)
    } else {
        c   <- clusGap(M, kmeans, n, B = B) # Doc says 500 is good
        ret <- maxSE( c$Tab[,3] , c$Tab[,4], SE.factor=1, method="globalmax")

        if (ret==1) {
            print(M)
        }

        return(ret)
    }
}

# Add cluster numbers sorted according to the base address
mmap.cluster <- function(mmap, B=100) {
    ivs <- disjoint.intervals(mmap)
    ps  <- matrix(sort(as.vector(ivs[,1])), ncol=1)
    #ps  <- matrix(sort(as.vector(ivs)), ncol=1)
    nc  <- ncluster(ps, B=B)
    fit <- kmeans(ps, nc)


    # Representative values for each cluster
    representatives <- ps[match(1:nc, fit$cluster)]
    cluster.perm    <- match(1:nc, order(-representatives))
    cluster.sorted  <- cluster.perm[fit$cluster]

    # from.cluster    <- cluster.sorted[match(mmap$from, ps)]
    from.cluster    <- cluster.sorted[findInterval(mmap$from,ps)]

    # time slice
    dt <- find.next(mmap$t) - mmap$t

    mmap.clus <- data.frame(
        t        = mmap$t,
        dt       = dt,
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

    g <- ggplot(frame, aes(x=t, y=from, xmin= t, xmax = t+dt, ymin = from, ymax = to, fill=v)) +
        geom_rect()

    ret <- g +
        scale_x_continuous() +
            scale_y_continuous(labels = mmap.sprint.page) +
                scale_fill_gradientn(colours = rainbow(7))
    return(ret)
}

label.cluster <- function(pid, sizesMB) {
    # Please don't mix non referential transparency and laziness!
    force(pid)
    force(sizesMB)
    l <- function(variable,value) sprintf("%dM", ceiling(sizesMB[value]))
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
        sizesMB   <- ceiling(mmap.cluster.size(clus) /2^(20-12))
        areaMB    <- sum(sizesMB)

        stopifnot(all(mmap$from < mmap$to))

        if (areaMB > 10000) {
            #print(curmap)
            #print(clus)
        }

        cat(sprintf("cluster_sizes_MB(pid=%d)=",pid),"\n")
        cat(sizesMB,"\n")

        labeller  <- label.cluster(pid,sizesMB)
        g         <- myplot.cluster(clus, labeller = labeller)

        ret[[i]] <- list(pid=pid, plot=g, mmap = clus, areaMB = areaMB)
        i <- i+1
    }
    return(ret)
}

find.trace.clone.process <- function(g, t, pid) {
    xs <- g$trace$trace[g$trace$child_pid == pid & g$trace$t <= t &
                            g$trace$success == 1 & g$trace$syscall == 2]
    if (length(xs)==0) {
        return(NULL)
    }
    return(tail(xs,n=1))
}

find.trace.exec <- function(g, t, pid) {
    xs <- g$trace$trace[g$trace$pid == pid & g$trace$t <= t & g$trace$success == 1 & g$trace$syscall==1]
    if (length(xs)==0) {
        return(NULL)
    }
    return(tail(xs,n=1))
}

find.trace_id <- function(mmap, t, p) {
    cat("t=",t,"\np=",p,"\n")
    matched <- mmap[mmap$t <= t & t < mmap$t + mmap$dt & mmap$from <= p & p < mmap$to , ]
    return(matched$trace_id[1])
}

find.trace <- function(g, t, p) {
    trace.id <- find.trace_id(g$mmap,t,p)

    xs <- g$trace$trace[ g$trace$trace_id == trace.id ]

    if (length(xs)==0) {
        return(NULL)
    }
    return(tail(xs,n=1))
}


human.bytes <- function(mb) {
    if (mb < 2^10) {
        sprintf("%.1fMB",mb)
    } else if (mb < 2^20) {
        sprintf("%.1fGB",mb/2^10)
    } else if (mb < 2^30) {
        sprintf("%.1fTB",mb/2^20)
    }
}

# ggplot object with trace info
mmap.plot.trace <- function(matrix.file, trace.file, B=100) {
    gs    <- mmap.plot(matrix.file, B=B)
    trace <- mmap.read(trace.file)

    for (i in 1:length(gs)) {
        gs[[i]]$trace <- trace
        gs[[i]]$plot.panel  <- sprintf("%d_%dMB", gs[[i]]$pid, ceiling(gs[[i]]$areaMB))
        gs[[i]]$trace.panel <- sprintf("trace_%s", gs[[i]]$pid)
    }
    return(gs)
}

test <- function () {
    datafile = "build/data-2016-12-12_22h47m17s/frame.data"
    tracefile = "build/data-2016-12-12_22h47m17s/trace.data"
    gs <- mmap.plot(datafile)

    print(gs[[1]]$plot)
    gs
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
        titlePanel("Vismem"),
        mainPanel( tabs.panel, width = 12)
        )
}

shiny.render.plot <- function(g) {
    ## Please please don't mix impurity and laziness in your language..
    force(g)
    renderPlot({
        print(g$pid)

        d <- dim(g$mmap)
        if (is.na(d[1])) {
            print("data not available")
            print(dim(g$mmap))
            print(head(g$mmap))
            print(head(g$mmap))

        } else if (d[1] > 10^6) {
            print("data too big")
            print(dim(g$mmap))
            print(head(g$mmap))
            print(head(g$mmap))
        } else {
            g$plot
        }
    })
}


shiny.render.text <- function(g,input) {
    force(g)
    force(input)

    renderText({

        t     <- input$plot_click$x
        page  <- input$plot_click$y

        if (is.numeric(t) && is.numeric(page)) {
            p     <- mmap.sprint.page(page)
            trace <- find.trace(g,t,page)

            if (!is.string(trace)) {
                trace <- find.trace.exec(g, t, g$pid)
            }

            if (!is.string(trace)) {
                trace <- find.trace.clone.process(g, t, g$pid)
            }

            if (!is.string(trace)) {
                trace <- "no trace"
            }

            ## Print to stdout. Useful for scripting or in multi-monitor setup
            cat("pid=",g$pid, "\nt=",t , "\np=", p, "\ntrace:\n", trace,"\n")

            ## Paste into the html
            paste0("t=",t , "\np=", p, "\ntrace:", trace)
        }
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
