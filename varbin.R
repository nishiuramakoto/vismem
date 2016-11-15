numbet <- 32
numtri <- 1e5
prob=5/6
#Fill a matrix
xcum <- matrix(NA, nrow=numtri, ncol=numbet+1)
for (i in 1:numtri) {
  x <- sample(c(0,1), numbet, prob=c(prob, 1-prob), replace = TRUE)
  xcum[i, ] <- c(i, cumsum(x)/cumsum(1:numbet))
}
colnames(xcum) <- c("trial", paste("bet", 1:numbet, sep=""))

mxcum <- reshape(data.frame(xcum), varying=1+1:numbet,
  idvar="trial", v.names="outcome", direction="long", timevar="bet")


library(plyr)
mxcum2 <- ddply(mxcum, .(bet, outcome), nrow)
mxcum3 <- ddply(mxcum2, .(bet), summarize,
                ymin=c(0, head(seq_along(V1)/length(V1), -1)),
                ymax=seq_along(V1)/length(V1),
                fill=(V1/sum(V1)))
head(mxcum3)

library(ggplot2)

p <- ggplot(mxcum3, aes(xmin=bet-0.5, xmax=bet+0.5, ymin=ymin, ymax=ymax)) +
    geom_rect(aes(fill=fill), colour="grey80") +
        scale_fill_gradient("Outcome", low="red", high="blue") +
            scale_y_continuous() +
                xlab("Bet")

print(p)
