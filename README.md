# Vismem: A Linux 64-bit VM emulator

(Not cabalized yet)

Synopsis:
    $ make show-prerequisites
	$ # Install prerequisites
    $ sudo apt-get install  libunwind8-dev libpcre3-dev r-base r-cran-ggplot2 r-cran-cluster
	$ git clone https://github.com/strace/strace.git && \
	     cd strace && ./bootstrap && ./configure --prefix=$HOME --with-libunwind && \
	     make && make install
    $ R
    > options("download.file.method" = "wget") # may be needed in Ubuntu
	> install.packages(c("shiny"))

    $ cabal install split hashable IntervalMap pretty regex-pcre

    $ make COMMAND="time ls"
	....
    Listening on http://127.0.0.1:5000
	....
	$ firefox http://127.0.0.1:5000
