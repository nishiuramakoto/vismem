# Vismem: A Linux VM Visualizer

(Not cabalized yet)

![alt screenshot](https://github.com/nishiuramakoto/vismem/blob/master/img/screenshot.png)

## Synopsis

1. Install the prerequisites.

        $ make show-prerequisites

        $ # An example in Ubuntu
        $ sudo apt-get install  libunwind8-dev libpcre3-dev r-base r-cran-ggplot2 r-cran-cluster

		$ # Compile strace or you will not be able to see stack traces
        $ git clone https://github.com/strace/strace.git && \
	          cd strace && ./bootstrap && ./configure --prefix=$HOME --with-libunwind && \
              make && make install

        $ # Install shiny
        $ R
        > options("download.file.method" = "wget") # may be needed in Ubuntu
    	> install.packages(c("shiny"))

        $ # Install cabal packages
        $ cabal install split hashable IntervalMap pretty regex-pcre

2. Edit the Makefile if necessary.


3. Run the command:

        $ make COMMAND="time ls"
        ...
	    DATA_DIR=build/data-2016-12-12_02h38m13s
        Listening on http://127.0.0.1:5000
	    ....
    	$ firefox http://127.0.0.1:5000

    Now you can click a region to show stack traces that are responsible for the state of the region.
    Clicking outside the region will show the trace of the `execve` call which is responsible for the pid.

4. Browse the previous results:

        $ # Feed the DATA_DIR shown above
        $ make DATA_DIR=build/data-2016-12-12_02h38m13s


## TODO
1. So slow.. should be like 100x faster.
2. Traces for munmap are not currently shown.
3. Current Sheaf module only supports 1-dimensional space, leading to
   huge inefficiency.
4. --quite switch may be needed
