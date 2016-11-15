##############################
## Mandatory configuration  ##
##############################

# The command to trace the memory usage
# For the moment, the command must only clone threads, not processes (i.e. fork)
COMMAND ?= ls

# Download method for install.packages.
# One of: internal|wget|curl|lynx
# See ?download.file for details.
# On my Ubuntu R was not linked to libcurl, so..
R_DOWNLOAD_FILE_METHOD     = wget


#####################################################
## Optional configuration                          ##
## Try changing the followings if something breaks ##
#####################################################

# If ggplot2 fails to install, comment out ggplot2 and try apt (or your package manager)
R_PREREQUISITE             = shiny cluster ggplot2

# Try apt-get if ggplot2 failed to install directly from CRAN
APT_PREREQUISITE           = libpcre3-dev # r-cran-ggplot2 r-cran-cluster

# You need libpcre3-dev above
CABAL_PREREQUISITE         = split hashable IntervalMap pretty regex-pcre

# The path and the options for strace binary
# Note that the option '-k' may not be available for the strace from your distribution,
# in which case you either need to compile it for yourself, or abandon the stack trace facility.
STRACE                     = strace
STRACEFLAGS                = -k -f -e trace=memory
STRACE_OUTPUT              = strace.data

# The name of the Haskell binary
STRACE_PARSER_BIN          = ./strace_parser

GHC                        = ghc
GHCFLAGS                   = -O

DATA_FILE                  = out.data
TRACE_FILE                 = trace.data

##############################
## End of configuration     ##
##############################

HASKELL_SOURCES  = Main.hs
R_SOURCES        = mmap.R

R_INSTALL_PACKAGES_COMMAND = $(call r_install_packages, $(PREREQUISITE_R))
r_install_packages         = install.packages(c( $(call quote, $(1)) ))
quote                      = $(patsubst %, \"%\", $(1))

# Prerequisite.
# Don't mess with the system directly, just show necessary prerequisite packages

.PHONY: prerequisite prerequisite_r prerequisite_cabal prerequisite_apt prerequisite_strace
prerequisite : prerequisite_r prerequisite_apt prerequisite_cabal prerequisite_strace
prerequisite_r :
	@echo Try running the following commands in a R session: ;\
	@echo "options(\"download.file.method\" = \"$(R_DOWNLOAD_FILE_METHOD)\")" ;\
	@echo "$(R_INSTALL_PACKAGES_COMMAND)"

prerequisite_apt :
	@echo Run your package manager like this: ;\
	@echo sudo apt-get install $(APT_PREREQUISITE)

prerequisite_cabal :
	@echo You need the following cabal packages: ;\
	@echo cabal install $(CABAL_PREREQUISITE)

prerequisite_strace :
	$(STRACE) -o /dev/null $(STRACEFLAGS) /bin/ls || \
	( echo "$(STRACE) $(STRACEFLAGS) is not available." ;\
	  echo "Try running the following commands:" ;\
	  echo "git clone https://github.com/strace/strace.git &&" ;\
	  echo "cd strace && ./bootstrap && ./configure --prefix=\$HOME --with-libunwind &&" ;\
	  echo "make && make install" ;\
	) || false

# Haskell
$(STRACE_PARSER_BIN) : $(HASKELL_SOURCES)
	$(GHC) $(GHCFLAGS) -o $@ $^

# Process data

$(STRACE_FILE) :
	$(STRACE) -o $@ $(STRACEOPT) $(COMMAND)

$(DATA_FILE) : $(STRACE_PARSER_BIN)
	$(STRACE_PARSER_BIN) <
