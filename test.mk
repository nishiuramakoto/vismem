##############################
## Mandatory configuration  ##
##############################

# The command to trace the memory usage.
# Override it with make COMMAND="your command"
# The whole process tree will be traced, and their outputs go to $(DATA_DIR) (see below).
COMMAND = time ls

# Download method for R's install.packages.
# One of: internal|wget|curl|lynx
# See ?download.file for details.
# On my Ubuntu R was not linked to libcurl, so..
R_DOWNLOAD_FILE_METHOD  = wget

# All outputs will go under this path.
# Must be a non empty string ('.' should work)
BUILD_DIR   = build

# The path prefix for the actually generated data
# This is not 'make clean'ed, use make dist-clean
# try 'make DATA_DIR=existing_dir' to analyze existing data
DATA_DIR_STEM  = $(BUILD_DIR)/data-


#####################################################
## Optional configuration                          ##
## Try changing the followings if something breaks ##
#####################################################



# These prerequisites are just a suggestion, I will not actually run them

# ggplot2 failed to install on my Ubuntu
R_PREREQUISITE             = shiny # cluster ggplot2

# This is more likely to work
APT_PREREQUISITE           = libunwind8-dev libpcre3-dev r-base r-cran-ggplot2 r-cran-cluster

# You need libpcre3-dev above
CABAL_PREREQUISITE         = split hashable IntervalMap pretty regex-pcre

# The path and the options for strace binary
# Note that the option '-k' may not be available from the strace of your distribution,
# in which case you either need to compile it for yourself, or abandon the stack trace facility.
# The output files go to $(DATA_DIR)
STRACE                     = strace
STRACEFLAGS                = -k -ff -e trace=memory -e trace=process
STRACE_OUTPUT_STEM         = strace.data
STRACE_OUTPUT_FILES        = $(wildcard $(DATA_DIR)/$(STRACE_OUTPUT_STEM).*)

# The name of the Haskell binary
STRACE_PARSER_BIN          = strace_parser

GHC                        = ghc
GHCFLAGS                   = -O

# These are generated in $(DATA_DIR)
DATA_FILE_STEM             = out.data
DATA_FILES                 = $(wildcard $(DATA_DIR)/$(DATA_FILE_STEM).*)
TRACE_FILE_STEM            = trace.data
TRACE_FILES                = $(wildcard $(DATA_DIR)/$(TRACE_FILE_STEM).*)

# What gets cleaned
CLEAN_FILES      = $(BUILD_DIR)/$(STRACE_PARSER_BIN)
CLEAN_PATHS      = $(BUILD_DIR)
DIST_CLEAN_FILES = $(STRACE_OUTPUT_FILES) $(DATA_FILES) $(TRACE_FILES)
DIST_CLEAN_PATHS = $(DATA_DIR)

##############################
## End of configuration     ##
##############################

haskell_sources  = Main.hs
r_script         = mmap.R

r_install_packages_command = install.packages(c($(call r-str-vector, $(R_PREREQUISITE))))

# Utility functions
r-str-vector               = $(call join-with-comma, $(call map-quote, $(1)))
join-with-comma            = $(subst $(space), $(comma),$(strip $(1)))
map-quote                  = $(patsubst %, \"%\", $(1))
space :=
space +=
comma := ,

test :
	echo $(DATA_DIR) $(TIMESTAMP)

$(DATA_DIR) :
	echo $@
