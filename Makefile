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


#####################################################
## Optional configuration                          ##
## Try changing the followings if something breaks ##
#####################################################

# The path prefix for the actually generated data
# This is not 'make clean'ed, use make dist-clean
# try 'make DATA_DIR=existing_dir' to re-analyze existing data
DATA_DIR_STEM  = $(BUILD_DIR)/data-

# Careful not to include ':' in prerequisites.
# Also note the strictness here
TIMESTAMP := $(shell date  '+%F_%Hh%Mm%Ss')
DATA_DIR  := $(DATA_DIR_STEM)$(TIMESTAMP)

# These prerequisites are only a suggestion, I will not actually run them

# ggplot2 failed to install on my Ubuntu
R_PREREQUISITE             = shiny # cluster ggplot2

# This is more likely to work
APT_PREREQUISITE           = libunwind8-dev libpcre3-dev r-base r-cran-ggplot2 r-cran-cluster

# You need libpcre3-dev above
CABAL_PREREQUISITE         = split hashable IntervalMap pretty regex-pcre

# The path and the options for strace binary
# Note that the option '-k' may not be available from the strace of your distribution,
# in which case you either need to compile it for yourself, or abandon the stack trace facility.
# '-ff' cannot be used because it doesn't distinguish tid's and pid's..
STRACE               = strace
STRACEFLAGS          = -k -f -e trace=memory,process
STRACE_DATA          = strace.data

# The name of the Haskell binary
STRACE_PARSER_BIN    = strace_parser
GHC                  = ghc
GHCFLAGS             = -O -DNDEBUG
GHCFLAGS_PROF        = -prof -fprof-auto
GHC_RTS              = +RTS -P -hc -RTS


# Generated outputs by the parser
FRAME_DATA           = frame.data
TRACE_DATA           = trace.data

# What gets cleaned
CLEAN_FILES      = $(STRACE_PARSER_BIN) spec_Sheaf.hs spec_Hyper.hs screenshot.jpg
CLEAN_PATHS      = $(BUILD_DIR)
DIST_CLEAN_FILES = $(DATA_DIR)/$(STRACE_DATA) $(DATA_DIR)/$(FRAME_DATA) $(DATA_DIR)/$(TRACE_DATA)
DIST_CLEAN_PATHS = $(DATA_DIR)

##############################
## End of configuration     ##
##############################

haskell_sources  = Main.hs Hyper.hs Invariant.hs Pretty.hs PrettySheaf.hs Sheaf.hs
haskell_spec     = spec_Sheaf.hs spec_Hyper.hs
r_script         = mmap.R

r_install_packages_command = install.packages(c($(call r-str-vector, $(R_PREREQUISITE))))

# Utility functions
r-str-vector               = $(call join-with-comma, $(call map-quote, $(1)))
join-with-comma            = $(subst $(space), $(comma),$(strip $(1)))
map-quote                  = $(patsubst %, \"%\", $(1))
space :=
space +=
comma := ,


##################
## Recipes      ##
##################
all : show-prerequisites strace runR

# Prepare paths
$(BUILD_DIR) :
	mkdir -p $@

$(DATA_DIR) :
	mkdir -p $@

# Suggest (but not actually install) prerequisites.
.PHONY: show-prerequisites prerequisite_r prerequisite_cabal prerequisite_apt prerequisite_strace
show-prerequisites : prerequisite_r prerequisite_apt prerequisite_cabal prerequisite_strace
	@echo COMMAND=$(COMMAND)   ;\
	 echo DATA_DIR=$(DATA_DIR)

prerequisite_r :
	@echo Try running the following commands in a R session: ;\
	 echo "> options(\"download.file.method\" = \"$(R_DOWNLOAD_FILE_METHOD)\")" ;\
	 echo "> $(r_install_packages_command)"

prerequisite_apt :
	@echo Run your package manager like this: ;\
	 echo "$$ sudo apt-get install $(APT_PREREQUISITE)"

prerequisite_cabal :
	@echo You need the following cabal packages: ;\
	 echo "$$ cabal install $(CABAL_PREREQUISITE)"

prerequisite_strace :
	@$(STRACE) $(STRACEFLAGS) /bin/ls > /dev/null 2>&1 || \
	( echo "$(STRACE) $(STRACEFLAGS) is not ok." ;\
	  echo "Try running the following commands:" ;\
	  echo "$$ git clone https://github.com/strace/strace.git &&" ;\
	  echo "   cd strace && ./bootstrap && ./configure --prefix=\$$HOME --with-libunwind &&" ;\
	  echo "   make && make install" ;\
	) || false


# Haskell
$(BUILD_DIR)/$(STRACE_PARSER_BIN) : $(haskell_sources) | $(BUILD_DIR)
	$(GHC) $(GHCFLAGS) -o $@ $^

$(BUILD_DIR)/$(STRACE_PARSER_BIN)_prof : $(haskell_sources) | $(BUILD_DIR)
	$(GHC) $(GHCFLAGS) $(GHCFLAGS_PROF) -o $@ $^

spec_%.hs : %.hs
	perl spec.pl $< > $@

.PHONY : spec
spec : $(haskell_spec)
	for x in $^; \
	do \
		runghc $$x ; \
	done

# Strace
# A hack to deal with unpredictable generated files
.PHONY : strace
strace : $(DATA_DIR)/$(STRACE_DATA)
$(DATA_DIR)/$(STRACE_DATA) : | $(DATA_DIR)
	$(STRACE) -o $@ $(STRACEFLAGS) $(COMMAND) || test -r $@ # Proceed even in errors

# Generate data frames for R.
.PHONY : parse
parse : $(DATA_DIR)/$(FRAME_DATA) $(DATA_DIR)/$(TRACE_DATA)

## A hackish way to track DAGs
%/$(FRAME_DATA) %/$(TRACE_DATA): $(BUILD_DIR)/$(STRACE_PARSER_BIN) %/$(STRACE_DATA)
	$^ --output=$*/$(FRAME_DATA) --trace=$*/$(TRACE_DATA)

# Profiling

.PHONY : prof
prof : $(STRACE_PARSER_BIN)_prof.prof view
%.prof %.hp: $(BUILD_DIR)/% $(DATA_DIR)/$(STRACE_DATA) Makefile
	$< $(DATA_DIR)/$(STRACE_DATA) \
		 --output=$(DATA_DIR)/$(FRAME_DATA) \
		 --trace=$(DATA_DIR)/$(TRACE_DATA) \
		 $(GHC_RTS)

.PHONY : view
view : $(STRACE_PARSER_BIN)_prof.svg
	display $<

%.svg : %.hp
	hp2pretty $<

# Run the Shiny server
.PHONY: runR
runR : $(r_script) $(DATA_DIR)/$(FRAME_DATA) $(DATA_DIR)/$(TRACE_DATA)
	Rscript $^

# Misc
.PHONY : screenshot
screenshot : img/screenshot.jpg
img/screenshot.jpg :
	import $@

# Cleaners
.PHONY : clean dist-clean dist-clean-1

clean :
	rm    $(CLEAN_FILES) strace_parser_prof.* ;\
	rmdir $(CLEAN_PATHS) ;\
	true

dist-clean :
	make -e dist-clean-1

dist-clean-1 :
	rm    $(DIST_CLEAN_FILES) ;\
	rmdir $(DIST_CLEAN_PATHS) ;\
	true

# Dangerous
purge :
	rm -rf $(BUILD_DIR)
