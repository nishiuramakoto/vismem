#!/usr/bin/perl
use strict;
use warnings;
my $hs = shift;
$hs =~/^(.*)\.hs$/ or die "$hs";
my $module = $1;


print <<"END";
import $module
import Test.Hspec
main = hspec \$ do
END


open(FH, $hs) or die "$!";
while (<FH>) {
    /^(spec_\w*)/ && print <<"END";
    $1
END
}
close FH;
