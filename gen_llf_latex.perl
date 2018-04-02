#!/usr/bin/perl
use warnings;
use strict;
use diagnostics;
use feature 'say';

#my ($sent) = @ARGV; 

#say $file;


my $exec = `/home/fibo/Desktop/candc-1.00/dev_ver/candc/bin/candc --models /home/fibo/Desktop/candc-1.00/dev_ver/candc/models --output /home/fibo/Desktop/NatTableau/ccg.pl --candc-printer boxer --candc-parser-noisy_rules=false`;

$exec = `swipl -s /home/fibo/Desktop/NatTableau/llf.pl -t 'gen_llfs_latex(_,_)'`;

$exec = `pdflatex latex/test_llf.tex -output-directory latex`;

$exec = `rm test_llf.aux; rm test_llf.log`;
