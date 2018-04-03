#!/usr/bin/perl
use warnings;
use strict;
use diagnostics;
use feature 'say';
use Switch;
#use Cwd;

my ($gold, $file) = @ARGV;

open my $MYFILE, '<', $file or die "Can't open the file $file, $!\n";
my $text = join ' ', <$MYFILE>;

#say $text;
my (@sys) = ($text =~ m&\d+.+?([A-Z]{5,})&sg);
my (@ids) = ($text =~ m&([0-9]+)\t[A-Z]{5,}\s*\n&sg);
#foreach (@sys) {say;}
#say scalar(@sys);

#
#say $gold;
open my $ANS, '<', $gold or die "Can't open the file $gold, $!\n";
my $target = join ' ', <$ANS>;
#say $target;

my (@ans) = ($target =~ m&([A-Z]{5,})\s*\n&sg);
my (@gold_ids) = ($target =~ m&([0-9]+)\t.+?\t[A-Z]{5,}\s*\n&sg);
#my (@ans) = ($target =~ m&[0-9]+\t.+?([A-Z]{5,})\s*\n&sg);
#foreach (@ans) {say;}
#say scalar(@ans);

my %gold;
@gold{@gold_ids} = @ans;
#foreach (@ids) {say $gold{$_}}
my %system;
@system{@ids} = @sys;

my %m;

$m{"E"}{"E"} = 0;
$m{"E"}{"N"} = 0;
$m{"E"}{"C"} = 0;
$m{"C"}{"E"} = 0;
$m{"C"}{"N"} = 0;
$m{"C"}{"C"} = 0;
$m{"N"}{"E"} = 0;
$m{"N"}{"N"} = 0;
$m{"N"}{"C"} = 0;

my @false_pos;

foreach (@ids) {
	if ( $system{$_} ne "NEUTRAL" && $system{$_} ne $gold{$_} ) { push @false_pos, $_  }
	my $val = $gold{$_}."+".$system{$_};
	#say $val; 
	switch ($val) {
		case "ENTAILMENT+ENTAILMENT" 	    {$m{"E"}{"E"}++}
		case "ENTAILMENT+NEUTRAL" 		    {$m{"E"}{"N"}++}
		case "ENTAILMENT+CONTRADICTION"     {$m{"E"}{"C"}++}	
		case "CONTRADICTION+ENTAILMENT" 	{$m{"C"}{"E"}++}
		case "CONTRADICTION+NEUTRAL" 		{$m{"C"}{"N"}++}
		case "CONTRADICTION+CONTRADICTION"  {$m{"C"}{"C"}++}
		case "NEUTRAL+ENTAILMENT" 		    {$m{"N"}{"E"}++}
		case "NEUTRAL+NEUTRAL" 		        {$m{"N"}{"N"}++}
		case "NEUTRAL+CONTRADICTION"	    {$m{"N"}{"C"}++}
	}
}

say @false_pos." False positives:\n ".join(",", @false_pos);

say "               ENTAILMENT \t CONTRADICTION \t NEUTRAL";
say "ENTAILMENT         $m{'E'}{'E'}     \t     $m{'E'}{'C'}     \t     $m{'E'}{'N'} ";
say "CONTRADICTION      $m{'C'}{'E'}     \t     $m{'C'}{'C'}     \t     $m{'C'}{'N'} ";
say "NEUTRAL            $m{'N'}{'E'}     \t     $m{'N'}{'C'}     \t     $m{'N'}{'N'} ";

my $precision = ($m{'C'}{'C'} + $m{'E'}{'E'})  / ($m{'E'}{'E'} + $m{'C'}{'E'} + $m{'N'}{'E'} + $m{'E'}{'C'} + $m{'C'}{'C'} + $m{'N'}{'C'});
my $recall =    ($m{'C'}{'C'} + $m{'E'}{'E'})  / ($m{'E'}{'E'} + $m{'C'}{'E'} + $m{'E'}{'N'} + $m{'E'}{'C'} + $m{'C'}{'C'} + $m{'C'}{'N'});
my $accuracy =  ($m{'C'}{'C'} + $m{'E'}{'E'} + $m{'N'}{'N'})  / scalar(@ids);
my $fscore =    2 * $precision * $recall / ($precision + $recall);

say "precision = $precision";
say "recall    = $recall";
say "accuracy  = $accuracy";
say "f-score   = $fscore";




