#!/usr/bin/perl
use warnings;
use strict;
use diagnostics;
use feature 'say';
use Switch;
#use Cwd;

# command
# perl combine\ two\ classifiers.pl sick_test_annotated/SICK_test_annotated.txt NaturalTableau.txt task1-all-primary-runs/Illinois-LH_run1/Illinois-LH_run1primary.txt 

my $gold   = shift @ARGV;
my $file_1 = shift @ARGV; #has high precision
my $file_2 = shift @ARGV;

####### system 1 ######### has high precision
open my $MYFILE_1, '<', $file_1 or die "Can't open the file $file_1, $!\n";
my $text_1 = join ' ', <$MYFILE_1>;
my (@ans_sys1) = ($text_1 =~ m&\d+\t([A-Z]{5,})\s*\n&sg);
my (@ids) = ($text_1 =~ m&(\d+)\t[A-Z]{5,}\s*\n&sg);
my %system1;
@system1{@ids} = @ans_sys1;

####### system 2  
open my $MYFILE_2, '<', $file_2 or die "Can't open the file $file_2, $!\n";
my $text_2 = join ' ', <$MYFILE_2>;
my (@ans_sys2) = ($text_2 =~ m&\d+\t([A-Z]{5,})\s*\n&sg);
my (@ids_sys2) = ($text_2 =~ m&(\d+)\t[A-Z]{5,}\s*\n&sg);
my %system2;
foreach my $i (0..$#ids) { 
	#say @ids;
	#say "$i --> $ids[$i] and $ids_sys2[$i]"; 
    if ($ids[$i] eq $ids_sys2[$i]) {
    	$system2{$ids_sys2[$i]} = $ans_sys2[$i]
    } else {
    	say "different answers (line $i): ${ids[$i]} vs ${ids_sys2[$i]}"; exit
    }
}    
#if (@ids ~~ @ids_sys2) { @system2{@ids} = @ans_sys2 } else {say "different answers"; exit}

####### gold answers
open my $ANS, '<', $gold or die "Can't open the file $gold, $!\n";
my $target = join ' ', <$ANS>;

####### Htbrid answers print file
open my $HYBRIDFILE, '>', 'HYBRID_ANSWERS' or die "Can't open the file $file_1, $!\n";
say $HYBRIDFILE "===== HYBRID =====";

# this extraction works for both sick and fracas gold answer files
my (@gold_ids) = ($target =~ m&([0-9]+)\t.*?[A-Z]{5,}\s*\n&sg);
my (@ans_gold) = ($target =~ m&\t([A-Z]{5,})\s*\n&sg);
my %gold;
@gold{@gold_ids} = @ans_gold;

######## COMBINE
say "Gold: ids(".scalar(@gold_ids)."), answers(".scalar(@ans_gold).")";
say "sys1: ids(".scalar(@ids)."), answers(".scalar(@ans_sys1).")";
say "sys2: ids(".scalar(@ids_sys2)."), answers(".scalar(@ans_sys2).")";


my $num = scalar(@ids);
my %m;
my $val;

$m{"E"}{"E"} = 0;
$m{"E"}{"N"} = 0;
$m{"E"}{"C"} = 0;
$m{"C"}{"E"} = 0;
$m{"C"}{"N"} = 0;
$m{"C"}{"C"} = 0;
$m{"N"}{"E"} = 0;
$m{"N"}{"N"} = 0;
$m{"N"}{"C"} = 0;

my @chosen_ids = (247,1696,1813,1868,2843,2895,3090,3406,3806,3974,4051,4887,5034,5709,5711,5713,5925,6690,7885,8237,8318,8372,9732);

my @sys1_beats_sys2;
my @sys2_beats_sys1;
my @diff_ids;


foreach my $i (@ids) { 
    if ( $system1{$i} ne $system2{$i} ) {   
		#say sprintf "%-6s: %-15s\t%-15s\t%-15s", $i, $gold{$i}, $system1{$i}, $system2{$i};
		push @diff_ids, $i;
		if ( $system1{$i} eq $gold{$i} ) { push @sys1_beats_sys2, $i }
		elsif ( $system2{$i} eq $gold{$i} ) { push @sys2_beats_sys1, $i } else {1} 
	} else {1}
	# hybrid answer
	if 		( $system1{$i} eq "NEUTRAL" )  { $val = $system2{$i} } 
	elsif 	( $system2{$i} eq "NEUTRAL" )  { $val = $system1{$i} }
	elsif	( $system1{$i} ne $system2{$i} ) { $val = "NEUTRAL"; say sprintf "Diverges: %-6s: %-18s\t%-18s\t%-18s", $i, $gold{$i}, $system1{$i}, $system2{$i};   }  
	else	{ $val = $system1{$i} }
	# print combined answer
	say $HYBRIDFILE $i."\t".$val;
	# freq count
	my $fin = $gold{$i}."+".$val;
	switch ($fin) {
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

say @diff_ids." Differences:\n ".join(",", @diff_ids);
say @sys1_beats_sys2." times Sys1 > Sys2:\n ".join(",",  @sys1_beats_sys2);
say @sys2_beats_sys1." times Sys2 > Sys1:\n ".join(",",  @sys2_beats_sys1);

# Print confusion matrix
say " COMBINED      ENTAILMENT \t CONTRADICTION \t NEUTRAL";
say "ENTAILMENT         $m{'E'}{'E'}     \t     $m{'E'}{'C'}     \t     $m{'E'}{'N'} ";
say "CONTRADICTION      $m{'C'}{'E'}     \t     $m{'C'}{'C'}     \t     $m{'C'}{'N'} ";
say "NEUTRAL            $m{'N'}{'E'}     \t     $m{'N'}{'C'}     \t     $m{'N'}{'N'} ";

my $precision = ($m{'C'}{'C'} + $m{'E'}{'E'})  / ($m{'E'}{'E'} + $m{'C'}{'E'} + $m{'N'}{'E'} + $m{'E'}{'C'} + $m{'C'}{'C'} + $m{'N'}{'C'});
my $recall =    ($m{'C'}{'C'} + $m{'E'}{'E'})  / ($m{'E'}{'E'} + $m{'C'}{'E'} + $m{'E'}{'N'} + $m{'E'}{'C'} + $m{'C'}{'C'} + $m{'C'}{'N'});
my $accuracy =  ($m{'C'}{'C'} + $m{'E'}{'E'} + $m{'N'}{'N'})  / $num;
my $fscore =    2 * $precision * $recall / ($precision + $recall);

say "precision = $precision";
say "recall    = $recall";
say "accuracy  = $accuracy";
say "f-score   = $fscore";

