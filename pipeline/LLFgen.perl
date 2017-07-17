#!/usr/bin/perl
use warnings;
use strict;
use diagnostics;
#use Getopt::Long::Configure ("bundling");
use Getopt::Long;
use feature 'say';
#use Cwd;
use FindBin; #get the directory of the perl script
#use Pod::Usage;



my ($txt, $candc, $easyccg, $html) = ('','','','');
my ($use_tok, $help, $verbose);

GetOptions (
	#'sent:s' => \$sent, 		# (un)tokenized sentence
	#'file:s' => \$spl_file,	# input file with sentences per line (spl)
	'candc:s' => \$candc, 		# candc command that returns an output in the boxer format			 
	'easyccg:s' => \$easyccg,	# easyccg command that returns an output in the prolog format	
	#'tab:s' => \$tableau_dir,	# the directory of the tableau prover Langpro
	'tok' => \$use_tok,			# use --tok to use the in-built shallow tokenizer otherwise provide a tokenized input 
	'html:s' => \$html,			# use --html FileName to print output in an html file rather than printing it in xml format in stdout
	'verbose' => \$verbose,		# use for verbosity
	'help' => \$help			# print help message
);	

if ($help) { &print_help; exit; }	

# for accessing the postpocessors of easyccg output, xml directory, xslt and css files, and langpro
my $script_dir = $FindBin::Bin; 
#say $script_dir;

# read the provided input or read it from the standard input
if (defined $ARGV[0]) {
	$txt = $ARGV[0];
} else {
	$txt = do { local $/; <STDIN> }; # slurp STDIN
	chomp($txt);
}

# tokenize tex if neccessary and generate sentence representations in Prolog 
my ($tok_txt, $sen_pl) = &user_input_to_sen_pl($txt, $use_tok);
my $LLFgen_code = "current_output(S), xml_senIDs_llfs(_, S)";
my $xslt = $html ? " | xsltproc --maxparserdepth 1000000 --maxdepth 1000000 -o $script_dir/../xml/$html $script_dir/../xml/xsl_dtd/ttterms.xsl -" : ''; 

# MAIN: parses the input and generates output incl. LLFs
if ( $candc || $easyccg ){
	my $ccg_pl;
	if ($easyccg) {
		say "Running easyCCG..."; 
		$ccg_pl = &sen_to_ccg_easyCCG($tok_txt, $easyccg);
	} else {
		say "Runing C&C...";
		#say $tok_txt;
		$ccg_pl = `echo "$tok_txt" | $candc`;
	}
	say "=" x 20 . " ccg.pl " . "=" x 20 . "\n$ccg_pl\n" . "=" x 60  if $verbose;
	my $assert = &assertz_prolog_clauses("$sen_pl \n\n $ccg_pl");
 	my $swipl = "swipl -f $script_dir/../main.pl -g \"$assert,\n $LLFgen_code, halt.\" $xslt";
	say "=" x 20 . " swipl " . "=" x 20 . "\n$swipl\n" . "=" x 60  if $verbose; 
	say "Loading and running LLFgen";
	my $proof = `$swipl`;
	if (!$html) {
		say "=" x 20 . " ccg-->ccgTerm-->corr_ccgTerm-->LLFs " . "=" x 20 . "\n$proof\n" . "=" x 60;
	}
	say "Done!";
} else {
	say "Error: no parser command provided"
} 

# takes a multiline text and a easyccg command
# the text is parsed using the command where -inputFile TEXT is inserted
# easyccg returns a prolog output that needs cosmetic changes by prolog_to_boxer.perl to be a prolog script
# the prolog script is converted into boxer prolog format via prolog_to_boxer_stdout/1 in prologCCG_to_boxerCCG.pl
# finally a boxer prolog script is returned   
sub sen_to_ccg_easyCCG {
	my ($in, $easy) = @_; 
	my $prolog_to_boxer = "$script_dir/prolog_to_boxer.perl"; # should be in the same dir with this file
	#say $in;
	my $out = `echo "$in" | $easy | perl $prolog_to_boxer`;
	#$easy =~ s/\b(-o +prolog)\b/ --inputFile <() \1/; 
	my $assertz = &assertz_prolog_clauses($out);
	my $prolog_syntax = "$script_dir/prologCCG_to_boxerCCG.pl"; # should be in the same dir with this file
	my $ccg_pl = `swipl -f $prolog_syntax -g \"$assertz, prolog_to_boxer_stdout, halt\"`;  
	return $ccg_pl; 
}

# takes a prolog script and returns a prolog script that asserts caluses of the source script
# used for passing prolog code via the command line  
sub assertz_prolog_clauses {
	($_) = @_;
	my @clauses = ($_ =~ m&((?:sen_id|ccg|w)\(.+?\))\.&sg);
	@clauses = map {"assertz($_)"} @clauses;
	my $asserts = join(",\n\n", @clauses);
	return $asserts;
}

# takes a multiline text and a flag weather to use an in-built tokenization
# returns a prolog script where each fact sen_id/5 states raw/tokenized sentences
# this is used to keep a link between derivations of the sentences and their surface/linguistic forms
sub user_input_to_sen_pl{
  	my ($in, $use_tok) = @_;
  	my @sen = split("\n", $in);
  	my @tok_sens;
  	my $ord = 1;
  	my $pl = ":- dynamic sen_id/5.\n:- multifile sen_id/5.\n:- discontiguous sen_id/5.\n\n";
  	foreach (@sen) {
		my $tok_sen = $use_tok ? &tok_sent($_) : $_; # (don't) use tokenization
		push(@tok_sens, $tok_sen);
		#$tok_in .= $tok_sen."\n"; 
		say "Sentence $ord: $tok_sen" if $verbose;
	   	$tok_sen =~ s/'/\\'/g; # escaping for prolog script
		$tok_sen =~ s/"/\\"/g; # escaping for -g "goal" and echo "txt"
	  	$pl .= "sen_id($ord, 1, 'p', 'nil', '$tok_sen').\n";
	   	$ord++;
  	}  
  	return (join("\n", @tok_sens), $pl);
}

# in-built shallow tokanization
# this is an optionala dn is used if --tok flag provided
sub tok_sent {
	($_) = @_;
	# html symbols to normal
	#s/&quot;/ '' /g; 	
	#s/&apos;/ '/g;	 
	#s/&amp;/&/g;
	s/n't / n't /g; 			# separate n't
	s/([a-zA-Z])'s /$1 's /g; 	# separate 's
	s/[,;:%\$]/ $& /g; 			# separate punctuations 
	#say "this is ".$_;
	s/\s+/ /g;					# remove unnecesary whitespace
	s/^\s+//g;
	s/\s+$//g;
	#s/isn 't/is not/g; 	# substitute abbreviations for negagtion
	#s/aren 't/are not/g;
	#s/don 't/do not/g;
	#s/doesn 't/does not/g;
	#s/can 't/can not/g;
	#s/couldn 't/could not/g;
	#s/wasn 't/was not/g;
	#s/won 't/will not/g;
	#say "final will be$_";
	#s/didn 't/did not/g; 
	# ? s/cannot/can not/g;
	return $_;  	
}

# prints help message
sub print_help {
	my $message = <<HELP_MESSAGE;

NAME
  LLF generator - a pipeline that produces LLFs (and co.)

SYNOPSIS
  LLFgen.perl  [--tok] [--html FILENAME] --candc CANDC  TEXT  
  LLFgen.perl  [--tok] [--html FILENAME] --easyccg EASYCCG  TEXT
  LLFgen.perl  --help

DESCRIPTION
  The pipeline takes a (un)tokenized text or sentence. First, it parses 
  the input with a CCG parser and then generates and prints several representations:
  CCG derivation > CCG term > corrected CCG term > (first) Lambda Logical Form (LLF).

OPTIONS
  --help
      Prints this message.

  --candc, -c    
      A command that uses C&C tools, take a tokenized TEXT and  returns derivations 
      in a boxer format. Either C&C or its rebanked version can be used for this. 
      See an example in USAGE.

  --easyccg, -e  
      A command that uses EasyCCG, takes a tokenized TEXT and returns derivations 
      in a prolog format. See an example in USAGE.  

  --html 
      If specified with FILE name, the output is printed in an html file, instead of 
      printing it in the xml format in STDOUT. This option is optional and useful for 
      humans to read the output.

  --tok, -t      
      Uses the in-built very shallow tokenizer to tokenize TEXT (optional).

USAGE
  It is handy first to define parser commands separately, for example:

    CANDC='candc/bin/candc --models candc/models --candc-printer boxer --candc-parser-noisy_rules=false'

    REBANKED_CANDC='candc/bin/candc --models candc/models --candc-super candc/models/super_hybrid --candc-parser candc/models/parser_hybrid --candc-printer boxer --candc-parser-noisy_rules=false'

    EASYCCG='candc/bin/pos --model candc/models/pos | candc/bin/ner --model candc/models/ner -ofmt "%w|%p|%n \n" | java -jar easyCCG/easyccg/easyccg.jar --model easyCCG/model -i POSandNERtagged -o prolog -r S[dcl]'

  Then run the pipeline from the LangPro directory as:

    ./pipeline/LLFgen.perl  --tok  --html LLFs.html  --candc "\${CANDC}"  "I am testing this pipeline"

  The html file is placed in LangPro/xml from where it has access to
  all the necessary style and script files. To generate LLFs for multiple
  sentences use --file input. Omit --html option to get output in STDOUT:

    cat sentence_per_line.txt | ./pipeline/LLFgen.perl  --tok  --candc "\${CANDC}"

CONTACT
  For more details visit https://github.com/kovvalsky/LangPro or 
  email to Lasha.Abziandize\@gmail.com
HELP_MESSAGE
	say $message;
}


