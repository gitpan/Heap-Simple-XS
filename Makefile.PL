#!/usr/bin/perl -w
use 5.006001;
use ExtUtils::MakeMaker;
BEGIN {
    @Heap::Simple::implementors = qw(CGI) unless @Heap::Simple::implementors;
}

# Allows to suppress all questions with -n
use Getopt::Std;
our $opt_n;
getopts("n") || die "Usage: $0 [-n]\n";

my $benchmark = 0;
my $benchmark_others = 0;

unless ($opt_n) {
    print <<EOT

   Note that you can avoid these questions by passing
   the '-n' option to 'Makefile.PL'.

EOT
;
    $benchmark = prompt("Run Heap::Simple benchmarks during 'make test' ?", "n") =~ /^y/i;
    if ($benchmark) {
        $benchmark_others = 
            prompt("Benchmarks against other heap modules that happen to be installed on this machine during 'make test' ?", "n") =~ /^y/i;
    }
}
my $option_file = "t/options";
my $new = "$option_file.new.$$";
open(my $fh, ">", $new) || die "Could not open '$new': $!";
printf($fh "BENCHMARK=%d\nBENCHMARK_OTHERS=%d\n", 
       $benchmark ? 1 : 0, 
       $benchmark_others ? 1 : 0) || die "Error writing to '$new': $!";
eval {
    close($fh) || die "Could not close '$new': $!";
    rename($new, $option_file) || 
        die "Could not rename '$new' to '$option_file': $!";
};
if ($@) {
    $fh = undef;	# close file if open
    unlink($new) || die "Could not unlink '$new': $! after $@";
    die $@;
}

WriteMakefile
    (NAME		=> 'Heap::Simple::XS',
     VERSION_FROM	=> 'XS.pm', # finds $VERSION
     PERL_MALLOC_OK	=> 1,
     'PREREQ_PM'	=> {
         "Heap::Simple"	=> 0.09,	# implementor switch
         "Test::More"	=> 0.11,	# For the tests only
     },
     AUTHOR	=> 'Ton Hospel <Heap-Simple-XS@ton.iguana.be>',
     # OPTIMIZE		=> "-g",
     LIBS	=> [''], # e.g., '-lm'
     DEFINE	=> '', # e.g., '-DHAVE_SOMETHING'
     INC	=> '-I.', # e.g., '-I. -I/usr/include/other'
);
