#!/usr/bin/perl -w
use 5.006001;
use ExtUtils::MakeMaker;
BEGIN {
    @Heap::Simple::implementors = qw(CGI) unless @Heap::Simple::implementors;
}
WriteMakefile
    (NAME		=> 'Heap::Simple::XS',
     VERSION_FROM	=> 'XS.pm', # finds $VERSION
     PERL_MALLOC_OK	=> 1,
     'PREREQ_PM'	=> {
         "Heap::Simple"	=> 0.08,	# implementor switch
         "Test::More"	=> 0.11,	# For the tests only
     },
     AUTHOR	=> 'Ton Hospel <Heap::Simple::XS@ton.iguana.be>',
     # OPTIMIZE		=> "-g",
     LIBS	=> [''], # e.g., '-lm'
     DEFINE	=> '', # e.g., '-DHAVE_SOMETHING'
     INC	=> '-I.', # e.g., '-I. -I/usr/include/other'
);
