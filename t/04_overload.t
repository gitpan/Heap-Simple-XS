#!/usr/bin/perl -w
# Before `make install' is performed this script should be runnable with
# `make test'. After `make install' it should work as `perl t/1.t'

use warnings;	# Remove this for production. Assumes perl 5.6
use strict;

BEGIN { $^W = 1 };
use Test::More "no_plan";
use lib "t";
use Ties;

BEGIN {
    @Heap::Simple::implementors = qw(Heap::Simple::XS) unless
        @Heap::Simple::implementors;
    use_ok("Heap::Simple");
};
is(Heap::Simple->implementation, "Heap::Simple::XS");

# Test overload
{
    package Num;
    use Carp;
    use Data::Dumper;

    my $compares = 0;
    use overload 
        ">"  => sub { $compares++; return $_[0][0] > $_[1][0] },
        "eq" => sub { return $_[0][0] eq $_[1][0] },
        '""' => sub { return "Num $_[0][0]" };
    
    
    sub new {
        my ($class, $val) = @_;
        return bless [$val], $class;
    }

    sub compares {
        my $old = $compares;
        $compares = 0;
        return $old;
    }
}

my $heap = Heap::Simple->new(order => ">", elements => [Hash => "foo"]);
my $a = Num->new(4);
my $b = Num->new(8);
$heap->insert({foo => $a});
is(Num->compares, 0);
$heap->insert({foo => $b});
is(Num->compares, 1);
is_deeply([$heap->extract_upto(Num->new(0))], [{foo => $b}, {foo => $a}]);
is(Num->compares, 2);
