package Heap::Simple::XS;
use 5.006001;
use strict;
use warnings;
use Carp;

our $VERSION = '0.01';

require XSLoader;
XSLoader::load('Heap::Simple::XS', $VERSION);

sub implementation() {
    return __PACKAGE__;
}

1;
__END__

=head1 NAME

Heap::Simple::XS - An XS implementation of the Heap::Simple interface

=head1 SYNOPSIS

    # Let Heap::Simple decide which implementation that provides its interface
    # it will load and use. This may be Heap::Simple::XS or it may not be.
    # Still, this is the normal way of using Heap::Simple
    use Heap::Simple;
    my $heap = Heap::Simple->new(...);
    # Use heap as described in the Heap::Simple documentation

    # If for some reason you insist on using this version:
    use Heap::Simple::XS;
    my $heap = Heap::Simple::XS->new(...);
    # Use the XS heap as described in the Heap::Simple documentation

=head1 DESCRIPTION

This module provides a pure perl implementation of the interface described
in L<Heap::Simple|Heap::Simple>. Look there for a description.

=head1 NOTES

=over

=item

Even though this implementation is written in C, it fully supports
overloading and magic (like L<ties|perltie>).

=item

The dirty option will cause scalars for the C<E<lt>> and C<E<gt>> orders
to be stored internally as an NV (double or long double). This means you lose
magic, overload and any internal integer representation.

The C<E<lt>> and C<E<gt>> order will also cause C<Array> and C<Hash> elements
to get their key internally cached as a NV. So indirect changes to the value
won't be noticed anymore (but most of the time you shouldn't do that anyways).

=item

Heap::Simple->implementation will return C<"Heap::Simple::XS"> if it selected
this module.

=back

=head1 EXPORT

None.

=head1 SEE ALSO

L<Heap::Simple>,
L<Heap::Simple::Perl>

=head1 AUTHOR

Ton Hospel, E<lt>Heap::Simple::XS@ton.iguana.beE<gt>

Parts are inspired by code by Joseph N. Hall
L<http://www.perlfaq.com/faqs/id/196>

=head1 COPYRIGHT AND LICENSE

Copyright (C) 2004 by Ton Hospel

This library is free software; you can redistribute it and/or modify
it under the same terms as Perl itself, either Perl version 5.6.1 or,
at your option, any later version of Perl 5 you may have available.

=cut
