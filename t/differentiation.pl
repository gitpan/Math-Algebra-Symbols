#!perl -w -I..
#______________________________________________________________________
# Symbolic algebra.
# Perl License.
# PhilipRBrenan@yahoo.com, 2004.
#______________________________________________________________________

use Math::Algebra::Symbols;
use Test::More tests => 4;

$x = symbols(qw(x));
           
ok(  sin($x)    ==  sin($x)->d->d->d->d);
ok(  cos($x)    ==  cos($x)->d->d->d->d);
ok(  exp($x)    ==  exp($x)->d->d->d->d);
ok( (1/$x)->d   == -1/$x**2);
exit(0);

