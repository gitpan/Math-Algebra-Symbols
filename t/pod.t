#!perl -w -I..
#______________________________________________________________________
# Symbolic algebra.
# Perl License.
# PhilipRBrenan@yahoo.com, 2004.
#______________________________________________________________________

use Math::Algebra::Symbols hyper=>1;
use Test::Simple tests=> 4;

($n, $x, $y) = symbols(qw(n x y));

ok(sin($x)**2 + cos($x)**2                                     == 1); 
ok((sin($n*$x)+cos($n*$x))->d->d->d->d/(sin($n*$x)+cos($n*$x)) == $n**4);
ok(tanh($x+$y) == (tanh($x)+tanh($y))/(1+tanh($x)*tanh($y)));
ok('2,3'       eq join(',', @{($x**2-5*$x+6) > $x}));

