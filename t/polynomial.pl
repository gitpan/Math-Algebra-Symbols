#!perl -w -I..
#______________________________________________________________________
# Symbolic algebra: polynomial tests.
# Perl License.
# PhilipRBrenan@yahoo.com, 2004.
#______________________________________________________________________

use Math::Algebra::Symbols;
use Test::More tests => 13;

my ($a, $b, $x, $y, $i, $c2, $c3) = symbols(qw(a b x y i 2 3));

ok(  sin($x)**2 + cos($x)**2      == 1,              'Pythagoras'); 
ok( ($x**8 - 1) /  ($x**4+1)      == $x**4-1,        'Polynomial division');
ok( ($x**2 - 1)                   == ($x-1) * ($x+1),'Polynomial multiplication');                        
ok(  abs(!($x+$y*$i)*!($a+$b*$i)) == 1,              'Length of product of units'); 

ok(  ($x+$x*$x)*$y/($x*$y)                == 1+$x);
ok(  (2*$x*$y**20) / (4*$y**19+4*$y**19)  == ($x*$y)/4);
ok(  (4*$b+4*$a*$b)/(4*$b+4*$a*$b)        == 1/($a+1)*$a+1/($a+1));

ok(  (sqrt($c2)+sqrt($c3))**4             == 10*(sqrt($c2)+sqrt($c3))**2 - 1);
ok(  ($x**16-1)/($x**8-1)                 == $x**8+1);
ok(  ($x+1)**11 / (1+$x)**12              == 1/($x+1));
ok(  ($x**2 + $y**2)/($x**2 + $y**2)      == 1);
ok(  ($x**2 + 2*$x*$y +$y**2) / ($x+$y)   == $x+$y);
ok(  (($x**2-1)/(($x+1)*($x-1)))          == 1);

exit(0);

