#!perl -w
#_ Symbols ______________________________________________________________
# Symbolic algebra.
# Perl License.
# PhilipRBrenan@yahoo.com, 2004.
#________________________________________________________________________

package Math::Algebra::Symbols;
$VERSION = 1.18;

use Math::Algebra::SymbolsSum;
use Math::Algebra::SymbolsTerm;
use Carp;

#_ Symbols ______________________________________________________________
# Constructers
#________________________________________________________________________

sub new              {symbols()->new};
sub newFromString($) {symbols()->newFromString(@_)};
sub n(@)             {symbols()->n(@_)};

#_ Symbols ______________________________________________________________
# Confirm type
#________________________________________________________________________

sub isSymbols($) {1}; 

#_ Symbols ______________________________________________________________
# Useful constants
#________________________________________________________________________

sub zero()  {symbols()->$zero}
sub one()   {symbols()->$one}
sub two()   {symbols()->$two}
sub mOne()  {symbols()->$mOne}
sub i()     {symbols()->$i}
sub mI()    {symbols()->$mI}
sub half()  {symbols()->$half}
sub mHalf() {symbols()->$mHalf}
sub pi()    {symbols()->$pi}   

#_ Symbols ______________________________________________________________
# Import - parameters from caller - set up as requested.
#________________________________________________________________________

sub import
 {my %P = (program=>@_);
  my %p; $p{lc()} = $P{$_} for(keys(%P));

#_ Symbols ______________________________________________________________
# New symbols term constructor - export to calling package.
#________________________________________________________________________

  my $s = <<'END';
package XXXX;

BEGIN  {delete $XXXX::{NNNN}}

sub NNNN
 {return SSSSSum::n(@_);
 }
END

#_ Symbols ______________________________________________________________
# Complex functions: re, im, dot, cross, conjugate, modulus              
#________________________________________________________________________
  
  if (exists($p{complex}))
   {$s .= <<'END';
BEGIN  {delete @XXXX::{qw(conjugate cross dot im modulus re unit)}}
END
    $s .= <<'END' if $p{complex};
sub conjugate($)  {$_[0]->conjugate()}
sub cross    ($$) {$_[0]->cross    ($_[1])}
sub dot      ($$) {$_[0]->dot      ($_[1])}
sub im       ($)  {$_[0]->im       ()}
sub modulus  ($)  {$_[0]->modulus  ()}
sub re       ($)  {$_[0]->re       ()}
sub unit     ($)  {$_[0]->unit     ()}
END
   }

#_ Symbols ______________________________________________________________
# Trigonometric functions: tan, sec, csc, cot              
#________________________________________________________________________

  if (exists($p{trig}) or exists($p{trigonometric}))
   {$s .= <<'END';
BEGIN  {delete @XXXX::{qw(tan sec csc cot)}}
END
    $s .= <<'END' if $p{trig} or $p{trigonometric};
sub tan($) {$_[0]->tan()}
sub sec($) {$_[0]->sec()}
sub csc($) {$_[0]->csc()}
sub cot($) {$_[0]->cot()}
END
   }
  if (exists($p{trig}) and exists($p{trigonometric}))
   {croak 'Please use specify just one of trig or trigonometric';
   }

#_ Symbols ______________________________________________________________
# Hyperbolic functions: sinh, cosh, tanh, sech, csch, coth              
#________________________________________________________________________

 if (exists($p{hyper}) or exists($p{hyperbolic}))
  {$s .= <<'END';
BEGIN  {delete @XXXX::{qw(sinh cosh tanh sech csch coth)}}
END
    $s .= <<'END' if $p{hyper} or $p{hyperbolic};
sub sinh($) {$_[0]->sinh()}
sub cosh($) {$_[0]->cosh()}
sub tanh($) {$_[0]->tanh()}
sub sech($) {$_[0]->sech()}
sub csch($) {$_[0]->csch()}
sub coth($) {$_[0]->coth()}
END
  }
 if (exists($p{hyper}) and exists($p{hyperbolic}))
  {croak 'Please specify just one of hyper or hyperbolic';
  }

#_ Symbols ______________________________________________________________
# Export to calling package.
#________________________________________________________________________

  my $name   = 'symbols';
     $name   = $p{symbols} if exists($p{symbols});
  my ($main) = caller();
  my $pack   = __PACKAGE__;   

  $s=~ s/XXXX/$main/g;
  $s=~ s/NNNN/$name/g;
  $s=~ s/SSSS/$pack/g;
  eval($s);

#_ Symbols ______________________________________________________________
# Check options supplied by user
#________________________________________________________________________

  delete @p{qw(
symbols program trig trigonometric hyper hyperbolic complex
)};

  croak "Unknown option(s): ". join(' ', keys(%p))."\n\n". <<'END' if keys(%p);

Valid options are:

  symbols=>'symbols' Create a routine with this name in the callers
                  namespace to create new symbols. The default is
                  'symbols'.


  trig   =>0      The default, no trigonometric functions         
  trig   =>1      Export trigonometric functions: tan, sec, csc, cot.
                  sin, cos are created by default by overloading 
                  the existing Perl sin and cos operators.

  trigonometric can be used instead of trig.


  hyper  =>0      The default, no hyperbolic functions         
  hyper  =>1      Export hyperbolic functions:
                    sinh, cosh, tanh, sech, csch, coth.

  hyperbolic can be used instead of hyper.


  complex=>0      The default, no complex functions         
  complex=>1      Export complex functions:
                    conjugate, cross, dot, im, modulus, re,  unit

END
 }

#_ Symbols ______________________________________________________________
# Package installed successfully
#________________________________________________________________________

1;

__DATA__

#______________________________________________________________________
# User guide.
#______________________________________________________________________

=head1 NAME

Math::Algebra::Symbols - Symbolic Algebra using Perl

=head1 SYNOPSIS

 use Math::Algebra::Symbols hyper=>1;

 my ($n, $x, $y) = symbols(qw(n x y));

 my  $a    += ($x**8 - 1)/($x-1);
 my  $b    +=  sin($x)**2 + cos($x)**2; 
 my  $c    += (sin($n*$x) + cos($n*$x))->d->d->d->d / (sin($n*$x)+cos($n*$x));
 my  $d     =  tanh($x+$y) == (tanh($x)+tanh($y))/(1+tanh($x)*tanh($y));
 my ($e,$f) =  @{($x**2 eq 5*$x-6) > $x};

 print "$a\n$b\n$c\n$d\n$e,$f\n";

 # $x+$x**2+$x**3+$x**4+$x**5+$x**6+$x**7+1
 # 1
 # $n**4
 # 1
 # 2,3

=head1 DESCRIPTION

This package supplies a set of functions and operators to manipulate
operator expressions algebraically  using the familiar Perl syntax.

These expressions are constructed
from L</Symbols>, L</Operators>, and L</Functions>, and processed via
L</Methods>.  For examples, see: L</Examples>.

=head2 Symbols

Symbols are created with the exported B<symbols()> constructor routine:

 use Math::Algebra::Symbols;

 my ($x, $y, $i, $o, $pi) = symbols(qw(x y i 1 pi));

 print "$x $y $i $o\n";

 # $x $y $i 1

The B<symbols()> routine constructs references to symbolic variables and
symbolic constants from a list of names and integer constants.

The special symbol B<i> is recognized as the square root of B<-1>.

The special symbol B<pi> is recognized as the smallest positive real
that satisfies:

 use Math::Algebra::Symbols;

 ($i, $pi) = symbols(qw(i pi));

 print exp($i*$pi), "\n";

 # -1

=head3 Constructor Routine Name

If you wish to use a different name for the constructor routine, say
B<S>:

 use Math::Algebra::Symbols symbols=>'S';

 my ($x, $y, $i, $o) = S(qw(x y i 1));

 print "$x $y $i $o\n";

 # $x $y $i 1

=head3 Constructing Expressions with Big Integers

If you wish to use Math::Algebra::Symbols constructed with big integers from L<Math::BigInt>:

 use Math::Algebra::Symbols BigInt=>1;

 my $z = symbols('1234567890987654321/1234567890987654321');

 print "$z\n";

 # 1

=head2 Operators

L</Symbols> can be combined with L</Operators> to create symbolic expressions:

=head3 Arithmetic operators


=head4 Arithmetic Operators: B<+> B<-> B<*> B</> B<**> 
            
 use Math::Algebra::Symbols;

 ($x, $y) = symbols(qw(x y));

 $z = ($x**2-$y**2)/($x-$y);

 print "$z\n";

 # $x+$y

The auto assign versions of these operators: B<+=> B<-=> B<*=> B</=> all
work courtesy of Perl Auto-Magical Operator Generation.

=head4 Square root Operator: B<sqrt>       

 use Math::Algebra::Symbols;

 $x = symbols(qw(x));

 $z = sqrt(-$x**2);

 print "$z\n";

 # $i*$x

=head4 Exponential Operator: B<exp>       

 use Math::Algebra::Symbols;

 $x = symbols(qw(x));

 $z = exp($x)->d($x);

 print "$z\n";

 # exp($x)

=head4 Logarithm Operator: B<log>       

 use Math::Algebra::Symbols;

 $x = symbols(qw(x));

 $z = log(exp($x)*exp($x));

 print "$z\n";

 # 2*$x

=head4 Sine and Cosine Operators: B<sin> and B<cos>       

 use Math::Algebra::Symbols;

 $x = symbols(qw(x));

 $z = sin($x)**2 + cos($x)**2;

 print "$z\n";

 # 1

=head3 Relational operators                                   

=head4 Relational operators: B<==>, B<!=> 

 use Math::Algebra::Symbols;

 ($x, $y) = symbols(qw(x y));

 $z = ($x**2-$y**2)/($x+$y) == $x - $y;

 print "$z\n";

 # 1

The relational equality operator B<==> compares two symbolic expressions
and returns TRUE(1) or FALSE(0) accordingly. B<!=> produces the opposite
result.

=head4 Relational operator: B<eq> 

 use Math::Algebra::Symbols;

 ($x, $v, $t) = symbols(qw(x v t));

 $z = ($v eq $x / $t)->solve(qw(x in terms of v t));

 print "x=$z\n";

 # x=$v*$t

The relational operator B<eq> is a synonym for the minus B<-> operator,
with the expectation that later on the L<solve()|/Solving equations>
function will be used to simplify and rearrange the equation. You may
prefer to use B<eq> instead of B<-> to enhance readability, there is no
functional difference.

=head3 Complex operators

=head4 Complex operators: the B<dot> operator: B<^>       

 use Math::Algebra::Symbols;

 ($a, $b, $i) = symbols(qw(a b i));

 $z = ($a+$i*$b)^($a-$i*$b);

 print "$z\n";

 # $a**2-$b**2

Note the use of brackets.  The B<^> operator has low priority.

The B<^> operator treats its left hand and right hand arguments as
complex numbers, which in turn are regarded as two dimensional vectors
to which the vector dot product is applied.

=head4 Complex operators: the B<cross> operator: B<x>       

 use Math::Algebra::Symbols;

 ($x, $i) = symbols(qw(x i));

 $z = $i*$x x $x;

 print "$z\n";

 # $x**2

The B<x> operator treats its left hand and right hand arguments as
complex numbers, which in turn are regarded as two dimensional vectors
defining the sides of a parallelogram. The B<x> operator returns the
area of this parallelogram.

Note the space before the B<x>, otherwise Perl is unable to disambiguate
the expression correctly.

=head4 Complex operators: the B<conjugate> operator: B<~>       

 use Math::Algebra::Symbols;

 ($x, $y, $i) = symbols(qw(x y i));

 $z = $x+$i*$y;

 print ~$z, "\n";

 # $x-$i*$y

The B<~> operator returns the complex conjugate of its right hand side.

=head4 Complex operators: the B<modulus> operator: B<abs>       

 use Math::Algebra::Symbols;

 ($x, $i) = symbols(qw(x i));

 $z = abs($x+$i*$x);

 print "$z\n";

 # sqrt(2)*$x

The B<abs> operator returns the modulus (length) of its right hand side.

=head4 Complex operators: the B<unit> operator: B<!>       

 use Math::Algebra::Symbols;

 $i = symbols(qw(i));

 $z = !($i+1);

 print "$z\n";

 # $i*sqrt(1/2)+sqrt(1/2)

The B<!> operator returns a complex number of unit length pointing in
the same direction as its right hand side.

=head3 Equation Manipulation Operators

=head4 Equation Manipulation Operators: B<Simplify> operator: B<+=>

 use Math::Algebra::Symbols;
 
 ($x) = symbols(qw(x));
 
  $z += ($x**8 - 1)/($x-1);

 print "$z\n";

 # $x+$x**2+$x**3+$x**4+$x**5+$x**6+$x**7+1

The simplify operator B<+=> is a synonym for the
L<simplify()|/"simplifying_equations:_simplify()"> method, if and only
if, the target on the left hand side initially has a value of undef.
Admittedly this is very strange behavior: it arises due to the shortage
of over-rideable operators in Perl: in particular it arises due to the
shortage of over-rideable unary operators in Perl. Never-the-less: this
operator is useful as can be seen in the L<Synopsis|/"synopsis">, and
the desired pre-condition can always achieved by using B<my>.

=head4 Equation Manipulation Operators: B<Solve> operator: B<E<gt>> 

 use Math::Algebra::Symbols;

 ($x, $v, $t) = symbols(qw(x v t));

 $z = ($v eq $x / $t) > [qw(x in terms of v t)];

 print "x=$z\n";

 # x=$v*$t

The solve operator B<E<gt>> is a synonym for the
L<solve()|/"Solving_equations:_solve()"> method.

The priority of B<E<gt>> is higher than that of B<eq>, so the brackets
around the equation to be solved are necessary until Perl provides a
mechanism for adjusting operator priority (cf. Algol 68).

If the equation is in a single variable, the single variable
may be named after the B<E<gt>> operator without the use of [...]:

 use Math::Algebra::Symbols;

 my $rabbit  = 10 + 5 * $t;
 my $fox     = 7 * $t * $t;
 my ($a, $b) = @{($rabbit eq $fox) > $t};

 print "$a\n";

 # 1/14*sqrt(305)+5/14

If there are multiple solutions, (as in the case of polynomials), B<E<gt>>
returns an array of symbolic expressions containing the solutions.

This example was provided by Mike Schilli m@perlmeister.com.

=head2 Functions

Perl operator overloading is very useful for producing compact
representations of algebraic expressions. Unfortunately there are only a
small number of operators that Perl allows to be overloaded. The
following functions are used to provide capabilities not easily expressed
via Perl operator overloading.

These functions may either be called as methods from symbols constructed
by the L</Symbols> construction routine, or they may be exported into
the user's namespace as described in L</EXPORT>.

=head3 Trigonometric and Hyperbolic functions

=head4 Trigonometric functions

 use Math::Algebra::Symbols trig=>1;

 ($x, $y) = symbols(qw(x y));

 $z = sin($x)**2 == (1-cos(2*$x))/2;

 print "$z\n";

 # 1

The trigonometric functions B<cos>, B<sin>, B<tan>, B<sec>, B<csc>,
B<cot> are available, either as exports to the caller's name space, or
as methods.

=head4 Hyperbolic functions

 use Math::Algebra::Symbols hyper=>1;

 ($x, $y) = symbols(qw(x y));

 $z = tanh($x+$y)==(tanh($x)+tanh($y))/(1+tanh($x)*tanh($y));

 print "$z\n";

 # 1

The hyperbolic functions B<cosh>, B<sinh>, B<tanh>, B<sech>, B<csch>,
B<coth> are available, either as exports to the caller's name space, or
as methods.

=head3 Complex functions

=head4 Complex functions: B<re> and B<im>       

 use Math::Algebra::Symbols complex=>1;

 ($x, $i) = symbols(qw(x i));

 $R = re($i*$x);
 $I = im($i*$x);

 print "$R $I\n";

 # 0 $x

The B<re> and B<im> functions return an expression which represents the
real and imaginary parts of the expression, assuming that symbolic
variables represent real numbers.

=head4 Complex functions: B<dot> and B<cross>       

 use Math::Algebra::Symbols complex=>1;

 $i = symbols(qw(i));

 $c = cross($i+1, $i-1);
 $d = dot  ($i+1, $i-1);

 print "$c $d\n";

 # 2 0

The B<dot> and B<cross> operators are available as functions, either as
exports to the caller's name space, or as methods.

=head4 Complex functions: B<conjugate>, B<modulus> and B<unit>       

 use Math::Algebra::Symbols complex=>1;

 $i = symbols(qw(i));

 $x = unit($i+1);
 $y = modulus($i+1);
 $z = conjugate($i+1);

 print "$x\n$y\n$z\n";

 # $i*sqrt(1/2)+sqrt(1/2)
 # sqrt(2)
 # 1-$i

The B<conjugate>, B<abs> and B<unit> operators are available as
functions: B<conjugate>, B<modulus> and B<unit>, either as exports to
the caller's name space, or as methods. The confusion over the naming of:
the B<abs> operator being the same as the B<modulus> complex function;
arises over the limited set of Perl operator names available for
overloading.


=head2 Methods

=head3 Methods for manipulating Equations             

=head4 Simplifying equations: B<simplify()>

 use Math::Algebra::Symbols;
 
 ($x) = symbols(qw(x));
 
  $y  = (($x**8 - 1)/($x-1))->simplify();  # Simplify method 
  $z +=  ($x**8 - 1)/($x-1);               # Simplify via += 

 print "$y\n$z\n";

 # $x+$x**2+$x**3+$x**4+$x**5+$x**6+$x**7+1
 # $x+$x**2+$x**3+$x**4+$x**5+$x**6+$x**7+1

B<Simplify()> attempts to simplify an expression. There is no general
simplification algorithm: consequently simplifications are carried out
on ad hoc basis. You may not even agree that the proposed simplification
for a given expressions is indeed any simpler than the original. It is
for these reasons that simplification has to be explicitly requested
rather than being performed automagically.

At the moment, simplifications consist of polynomial division: when the
expression consists, in essence, of one polynomial divided by another,
an attempt is made to perform polynomial division, the result is
returned if there is no remainder.

The B<+=> operator may be used to simplify and assign an expression to a
Perl variable. Perl operator overloading precludes the use of B<=> in this
manner. 


=head4 Substituting into equations: B<sub()>

 use Math::Algebra::Symbols;
 
 ($x, $y) = symbols(qw(x y));
 
 $e  = 1+$x+$x**2/2+$x**3/6+$x**4/24+$x**5/120;

 $e2 = $e->sub(x=>$y**2, z=>2);   #1
 $e3 = $e->sub(x=>1);             #2

 print "$e2\n\n$e3\n\n";

 # 1+$y**2+1/2*$y**4+1/6*$y**6+1/24*$y**8+1/120*$y**10

 # 163/60

The B<sub()> function example on line B<#1> demonstrates replacing
variables with expressions. The replacement specified for B<z> has no
effect as B<z> is not present in this equation.

Line B<#2> demonstrates the resulting rational fraction that arises when
all the variables have been replaced by constants. This package does not
convert fractions to decimal expressions in case there is a loss of
accuracy, however:

 $e3 =~ /^(\d+)\/(\d+)$/;
 $result = $1/$2;

or similar will produce approximate results.

At the moment only variables can be replaced by expressions. Mike
Schilli, m@perlmeister.com, has proposed that substitutions for
expressions should also be allowed, as in:

 $x/$y => $z
 

=head4 Solving equations: B<solve()>

 use Math::Algebra::Symbols;

 ($x, $v, $t) = symbols(qw(x v t));

 $z = ($v eq $x / $t)->solve(qw(x in terms of v t)); #1

 print "x=$z\n";

 # x=$v*$t

B<solve()> assumes that the equation on the left hand side is equal to
zero, applies various simplifications, then attempts to rearrange the
equation to obtain an equation for the first variable in the parameter
list assuming that the other terms mentioned in the parameter list are
known constants. There may of course be other unknown free variables in
the equation to be solved: the proposed solution is automatically tested
against the original equation to check that the proposed solution
removes these variables, an error is reported via B<die()> if it does not.

 use Math::Algebra::Symbols;
 use symbols;

 my ($x) = symbols(qw(x));

 my  $p = $x**2-5*$x+6;        # Quadratic polynomial
 my ($a, $b) = @{($p > $x )};  # Solve for x

 print "x=$a,$b\n";            # Roots

 # x=2,3

If there are multiple solutions, (as in the case of polynomials), B<solve()>
returns an array of symbolic expressions containing the solutions.

=head3 Methods for performing Calculus

=head4 Differentiation: B<d()>

 use Math::Algebra::Symbols;

 ($x, $i) = S(qw(x i));

 $z = exp($x)->d->d('x')->d($x)->d();

 print "$z\n";

 # exp($x)

B<d()> differentiates the equation on the left hand side by the named
variable.

The variable to be differentiated by may be explicitly specified,
either as a string or as single symbol; or it may be heuristically
guessed as follows:

If the equation to be differentiated refers to only one symbol, then
that symbol is used. If several symbols are present in the equation, but
only one of B<t>, B<x>, B<y>, B<z> is present, then that variable is
used in honor of Newton, Leibnitz, Cauchy.

=head2 Examples

=head3 Example Expressions

 use Math::Algebra::Symbols;

 ($a, $b, $x, $y, $i) = symbols(qw(a b x y i));

   print $i x 1, "\n";              # Cross product
 # 1

   print $i^1,   "\n";              # Dot product - different vectors
 # 0

   print $i^$i,  "\n";              # Dot product - same vector
 # 1

   print abs $i, "\n";              # Length of unit vector
 # 1

   print ~($a+$b) == ~$a+~$b, "\n"; # Conjugation is distributive
 # 1                                  over addition

   print ~($a*$b) == ~$a*~$b, "\n"; # Conjugation is distributive
 # 1                                  over multiplication

   print ~($a**2) == (~$a)**2,"\n"; # Conjugation is distributive
 # 1                                  over power

   print  abs(!($x+$y*$i))==1,"\n"; # Length of unit vector
 # 1

   print                            # Length of product = product of lengths
         abs($a+$i*$b)*abs($x+$i*$y) ==
        abs(($a+$i*$b)*   ($x+$i*$y)), "\n";
 # 1  


=head3 Example of Equation Solving: the focii of a hyperbola:

 use Math::Algebra::Symbols;
 ($a, $b, $x, $y, $i, $o) = symbols(qw(a b x y i 1));

 print
 "Hyperbola: Constant difference between distances from focii to locus of y=1/x",
 "\n  Assume by symmetry the focii are on ",
 "\n    the line y=x:                     ",  $f1 = $x + $i * $x,
 "\n  and equidistant from the origin:    ",  $f2 = -$f1,
 "\n  Choose a convenient point on y=1/x: ",  $a = $o+$i,
 "\n        and a general point on y=1/x: ",  $b = $y+$i/$y,
 "\n  Difference in distances from focii",
 "\n    From convenient point:            ",  $A = abs($a - $f2) - abs($a - $f1),  
 "\n    From general point:               ",  $B = abs($b - $f2) + abs($b - $f1),
 "\n\n  Solving for x we get:            x=", ($A - $B) > $x,
 "\n                         (should be: sqrt(2))",                        
 "\n  Which is indeed constant, as was to be demonstrated\n";

This example demonstrates the power of symbolic processing by finding the
focii of the curve B<y=1/x>, and incidentally, demonstrating that this curve
is a hyperbola.

=head3 Further Examples

 use Math::Algebra::Symbols;

 $x = symbols(qw(x));

 $x->test();

The B<test()> method performs many tests which are useful in validating this package and as
examples of the capabilities of this package.  These tests may also be run as:

 perl symbols.pm
 

=head1 EXPORT

 use Math::Algebra::Symbols
   symbols=>'S',
   BigInt => 0,
   trig   => 1,
   hyper  => 1,
   complex=> 1;

=over

=item BigInt=>0

The default - use regular perl numbers.

=item BigInt=>1

Use Perl L<Math::BigInt> to represent numbers.  

=item symbols=>'name'

Create a routine with this name in the caller's namespace to construct
new symbols. The default is B<symbols>.

=item trig=>0

The default, do not export trigonometric functions. 

=item trig=>1

Export trigonometric functions: B<tan>, B<sec>, B<csc>, B<cot> to the
caller's namespace. B<sin>, B<cos> are created by default by overloading
the existing Perl B<sin> and B<cos> operators.

=item B<trigonometric>

Alias of B<trig>

=item hyperbolic=>0

The default, do not export hyperbolic functions. 

=item hyper=>1

Export hyperbolic functions: B<sinh>, B<cosh>, B<tanh>, B<sech>,
B<csch>, B<coth> to the caller's namespace.

=item B<hyperbolic>

Alias of B<hyper>

=item complex=>0

The default, do not export complex functions         

=item complex=>1

Export complex functions: B<conjugate>, B<cross>, B<dot>, B<im>,
B<modulus>, B<re>, B<unit> to the caller's namespace.

=back

=head1 PACKAGES

The Symbols packages manipulate a sum of products representation of an
algebraic equation. The B<Symbols> package is the user interface to the
functionality supplied by the B<SymbolsSum> and B<SymbolsTerm> packages.

=head2 Math::Algebra::SymbolsTerm

B<SymbolsTerm> represents a product term. A product term consists of the
number B<1>, optionally multiplied by:

=over

=item Variables

any number of variables raised to integer powers,

=item Coefficient

An integer coefficient optionally divided by a positive integer divisor,
both represented as BigInts if necessary. 

=item Sqrt

The sqrt of of any symbolic expression representable by the B<Symbols>
package, including minus one: represented as B<i>.

=item Reciprocal

The multiplicative inverse of any symbolic expression representable by
the B<Symbols> package: i.e. a B<SymbolsTerm> may be divided by any
symbolic expression representable by the B<Symbols> package.

=item Exp

The number B<e> raised to the power of any symbolic expression
representable by the B<Symbols> package.

=item Log

The logarithm to base B<e> of any symbolic expression representable by
the B<Symbols> package.

=back

Thus B<SymbolsTerm> can represent expressions like:

  2/3*$x**2*$y**-3*exp($i*$pi)*sqrt($z**3) / $x

but not:

  $x + $y

for which package B<SymbolsSum> is required. 


=head2 Math::Algebra::SymbolsSum

B<SymbolsSum> represents a sum of product terms supplied by
B<SymbolsTerm> and thus behaves as a polynomial. Operations such as
equation solving and differentiation are applied at this level.

The main benefit of programming B<SymbolsTerm> and B<SymbolsSum> as two
separate but related packages is Object Oriented Polymorphism. I.e. both
packages need to multiply items together: each package has its own B<multiply> method,
with Perl method lookup selecting the appropriate one as required. 

=head2 Math::Algebra::Symbols

Packaging the user functionality alone and separately in package
B<Symbols> allows the internal functions to be conveniently hidden from
user scripts.


=head1 AUTHOR

Philip R Brenan at B<philiprbrenan@yahoo.com>

=cut



