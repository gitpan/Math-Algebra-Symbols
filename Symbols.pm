#!perl -w
#_ Symbols ______________________________________________________________
# Symbolic algebra.
# Perl License.
# PhilipRBrenan@yahoo.com, 2004.
#________________________________________________________________________

package Math::Algebra::Symbols;
$VERSION = 1.05;

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
# Overload.
#________________________________________________________________________

use overload
 '+'     =>\&add3,
 '-'     =>\&negate3,
 '*'     =>\&multiply3,
 '/'     =>\&divide3,
 '**'    =>\&power3,
 '=='    =>\&equals3,
 '<=>'   =>\&tequals3,
 'sqrt'  =>\&sqrt3,
 'exp'   =>\&exp3,
 'log'   =>\&log3,
 'tan'   =>\&tan3,
 'sin'   =>\&sin3,
 'cos'   =>\&cos3,
 '""'    =>\&print3,
 '^'     =>\&dot3,       # Beware the low priority of this operator
 '~'     =>\&conjugate3,  
 'x'     =>\&cross3,  
 'abs'   =>\&modulus3,  
 '!'     =>\&unit3,  
 fallback=>1;

#_ Symbols ______________________________________________________________
# Operators.
#________________________________________________________________________

sub add3      {$_[0]->add3      ($_[1],$_[2])}
sub negate3   {$_[0]->negate3   ($_[1],$_[2])}
sub multiply3 {$_[0]->multiply3 ($_[1],$_[2])}
sub divide3   {$_[0]->divide3   ($_[1],$_[2])}
sub power3    {$_[0]->power3    ($_[1],$_[2])}
sub equals3   {$_[0]->equals3   ($_[1],$_[2])}
sub tequals3  {$_[0]->tequals3  ($_[1],$_[2])}
sub print3    {$_[0]->print3    ($_[1],$_[2])}
sub sqrt3     {$_[0]->sqrt3     ($_[1],$_[2])}
sub exp3      {$_[0]->exp3      ($_[1],$_[2])}
sub sin3      {$_[0]->sin3      ($_[1],$_[2])}
sub cos3      {$_[0]->cos3      ($_[1],$_[2])}
sub tan3      {$_[0]->tan3      ($_[1],$_[2])}
sub log3      {$_[0]->log3      ($_[1],$_[2])}
sub dot3      {$_[0]->dot3      ($_[1],$_[2])}
sub cross3    {$_[0]->cross3    ($_[1],$_[2])}
sub unit3     {$_[0]->unit3     ($_[1],$_[2])}
sub modulus3  {$_[0]->modulus3  ($_[1],$_[2])}
sub conjugate3{$_[0]->conjugate3($_[1],$_[2])}

#_ Symbols ______________________________________________________________
# Package installed successfully
#________________________________________________________________________

1;

