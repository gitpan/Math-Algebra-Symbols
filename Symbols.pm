#!perl -w
#______________________________________________________________________
# Symbolic algebra.
# Perl License.
# PhilipRBrenan@yahoo.com, 2004.
#:folding=indent:
#______________________________________________________________________

package Math::Algebra::Symbols;
use strict;
use Carp;
use Math::BigInt;

$symbols::VERSION = '1.04';

#______________________________________________________________________
# Overload.
# The operator representations are very convenient, but suffer from two
# major defects:
# Major Defect 1: There are not enough operators
# Major Defect 2: The priority of ^ which I use for dot is far too low.    
#______________________________________________________________________

use overload
 '+'     =>\&add3,
 '-'     =>\&negate3,
 'eq'    =>\&negate3,
 '*'     =>\&multiply3,
 '/'     =>\&divide3,
 '**'    =>\&power3,
 'sqrt'  =>\&sqrt3,
 'exp',  =>\&exp3, 
 'log',  =>\&log3, 
 'sin',  =>\&sin3, 
 'cos',  =>\&cos3, 
 '=='    =>\&equals3,
 '""'    =>\&print3,
 '^'     =>\&dot3,       # Beware the low priority of this operator
 '~'     =>\&conjugate3,  
 'x'     =>\&cross3,  
 'abs'   =>\&modulus3,  
 '!'     =>\&unit3,  
 fallback=>1;

#______________________________________________________________________
# Forward.
#______________________________________________________________________

sub new($);

#______________________________________________________________________
# Big integer version - slower.
#______________________________________________________________________

sub bintBigInt($) {Math::BigInt->new($_[0])}
sub bintBigOne    {Math::BigInt->bone()}
sub bintBigZero   {Math::BigInt->bzero()}

#______________________________________________________________________
# Regular size integer version - faster.
#______________________________________________________________________

sub bint($) {$_[0]}
sub bone()  {1}
sub bzero   {0}

#______________________________________________________________________
# Import - parameters from caller - set up as requested.
#______________________________________________________________________

sub import
 {my %P = (program=>@_);
  my %p; $p{lc()} = $P{$_} for(keys(%P));

#______________________________________________________________________
# Numbers
#______________________________________________________________________

  *bint  = *bintBigInt  if $p{bigint}; # Select integer type
  *bone  = *bintBigOne  if $p{bigint}; # Select integer type
  *bzero = *bintBigZero if $p{bigint}; # Select integer type

#______________________________________________________________________
# New symbol constructor - export to calling package.
#______________________________________________________________________

  my $s = <<'END';
package XXXX;

BEGIN  {delete $XXXX::{NNNN}}

sub NNNN
 {return SSSS::symbols(@_);
 }
END

#______________________________________________________________________
# Complex functions: re, im, dot, cross, conjugate, modulus              
#______________________________________________________________________

  $s .= <<'END' if defined($p{complex});

BEGIN  {delete @XXXX::{qw(conjugate cross dot im modulus re unit)}}

sub conjugate($)  {SSSS::conjugate($_[0])}
sub cross    ($$) {SSSS::cross    ($_[0], $_[1])}
sub dot      ($$) {SSSS::dot      ($_[0], $_[1])}
sub im       ($)  {SSSS::im       ($_[0])}
sub modulus  ($)  {SSSS::modulus  ($_[0])}
sub re       ($)  {SSSS::re       ($_[0])}
sub unit     ($)  {SSSS::unit     ($_[0])}
END

#______________________________________________________________________
# Trigonometric functions: tan, sec, csc, cot              
#______________________________________________________________________

  $s .= <<'END' if defined($p{trig}) or defined($p{trigonometric});

BEGIN  {delete @XXXX::{qw(tan sec csc cot)}}

sub tan($) {SSSS::tan($_[0])}
sub sec($) {SSSS::sec($_[0])}
sub csc($) {SSSS::csc($_[0])}
sub cot($) {SSSS::cot($_[0])}
END

#______________________________________________________________________
# Hyperbolic functions: sinh, cosh, tanh, sech, csch, coth              
#______________________________________________________________________

  $s .= <<'END' if defined($p{hyper}) or defined($p{hyperbolic});

BEGIN  {delete @XXXX::{qw(sinh cosh tanh sech csch coth)}}

sub sinh($) {SSSS::sinh($_[0])}
sub cosh($) {SSSS::cosh($_[0])}
sub tanh($) {SSSS::tanh($_[0])}
sub sech($) {SSSS::sech($_[0])}
sub csch($) {SSSS::csch($_[0])}
sub coth($) {SSSS::coth($_[0])}
END

#______________________________________________________________________
# Export to calling package.
#______________________________________________________________________

  my $name   = 'symbols';
     $name   = $p{symbols} if defined($p{symbols});
  my ($main) = caller();
  my $pack   = ref(bless({}));

  $s=~ s/XXXX/$main/g;
  $s=~ s/NNNN/$name/g;
  $s=~ s/SSSS/$pack/g;
  eval($s);

#______________________________________________________________________
# Check options supplied by user
#______________________________________________________________________

  delete @p{qw(
bigint symbols program trig trigonometric hyper hyperbolic complex
)};

  croak "Unknown option(s): ". join(' ', keys(%p))."\n\n". <<'END' if keys(%p);

Valid options are:

  BigInt =>0      The default - use regular perl numbers.
  BigInt =>1      Use Perl BigInt to represent numbers.  


  symbols=>'name' Create a routine with this name in the callers
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

#______________________________________________________________________
# Create a new symbol                              
#______________________________________________________________________

sub symbols
 {return new(shift()) if scalar(@_) == 1;
  my @A = ();
  push @A, new($_) for(@_);
  @A; 
 }

#______________________________________________________________________
# New symbolic term.
#______________________________________________________________________

sub new($)
 {my $s = $_[0];

#______________________________________________________________________
# From array of terms.
#______________________________________________________________________

  if (ref $s eq 'ARRAY' or ref $s eq ref bless {})
   {my @E;
    push @E, @{new($_)} for(@$s);
    return bless \@E;
   }

#______________________________________________________________________
# From a string.
#______________________________________________________________________

  if (!ref($s) or ref($s) eq 'Math::BigInt')
   {my $a = "$s";
    my @T;

    defined($a) or croak "Cannot parse undefined string"; 

    for (;$a ne '' and $a =~ /^\s*([+-])?\s*(\d+)?(?:\/(\d+))?(i)?(?:\*)?(.*)$/;)
     {my $c  = bone(); 
         $c  = bint(-1) if $1 and $1 eq '-';
         $c *= bint($2) if defined($2);
      my $d  = bone();
         $d  = bint($3) if $3;
      my $i = 0;
         $i = 1 if $4;
      my $r = {c=>$c, d=>$d, i=>$i};

      my $b = $5;

      for (;$b =~ /^([a-zA-Z]+)(\*|\d+)?(.*)$/;)
       {my $v = $1;
        my $p = 1;
        $p = $2 if $2 and $2 ne '*';
        $b = $3;
        $r->{v}{$v}  = 0 unless $r->{v}{$v};
        $r->{v}{$v} += $p;
       }

      croak "Cannot parse: $a" if $a eq $b;
      $a = $b;

      push @T, $r;
     }

    return new(\@T); 
   }

#______________________________________________________________________
# From a single term supplied in a hash
#______________________________________________________________________

  my $t = {%$s};
  for my $e(qw(sqrt divide exp log))
   {$t->{$e} = new($s->{$e}) if defined($s->{$e});
   }
  $t->{v} = {%{$s->{v}}} if defined($s->{v});
  $s = $t;

#______________________________________________________________________
# From term: Assume zero if coefficient not set.
#______________________________________________________________________

  return bless [{c=>bint(0)}] if !exists $s->{c} or $s->{c} == 0 or
    (defined($s->{log}) and isOne($s->{log}));

#______________________________________________________________________
# Reduce coefficent and divisor by common factor.
#______________________________________________________________________

  if (my $d = $s->{d})
   {if ($d != 1)
     {my $g = gcd($s->{c}, $d);
      $s->{c} /= $g;
      $s->{d} /= $g;
     }
   }

#______________________________________________________________________
# Remove divisor if possible.  
#______________________________________________________________________

  if (my $d = $s->{d})
   {if ($d < 0)
     {$s->{c} *= -1;
      $s->{d} *= -1;
     }
    delete $s->{d} if $d == 1;
   }

#______________________________________________________________________
# Remove or simplify i if possible.                       
#______________________________________________________________________

  delete $s->{i} if defined $s->{i} and $s->{i} == 0;

#______________________________________________________________________
# Remove or simplify sqrt, exp, log if possible.                       
#______________________________________________________________________

  simplifySqrt($s) if defined $s->{sqrt};
  simplifyExp ($s) if defined($s->{exp});
  simplifyLog ($s) if defined($s->{log});

#______________________________________________________________________
# Remove or simplify 'divide by' by eliminating common fields, factors.
#______________________________________________________________________

  if (defined($s->{divide}))
   {my $d = $s->{divide};
    removeCommonCD    ($s, $d);
    removeCommonI     ($s, $d);
    removeCommonField ($s, $d);
    removeCommonFactor($s, $d);
    if (my $i = invert($d))
     {my $t = bless[$s]; 
      delete $s->{divide};     
      $s = multiply($t, $i);
      $s = $$s[0]; 
     }
   }

#______________________________________________________________________
# Result - clean up.
#______________________________________________________________________

  delete $s->{i}    unless defined $s->{i} and $s->{i} != 0;
  delete $s->{d}    unless defined $s->{d} and $s->{d} != 1;

  for my $e(qw(sqrt divide exp log))
   {delete $s->{$e} if defined $s->{$e} and scalar(@{$s->{$e}}) == 0;
    delete $s->{$e} unless defined $s->{$e};
   }

  if (defined($s->{v}))
   {for my $v(keys(%{$s->{v}}))
     {delete $s->{v}{$v} if $s->{v}{$v} == 0;
     }
    delete $s->{v}  if scalar(keys(%{$s->{v}})) == 0;
   } 

  croak "Zero divisor not allowed" if $s->{d} and $s->{d} == 0;

  bless [$s];
 }

#______________________________________________________________________
# Get component values or supply defaults if not present.
#______________________________________________________________________

sub get($)
 {my $e = $_[0];

  return ($e->{c} || bzero(),  $e->{i} || 0,  $e->{d} || bone(),
          $e->{sqrt}, $e->{divide}, $e->{exp}, $e->{log});
 }

#______________________________________________________________________
# Get variables and their associated powers from a term.
#______________________________________________________________________

sub getVP($)
 {my $e = $_[0];
  return () unless exists $e->{v};
  my @v = (); push @v, [$_, $e->{v}{$_}] for(keys(%{$e->{v}}));
  @v;
 }

#______________________________________________________________________
# Get variables and their associated powers from a term - sorted by name.
#______________________________________________________________________

sub getVPSort($)
 {my $e = $_[0];
  return () unless exists $e->{v};
  my @v = (); push @v, [$_, $e->{v}{$_}] for(sort(keys(%{$e->{v}})));
  @v;
 }

#______________________________________________________________________
# Get variable names from an expression - go deep.
#______________________________________________________________________

sub getVE($);
sub getVE($)
 {my %v;
  for my $t(@{$_[0]}) 
   {if (defined($t->{v}))
     {$v{$_} = 1 for(keys(%{$t->{v}}));
     }
    for my $s(qw(sqrt divide exp log))
     {%v = (%v, %{getVE($t->{$s})}) if exists($t->{$s});
     }
   }
  \%v;
 }

#______________________________________________________________________
# Check whether an expression is not zero.
#______________________________________________________________________

sub nonZero($)
 {my $A = $_[0];
  for my $a(@$A)
   {return 1 if defined($a->{c}) and $a->{c} != 0;
   }
  0;
 }

#______________________________________________________________________
# Check whether an expression is one.
#______________________________________________________________________

sub isOne($)
 {my $A = $_[0];
  return 0 unless scalar(@$A) == 1;

  for my $a(@$A)
   {return 0 unless defined($a->{c}) and $a->{c} == 1;
    return 0 unless scalar(keys(%$a)) == 1;
   }
  1;
 }

#______________________________________________________________________
# Factor a number.
#______________________________________________________________________

sub factorize($)
 {my @primes = qw(
  2  3   5   7   11  13  17  19  23  29  31  37  41  43  47  53  59  61
 67 71  73  79   83  89  97 101 103 107 109 113 127 131 137 139 149 151
157 163 167 173 179 181 191 193 197 199 211 223 227 229 233 239 241 251
257 263 269 271 277 281 283 293 307 311 313 317 331 337 347 349 353 359
367 373 379 383 389 397 401 409 419 421 431 433 439 443 449 457 461 463
467 479 487 491 499 503 509 521 523 541 547 557 563 569 571 577 587 593
599 601 607 613 617 619 631 641 643 647 653 659 661 673 677 683 691 701
709 719 727 733 739 743 751 757 761 769 773 787 797 809 811 821 823 827
829 839 853 857 859 863 877 881 883 887 907 911 919 929 937 941 947 953
967 971 977 983 991 997);

  my $n = bint($_[0]);
  my $f;

  for my $p(@primes)
   {for(;$n % $p == 0;)
     {$f->{$p}++;
      $n /= $p;
     }
    last unless $n > $p;
   }
  $f;
 };

#______________________________________________________________________
# Greatest Common Divisor.
#______________________________________________________________________

sub gcd($$)
 {my $x = abs($_[0]);
  my $y = abs($_[1]);

  return 1 if $x == 1 or $y == 1; 

  my ($a, $b) = ($x, $y); $a = $y, $b = $x if $y < $a;
  
  for(my $r;;)
   {$r = $b % $a;
    return $a if $r == 0;
    ($a, $b) = ($r, $a);
   }
 };

#______________________________________________________________________
# Least common multiple.  
#______________________________________________________________________

sub lcm($$)
 {my $x = abs($_[0]);
  my $y = abs($_[1]);
  return $x*$y if $x == 1 or $y == 1; 
  $x*$y / gcd($x, $y);
 };

#______________________________________________________________________
# Print.
#______________________________________________________________________

sub print($)
 {my $a = $_[0]; # Expression

#______________________________________________________________________
# Print expression
#______________________________________________________________________

  if (ref($a) eq ref bless {})
   {my @s = ();
    push @s, &print($_) for(@$a);
    my $s = join('+', @s);
    $s =~ s/\+\-/\-/g;
    $s = '0' if $s eq '';
    return $s;
   }

#______________________________________________________________________
# Print term
#______________________________________________________________________
  
  return '' unless nonZero([$a]);

# Variables

  my @v = ();
  for my $vp(getVPSort($a))
   {my ($v, $p) = @$vp;
    next if $p == 0;
    push @v, '*', '$'.$v;
    push @v, "**$p" if $p != 1;
   }

# Other components

  my ($c, $i, $d) = get($a);

  my @s = ();
  push @s, '+', abs($c) if     $c >= 0;
  push @s, '-', abs($c) unless $c >= 0;
  push @s, '/', $d      unless $d == 1;
  push @s, '*', '$i'    unless $i == 0;
  push @s, '*', 'sqrt', '(', &print($a->{sqrt}),   ')' if $a->{sqrt};
  push @s, '*', 'exp',  '(', &print($a->{exp}),    ')' if $a->{exp};
  push @s, '*', 'log',  '(', &print($a->{log}),    ')' if $a->{log};
  push @s, '/',         '(', &print($a->{divide}), ')' if $a->{divide};
  push @s, @v;

# Clean up

  shift @s if $s[0] =~ m#[\+]#;

# Join terms up and return
     
  my $r = join('', @s);
  $r =~ s/(?<!\*\*\-)1\*//g;                                 # remove: 1*
  $r =~ s/\*(\$[a-zA-Z]+)\*\*\-1(?!\d)/\/$1/g;               # change:  *$y**-1 to    /$y
  $r =~ s/\*(\$[a-zA-Z]+)\*\*\-(\d+)/\/$1**$2/g;             # change:  *$y**-n to    /$y**n
  $r =~ s/([\+\-])(\$[a-zA-Z]+)\*\*\-1(?!\d)/1\/$1/g;        # change: +-$y**-1 to +-1/$y
  $r =~ s/([\+\-])(\$[a-zA-Z]+)\*\*\-(\d+)/${1}1\/$2**$3/g;  # change: +-$y**-n to +-1/$y**n
  return $r;        
 }

#______________________________________________________________________
# Print operator.
#______________________________________________________________________

sub print3
 {&print($_[0]);
 }

#______________________________________________________________________
# Add a term.  Return undef if the terms cannot be added.
#______________________________________________________________________

sub addTerm($$)
 {my ($a, $b) = @_;

#______________________________________________________________________
# ci
#______________________________________________________________________

  my ($ca, $ia, $da) = get($a);
  my ($cb, $ib, $db) = get($b);

  return undef unless $ia == $ib; 

#______________________________________________________________________
# v
#______________________________________________________________________

  my %v = ();                      
     %v = (%v, %{$a->{v}}) if $a->{v};
     %v = (%v, %{$b->{v}}) if $b->{v};

  for my $v(keys(%v))
   {my $A = $a->{v}{$v} || 0;
    my $B = $b->{v}{$v} || 0;
    
    return undef unless $A == $B;
   }

#______________________________________________________________________
# sqrt, divide, exp
#______________________________________________________________________

  for my $e(qw(sqrt divide exp))
   {my ($s, $t) = ($a->{$e}, $b->{$e});
    return undef if defined($s) xor defined($t);
    return undef if defined($s) and defined($t) and !equals($s, $t);
   } 

#______________________________________________________________________
# Log: l=0 equal logs or no logs, l=1 same coefficients, different logs
#______________________________________________________________________

  my $l = 0;
   {my ($s, $t) = ($a->{log}, $b->{log});
    return undef if defined($s) xor defined($t);
    return undef if defined($s) and defined($t) and
     !(equals($s, $t) or $l = ($ca == $cb and $da == $db));
   } 

#______________________________________________________________________
# Same variables, sqrt, exp, divide. Possible variation in log
#______________________________________________________________________

  my ($c, $d) = ($ca, $da);
  unless ($l)
   {$d = lcm($da, $db);
    $c = $ca * ($d/$da) + $cb * ($d/$db);
    return {c=>bint(0)} if $c == 0;
   
    my $g = gcd($c, $d); $c /= $g; $d /= $g;
   }
#______________________________________________________________________
# Construct result                                            
#______________________________________________________________________

  my $r   = {};
  $r->{c} = $c;
  $r->{i} = $ia;
  $r->{d} = $d;
  $r->{v} = $a->{v};
  for my $e(qw(sqrt divide exp log))
   {$r->{$e} = $a->{$e} if defined($a->{$e});
   }

#______________________________________________________________________
# Same coefficents, different logs: A*log(a)+A*log(b) == A*log(a*b)
#______________________________________________________________________

  $r->{log} = multiply($a->{log}, $b->{log}) if $l; 

#______________________________________________________________________
# Result
#______________________________________________________________________
  
  $r;                                            
 }

#______________________________________________________________________
# All expressions.
#______________________________________________________________________

sub getAllExpressions($)
 {my $e = [];
  for my $a(@{$_[0]})                      
   {if (ref($a) eq ref bless {})
     {push @$e, $_ for (@$a);                      
     }
    else
     {push @$e, $a;                      
     }
   }
  $e;
 }

#______________________________________________________________________
# Signature for a term - used to speed up add.
#______________________________________________________________________

sub signature($)
 {my $t = $_[0]; # Term
  return '' unless exists $t->{v};

  my $s = ''; $s .= $_.$t->{v}{$_} for (sort(keys(%{$t->{v}})));
  $s;
 }

#______________________________________________________________________
# Add.
#______________________________________________________________________

sub add(@)
 {my %P;

#______________________________________________________________________
# Partition terms by signature.
#______________________________________________________________________
    
  push @{$P{signature($_)}}, $_ for (@{getAllExpressions(\@_)});
 
#______________________________________________________________________
# Collect like terms by trying to add every possible combination within
# each partition induced by the signature.
#______________________________________________________________________
    
  my @T = ();
  for     my $p(keys(%P))
   {my @P = @{$P{$p}};
    my $n = scalar(@P)-1;

    for   my $s(0..$n)  
     {next   unless defined($P[$s]);

      for my $t(0..$n)  
       {next if $s == $t or !defined($P[$t]);

        if (my $r = addTerm($P[$s], $P[$t]))  
         {delete $P[$t];
          $P[$s] = $r;
         }
       }
     }
    for my $p(@P)
     {push @T, $p if defined($p) and $p->{c} != 0;
     }
   }

#______________________________________________________________________
# Sort terms into degree order.  This feature is still unstable.
# Its desireable for the terms to come out in the same order each time
# as it makes reading and comparison much easier.  Choosing a quick and
# reliable ordering is difficult.
# PolynomialDivision() relies on this feature as it needs polynomials
# in degree order.
# Performance is acceptable as we are not in addTerm().
#______________________________________________________________________

  my @t = ();
  for my $t(@T)
   {my $k  = '';
    my $k1 = 0; 
    for my $vp(getVPSort($t))
     {my ($v, $p) = @$vp;
      $k  .= $v; # x (abs($p)+1);
      $k1 += abs($p);         
     }
    push @t, [$t, sprintf("%010d%s", $k1, $k)];
   }

  my @s = sort {$a->[1] cmp $b->[1]} @t;
  my @r = ();
  for my $t(@s)
   {push @r, $t->[0];
   }  
  new(\@r);
 }

#______________________________________________________________________
# Add operator.
#______________________________________________________________________

sub add3
 {my ($a, $b) = @_;
  add($a, new($b));
 }

#______________________________________________________________________
# Negate.
#______________________________________________________________________

sub negate($)
 {my $a = $_[0];
  my $b = new($a);
  $_->{c} = -$_->{c} for(@$b);
  $b;
 }

#______________________________________________________________________
# Negate operator.
#______________________________________________________________________

sub negate3
 {my ($a, $b, $c) = @_;
  my $r;
  $b = new($b) if defined($b) and !ref($b);
  if (ref($b))
   {$r = add($b, negate($a)) if     $c;
    $r = add($a, negate($b)) unless $c;
   }   
  else
   {$r = negate($a);
   } 
  return $r;
 }

#______________________________________________________________________
# Multiply terms. Creates a new term representing the product of two
# terms.
#______________________________________________________________________

sub multiplyTerm($$)
 {my ($a, $b) = @_;
  my ($ca, $ia, $da, $sa, $va, $ea, $la) = get($a);
  my ($cb, $ib, $db, $sb, $vb, $eb, $lb) = get($b);

#______________________________________________________________________
# c
#______________________________________________________________________

  my $c = $ca * $cb;
  my $d = $da * $db;
  my $g = gcd($c, $d);
     $c /= $g; $d /= $g; 

#______________________________________________________________________
# i
#______________________________________________________________________

  my $i = ($ia + $ib) % 4;
  ($c *= -1, $i -= 2) if $i == 2 or $i == 3;

#______________________________________________________________________
# v
#______________________________________________________________________

  my %v = ();                      
     %v = (%v, %{$a->{v}}) if $a->{v};
     %v = (%v, %{$b->{v}}) if $b->{v};
  my $w;

  for my $v(sort(keys(%v)))
   {my $av = $a->{v}{$v} || 0;
    my $bv = $b->{v}{$v} || 0;
    my $n = $av + $bv;
    $w->{$v} = $n unless $n == 0;
   }

#______________________________________________________________________
# sqrt divide exp log
#______________________________________________________________________

  my ($extra, $s, $e, $v, $l);

#______________________________________________________________________
# Sqrt: sqrt(a)*sqrt(b) = sqrt(a*b)
#______________________________________________________________________

  $s = $sa if defined($sa); 
  $s = $sb if defined($sb);
  if (defined($sa) and defined($sb))
   {if (equals($sa, $sb))
     {$extra = new($sa); # Equal square roots - move a copy out
      $s = undef;
     }
    else
     {$s = $sa * $sb;
     }
   }

#______________________________________________________________________
# Divide: 1/a*1/b = 1/(a*b)
#______________________________________________________________________

  $v = $va if defined($va); 
  $v = $vb if defined($vb);
  $v = $va * $vb if defined($va) and defined($vb);

#______________________________________________________________________
# Exp: exp(a)*exp(b) = exp(a+b)
#______________________________________________________________________

  $e = $ea if defined($ea); 
  $e = $eb if defined($eb);
  $e = $ea + $eb if defined($ea) and defined($eb);
  $e = undef if defined($e) and !nonZero($e);

#______________________________________________________________________
# Log: log(a)*log(b) = exp(log(log(a))+log(log(b)))
# This avoids introduction of new fields
#______________________________________________________________________

  if (defined($la) and defined($lb)) 
   {my $l  = log(log($la))+log(log($b));
       $l += $e if defined($e);
    $e = $l;
    $l = undef;
   }
  else
   {$l = $la if defined($la); 
    $l = $lb if defined($lb);
   }
  
#______________________________________________________________________
# Result
#______________________________________________________________________
  
  my $r        = {};
  $r->{c}      = $c;
  $r->{d}      = $d;
  $r->{i}      = $i;
  $r->{v}      = $w;
  $r->{sqrt}   = $s if defined($s);
  $r->{divide} = $v if defined($v);
  $r->{exp}    = $e if defined($e);
  $r->{log}    = $l if defined($l);

  return new($r)*$extra if defined($extra); # From equal square roots
  return bless [$r];
 }

#______________________________________________________________________
# Multiply.
#______________________________________________________________________

sub multiply($$)
 {my ($A, $B) = @_;

  return $A if !nonZero($A) or isOne($B);
  return $B if !nonZero($B) or isOne($A);

  my @T = ();

# Optimization: eliminate divisor equal to multipier

  for my $a(@$A)
   {my $d = $a->{divide};
    if (defined($d) and equals($d, $B))
     {my %r = (%$a); 
      delete $r{divide};
      push @T, \%r;
     }

# Otherwise: Multiply term by term

    else
     {for my $b(@$B) 
       {push @T, @{multiplyTerm($a, $b)};
       }
     }
   }
  add(bless \@T);
 }

#______________________________________________________________________
# Multiply operator.
#______________________________________________________________________

sub multiply3
 {my ($a, $b) = @_;
  $b = new($b) unless ref($b);
  multiply($a, $b);
 }

#______________________________________________________________________
# Invert - take the reciprocal of a single term.
#______________________________________________________________________

sub invert($);
sub invert($)
 {my $A = $_[0];

  return undef unless scalar(@$A) == 1;  

  for my $a(@$A)
   {my ($c, $i, $d, $s, $v, $e, $l) = get($a);

# i
    $c = -$c if $i;

# Sqrt

    if (defined($s))
     {my $S = invert($s);
      return undef unless $S;
      $s = $S;
     } 

# Exp

    $e = -$e if defined($e);

# Log

    $l = 1/$l if defined($l);

# Variable powers
    
    my $w; $w->{$_} = -$a->{v}{$_} for(sort(keys(%{$a->{v}})));

# Result

    my $r = new {c=>$d, d=>$c, i=>$i, sqrt=>$s, v=>$w, exp=>$e, log=>$l};
    return $r unless $v;
    return $r * $v;  # Multiply by 'divide by'
   }
 }

#______________________________________________________________________
# The term A is about to be divided by expression B, both A and B may
# have 'divide'  fields. Multiply A and B (top and bottom) by the 'divide'
# fields of  B in order to remove the 'divide' fields from B, thus
# converting a three level fraction to a conventional two level fraction.
#______________________________________________________________________

sub multiplyOutDivides($$)
 {my $A = new($_[0]); # The term being divided
  my $B = new($_[1]); # The dividing term with possibly 'divide' fields

  L: for(;;)
   {for my $b(@$B)
     {my $d = $b->{divide};
      if (defined($d))
       {$A *= $d;
        $B *= $d;
        next L;
       }
     }
    last L;
   }
  return ($A, $B);
 }

#______________________________________________________________________
# Divide.
#______________________________________________________________________

sub divide($$)
 {my ($A, $B) = (new($_[0]), new($_[1]));

  removeCommonCD    ($A, $B); # Common coefficients and divisors
  removeCommonI     ($A, $B); # Common i                          
  removeCommonField ($A, $B); # Common fields         
  removeCommonFactor($A, $B); # Common variable powers

  ($A, $B) = multiplyOutDivides($A, $B);

  nonZero($B) or croak "Cannot divide by zero";

#______________________________________________________________________
# Simple divide - divide by single invertible term
#______________________________________________________________________

  my $i = invert($B);
  return multiply($A, $i) if $i;

#______________________________________________________________________
# Difficult divide
#______________________________________________________________________

  my ($D, $R) = polynomialDivision($A, $B);

  my @E = (@$D);         # Divide result
  for my $r(@$R)         # Divide remainder 
   {my $d = $r->{divide};

    $r->{divide} = multiply($d, $B) if     $d;
    $r->{divide} = new($B)          unless $d;  
    push @E, $r;
   }
  add(bless \@E);
 }

#______________________________________________________________________
# Divide operator.
#______________________________________________________________________

sub divide3
 {my ($a, $b, $c) = @_;
  my $d = $b;
     $d = new($d) unless ref($d) eq ref bless {};
  my $r;
     $r = divide($d, $a) if     $c;
     $r = divide($a, $d) unless $c;
  $r;
 }

#______________________________________________________________________
# Power.
#______________________________________________________________________

sub power($$)
 {my ($e, $p) = @_;
  my $r = new($e);

# Is the power a constant?

  L: for(;;)
   {last unless ref($p) eq ref(bless {});
    last unless scalar(@$p) == 1;
    for my $f(qw(sqrt divide exp log))
     {last L if defined($$p[0]->{$f});
     }
    last if defined($$p[0]->{v}) and scalar(keys(%{$$p[0]->{v}}));
    my ($C, $I, $D) = get($$p[0]);
    last unless $I == 0; 
    last unless $D == 1;
    $p = $C;
    last;
   }

# By a constant:  use successive squares to construct desired power

  if (!ref($p) or ref($p) eq 'Math::BigInt')
   {my @B = ([1, $r]);
    my $b;
    for ($b = 2; $b <= $p; $b *= 2)
     {$r *= $r;
      push @B, [$b, $r];
     }
    pop @B; $b = $b/2; $p -= $b;
    for (; $p > 0 ;)
     {my ($B, $R) = @{pop @B};
      if ($B <= $p)
       {$r *= $R;
        $p -= $B;
       }
     }
    return $r;
   }   

# By expression: use  a**p == exp(p*log(a))

  else   
   {return exp($p*log($r));
   }
 }

#______________________________________________________________________
# Power operator.
#______________________________________________________________________

sub power3
 {my ($a, $b, $c) = @_;
  my $d = $b;
     $d = new($d) unless ref($d) eq ref bless {};
  my $r;
     $r = power($d, $a) if     $c;
     $r = power($a, $d) unless $c;
  $r;
# power($a, $b);
 }

#______________________________________________________________________
# Equals.
#______________________________________________________________________

sub equals($$)
 {my ($a, $b) = @_;
  !nonZero(add($a, negate($b)));
 }

#______________________________________________________________________
# Equals operator.
#______________________________________________________________________

sub equals3
 {my ($a, $b) = @_;
  !nonZero(isZero(add($a, negate($b))));
 }

#______________________________________________________________________
# Square root operator.
#______________________________________________________________________

sub sqrt3
 {new({c=>1, sqrt=>new($_[0])});
 }

#______________________________________________________________________
# Exponential operator.
#______________________________________________________________________

sub exp3
 {new({c=>1, exp=>new($_[0])});
 }

#______________________________________________________________________
# Log operator.
#______________________________________________________________________

sub log3
 {new({c=>1, log=>new($_[0])});
 }

#______________________________________________________________________
# Sin operator.
#______________________________________________________________________

sub sin3
 {my $a = new($_[0]);
  my $i = new('i');
  new({c=>1, i=>1, d=>2, exp=>(- $i*$a)}) -
  new({c=>1, i=>1, d=>2, exp=>(  $i*$a)});
 }

#______________________________________________________________________
# Cos operator.
#______________________________________________________________________

sub cos3
 {my $a = new($_[0]);
  my $i = new('i');
  new({c=>1, d=>2, exp=>(  $i*$a)}) +
  new({c=>1, d=>2, exp=>(- $i*$a)});
 }

#______________________________________________________________________
# Tan, sec, csc, cot functions
#______________________________________________________________________

sub tan($) {sin($_[0])/cos($_[0])}
sub sec($) {         1/cos($_[0])}
sub csc($) {         1/sin($_[0])}
sub cot($) {cos($_[0])/sin($_[0])}

#______________________________________________________________________
# Hyperbolic functions
#______________________________________________________________________

sub sinh($) {(exp($_[0])-exp(-$_[0]))/2}
sub cosh($) {(exp($_[0])+exp(-$_[0]))/2}
sub tanh($) {sinh($_[0])/cosh($_[0])}
sub sech($) {          1/cosh($_[0])}
sub csch($) {          1/sinh($_[0])}
sub coth($) {cosh($_[0])/sinh($_[0])}

#______________________________________________________________________
# Real part.
#______________________________________________________________________

sub re($)
 {my $A = $_[0];
  $A = new($A) unless ref($A);
  my @r;
  for my $a(@$A)
   {push @r, $a if !defined($a->{i}) or  $a->{i} == 0;
   }
  bless \@r;
 }

#______________________________________________________________________
# Imaginary part.
#______________________________________________________________________

sub im($)
 {my $A = $_[0];
  $A = new($A) unless ref($A);
  my @i;
  for my $a(@$A)
   {next unless defined($a->{i});
    my $b = {%$a};
    delete $b->{i};
    push @i, $b;
   }
  bless \@i;
 }

#______________________________________________________________________
# Modulus.
#______________________________________________________________________

sub modulus($)
 {my $a = $_[0];
  sqrt((re($a))**2+((im($a))**2));
 }

#______________________________________________________________________
# Modulus operator.
#______________________________________________________________________

sub modulus3
 {modulus($_[0]);
 }

#______________________________________________________________________
# Conjugate.
#______________________________________________________________________

sub conjugate($)
 {my $a = $_[0];
  re($a) - im($a) * new('i');
 }

#______________________________________________________________________
# Conjugate.
#______________________________________________________________________

sub conjugate3
 {conjugate($_[0]);
 }

#______________________________________________________________________
# Simplify square root.
# The simplification is performed in situ.
#______________________________________________________________________

sub simplifySqrt($)
 {my $t = $_[0];

#______________________________________________________________________
# cdis
#______________________________________________________________________

  my ($c, $i, $d, $s) = get($t);
  return if !defined($s);

#______________________________________________________________________
# Set the lowest power of each variable in sqrt terms to be 0 or 1
#______________________________________________________________________

  my %v = ();                          
  for my $a(@$s)                      
   {for my $vp(getVP($a))
     {my ($v, $p) = @$vp;
      $v{$v} = 0  if !defined($v{$v});
      $v{$v} = $p if $p < $v{$v} ;
     }
   }

  for my $v(keys(%v))
   {my $p = $v{$v};
    next if $p == 0 or $p == 1;
    $p = int( $v{$v}    / 2) if $p > 0;
    $p = int(($v{$v}-1) / 2) if $p < 0;
    $t->{v}{$v} += $p;
    for my $a(@$s)                      
     {$a->{v}{$v} -= 2*$p;
     }
   }

#______________________________________________________________________
# No further simplification unless single term sqrt
#______________________________________________________________________

  return if scalar(@$s) > 1;

#______________________________________________________________________
# Array of zero entries means the square root is zero
#______________________________________________________________________

  if (scalar(@$s) == 0)
   {delete $t->{sqrt};
    $t->{c} = 0;
    return; 
   }

#______________________________________________________________________
# cdis for square root
#______________________________________________________________________

  my $r = $s->[0];
  my ($c2, $i2, $d2, $s2) = get($r);

#______________________________________________________________________
# Remove largest square root
#______________________________________________________________________

  my $lsr = sub ($)
   {my $n = shift();
    my ($a, $b) = (1, $n);
    my $f = factorize($n);
  
    for my $v(keys(%$f))
     {my $p = $f->{$v};
      if ($p % 2 == 0)
       {$a *= $v**($p/2);
        $b /= $v** $p;
       }
     }
    return ($a, $b);
   };

#______________________________________________________________________
# Remove duplicate factors from square root
#______________________________________________________________________

   my ($a, $b) = &$lsr($c2);
   $t->{c} *= $a; $r->{c} = $b;


   if ($d2 != 1)
    {my ($a, $b) = &$lsr($d2);

     $t->{d} = 1 unless $t->{d};
     $t->{d} *= $a;
     $r->{d}  = $b;
     delete $r->{d} if $b == 1; 
    }

#______________________________________________________________________
# Remove duplicate powers from square root
#______________________________________________________________________

  for my $vp(getVP($r))
   {my ($v, $p) = @$vp;
    my $q = $p - $p % 2;
    $r->{v}{$v} -= $q;
    $t->{v}{$v} += $q/2;
   }

#______________________________________________________________________
# Remove zero powers from square root and container
#______________________________________________________________________

  for my $o(($r, $t))
   {for my $vp(getVP($o))
     {my ($v, $p) = @$vp;
      delete $o->{v}{$v} if $p == 0;
     }
    delete $o->{v}  if scalar(keys(%{$o->{v}})) == 0;
   }

#______________________________________________________________________
# Remove sign from square root
#______________________________________________________________________

  if ($r->{c} < 0)
   {$r->{c}  = abs($r->{c});
    $t->{i} += 1;
   } 

#______________________________________________________________________
# Remove sqrt if 1
#______________________________________________________________________

  delete $t->{sqrt} if isOne($s);
 };

#______________________________________________________________________
# Simplify a single term that contains Exp:  exp(log(a)) = a
# The simplification is performed in situ.
#______________________________________________________________________

sub simplifyExp($)
 {my $t = $_[0];

  my ($c, $i, $d, $s, $D, $e, $l)          = get($t);
  return if !defined($e);

#______________________________________________________________________
# Complex case: exp contains terms of the form: i*n*pi/2: 
#______________________________________________________________________

   {my @r;
    for my $E(@$e)
     {my ($ec, $ei, $ed, $es, $eD, $ee, $el) = get($E);
      push @r, $E;
      next unless $ei == 1;
      next unless       defined($E->{v});
      next unless scalar(keys(%{$E->{v}}))  == 1;
      next unless       defined($E->{v}{pi});
      next unless               $E->{v}{pi} == 1; 
      next unless $ed == 1 or $ed == 2;
                       
      my ($a, $b) = (1, 0);
      if ($ed == 1)
       {$a = -1 if $ec % 2 == 1;
       } 
      else 
       {my $r = $ec % 4;
        ($a, $b) = ( 1, 1) if $r == 1;
        ($a, $b) = (-1, 0) if $r == 2;
        ($a, $b) = (-1, 1) if $r == 3;
       }
      $a = -$a         if     $i+$b == 2;  # ii = -1
      $t->{c} = $a*$c;
      $t->{i} = 0      unless $i+$b == 1;  # Even i
      $t->{i} = 1      if     $i+$b == 1;  # Odd i
      pop @r; 
     }
    $t->{exp} = bless \@r unless scalar(@r) == scalar(@$e);
    delete $t->{exp}      if     scalar(@r) == 0;
   }

#______________________________________________________________________
# Simple case: exp(0): remove exp field and return
#______________________________________________________________________

  unless(nonZero($e))   
   {delete $t->{exp};
    return $t;
   }  

#______________________________________________________________________
# Otherwise simplify exp(log(single-term))
#______________________________________________________________________

  return if scalar(@$e) != 1;
  return if defined($$e[0]->{v});
  my ($ec, $ei, $ed, $es, $eD, $ee, $el) = get($$e[0]);
  return if defined($es) or defined($eD) or defined($ee);

#______________________________________________________________________
# Otherwise check for log 
#______________________________________________________________________

  return unless $ec == 1 and $ei == 0 and $ed == 1;
  return unless defined($el);

  return if scalar(@$el) != 1;

  delete $t->{exp};
  my $r = multiplyTerm($t, $$el[0]);
 
  %$t = %{$$r[0]};
 }

#______________________________________________________________________
# Simplify a single term that contains Log:  log(exp(a)) = a
# The simplification is performed in situ.
#______________________________________________________________________

sub simplifyLog($)
 {my $t = $_[0];

  my ($c, $i, $d, $s, $D, $e, $l)        = get($t);
  return if !defined($l) or scalar(@$l) != 1;
  return if defined($$l[0]->{v});

#______________________________________________________________________
# Simple case: log(1): set term to zero
#______________________________________________________________________

  if (isOne($l))   
   {%$t = (c=>0);
    return;
   }  

#______________________________________________________________________
# Otherwise simplify log(exp(single-term))
#______________________________________________________________________

  my ($lc, $li, $ld, $ls, $lD, $le, $ll) = get($$l[0]);

  return unless $lc == 1 and $li == 0 and $ld == 1;
  return if     defined($ls) or defined($lD) or defined($ll);
  return unless defined($le);

  return if scalar(@$le) != 1;

  delete $t->{log};
  my $r = multiplyTerm($t, $$le[0]);
 
  %$t = %{$$r[0]};
 }

#______________________________________________________________________
# Remove common coefficients, divisors.
#______________________________________________________________________

sub removeCommonCD(@)
 {my $e = getAllExpressions(\@_);

  return unless scalar(@$e);

  my @c; my @d;                          
  for my $a(@$e)                      
   {my ($c, undef, $d) = get($a);
    push @c, $c; push @d, $d;
   }

  my $dd = $d[0]; $dd = lcm($dd, $_) for (@d);                      

  my $cc;
  for my $i(0..scalar(@c)-1)
   {$c[$i] *= $dd/ $d[$i];
    $cc = $c[$i]           unless $cc;
    $cc = gcd($cc, $c[$i]) if     $cc;
   }

  $_ /= $cc for (@c);

  for my $i(0..scalar(@c)-1)
   {$e->[$i]{c} = $c[$i];
    delete $e->[$i]{d};
   }
 }

#______________________________________________________________________
# Remove a common factor from a list of expressions.
#______________________________________________________________________

sub removeCommonFactor(@)
 {my $e = getAllExpressions(\@_);

# Get all the variables across all expressions

  my $w = {};                          
  for my $a(@$e)                      
   {$w = {%$w, %{$a->{v}}} if $a->{v};
   }

# Find minimum power of each variable across all expressions

  for my $a(@$e)                      
   {my $W = {};
    for my $vp(getVP($a))
     {my ($v, $p) = @$vp;
      $W->{$v} = $w->{$v} if exists($w->{$v});
      $W->{$v} = $p       if exists($W->{$v}) and $W->{$v} > $p;
     }
    $w = {%$W};
   }

  return undef unless keys(%$w);

# Remove common factor from all expressions

  for my $a(@$e)                      
   {for my $vp(getVP($a))
     {my ($v, $p) = @$vp;
      next unless exists($w->{$v});
      $a->{v}{$v} -= $w->{$v};
      delete $a->{v}{$v} unless $a->{v}{$v}; 
     }  
    delete $a->{v} unless keys(%{$a->{v}}); 
   }
 }

#______________________________________________________________________
# Remove a common field: sqrt divide exp log
#______________________________________________________________________

sub removeCommonField(@)
 {my $e = getAllExpressions(\@_);

#______________________________________________________________________
# Check they all have the same field before going further
#______________________________________________________________________

  L: for my $f(qw(sqrt divide exp log))
   {my @s = ();                    
    for my $a(@$e)                      
     {next L unless defined($a->{$f});
      push @s, $a->{$f};
     }

    next L unless @s;

#______________________________________________________________________
# Confirm thay all have the same expression in the common field
#______________________________________________________________________

    my $a = shift(@s);
    for my $b(@s)    
     {return undef unless equals($a, $b); 
     }

#______________________________________________________________________
# Delete the field in common
#______________________________________________________________________

    delete $_->{$f} for (@$e);    
   }
 }

#______________________________________________________________________
# Remove a common I
#______________________________________________________________________

sub removeCommonI(@)
 {my $e = getAllExpressions(\@_);
  my ($i0, $i1) = (0, 0);

  for my $a(@$e)                      
   {++$i0 unless defined($a->{i});
    ++$i1 if     defined($a->{i});
   }
  return unless $i0 == 0;

  delete $_->{i} for (@$e);    
 }

#______________________________________________________________________
# Substitute.
#______________________________________________________________________

sub sub($@)
 {my $E = new(shift());
  my @R = @_;
  my $S = $E;

# Each replacement

  for(;@R > 0;)
   {my $s =     shift @R;  # Replace this variable
    my $W = new(shift @R); # With this expression
    my @T = ();

    $s =~ /^[a-zA-Z=]+$/ or croak "Can only substitute an expression for a variable, not $s";

# Each expression

    for my $e(@$S)
     {for my $f(qw(sqrt divide exp))
       {$e->{$f} = &sub($e->{$f},  @_) if defined($e->{$f});
       }

      my $n = delete $e->{v}{$s} || 0;
      if ($n == 0)
       {push @T, $e;
       }
      else
       {push @T, @{multiply(new($e), power($W,  $n))} if $n > 0;
        push @T, @{divide  (new($e), power($W, -$n))} if $n < 0;
       }
     }
    $S = \@T;
   }

  return add(new($S));
 }

#______________________________________________________________________
# Differentiate.
#______________________________________________________________________

sub d($;$);
sub d($;$)
 {my $c = new($_[0]); # Differentiate this expression 
  my $b =     $_[1];  # With this variable

#______________________________________________________________________
# Get differentrix. Assume 'x', 'y', 'z' or 't' if appropriate.
#______________________________________________________________________

  if (defined($b) and !ref $b)
   {$b =~ /^[a-zA-Z]+$/ or croak "Cannot differentiate by '$b'";
   }
  else
   {my %b = %{getVE($b)};
       %b = %{getVE($c)} unless scalar(keys(%b));
    my $i = 0;
    ++$i, $b = 'x'     if scalar(keys(%b)) == 0; # Constant expression anyway
    ++$i, $b = (%b)[0] if scalar(keys(%b)) == 1;
    ++$i, $b = 't'     if scalar(keys(%b))  > 1 and defined($b{t});
    ++$i, $b = 'x'     if scalar(keys(%b))  > 1 and defined($b{x});
    ++$i, $b = 'y'     if scalar(keys(%b))  > 1 and defined($b{y});
    ++$i, $b = 'z'     if scalar(keys(%b))  > 1 and defined($b{z});
    defined($b) and $i  == 1 or 
      croak "Please specify a single variable to differentiate by";
   }

#______________________________________________________________________
# Each term
#______________________________________________________________________

  my @R = ();
  for my $t(@$c)
   {my %V = %$t;
    my $S = delete $V{sqrt};
    my $D = delete $V{divide};
    my $E = delete $V{exp};
    my $L = delete $V{log};
    my $s = d($S, $b) if $S;    
    my $d = d($D, $b) if $D;      
    my $e = d($E, $b) if $E;  
    my $l = d($L, $b) if $L;  

#______________________________________________________________________
# Differentiate Variables: A*v**n->d == A*n*v**(n-1)
#______________________________________________________________________

     {my %v = %V;
      delete $v{v};
      %{$v{v}} = %{$V{v}} if defined($V{v});
      if (exists $v{v}{$b} and $v{v}{$b})
       {$v{c} *= $v{v}{$b};
        --$v{v}{$b};
        $v{sqrt}   = $S if $S;
        $v{divide} = $D if $D;
        $v{exp}    = $E if $E;
        $v{log}    = $L if $L;
        push @R, new(\%v);
      }
     }

#______________________________________________________________________
# Differentiate Sqrt: A*sqrt(F(x))->d == 1/2*A*f(x)/sqrt(F(x))
#______________________________________________________________________

     {my %v = %V;
      if ($S)
       {$v{divide} = $D if $D;
        $v{exp}    = $E if $E;
        $v{log}    = $L if $L;
        $v{d} *= 2 if     defined($v{d});  # Divide by 2
        $v{d}  = 2 unless defined($v{d});  #  fast method
        push @R, divide(multiply(new(\%v), $s), sqrt($S));
       }
     }

#______________________________________________________________________
# Differentiate Divide: A/F(x)->d == -A*f(x)/F(x)**2
#______________________________________________________________________

     {my %v = %V;
      if ($D)
       {$v{sqrt} = $S if $S;
        $v{exp}  = $E if $E;
        $v{log}  = $L if $L;
        $v{c} = -$v{c}; # *-1, fast method
        push @R, divide(multiply(new(\%v), $d), multiply($D, $D));
       }
     }

#______________________________________________________________________
# Differentiate Exp: A*exp(F(x))->d == A*f(x)*exp(F(x))
#______________________________________________________________________

     {my %v = %V;
      if ($E)
       {$v{sqrt}   = $S if $S;
        $v{divide} = $D if $D;
        $v{log}    = $L if $L;
        $v{exp}    = $E;
        push @R, multiply(new(\%v), $e);
       }
     }
#______________________________________________________________________
# Differentiate Log: A*log(F(x))->d == A*f(x)/F(x)
#______________________________________________________________________

     {my %v = %V;
      if ($L)
       {$v{sqrt}   = $S if $S;
        $v{divide} = $D if $D;
        $v{exp}    = $E if $E;
        push @R, divide(multiply(new(\%v), $l), $L);
       }
     }
   }

#______________________________________________________________________
# Result
#______________________________________________________________________

  add(new(\@R));
 }

#______________________________________________________________________
# Dot - complex dot product.
#______________________________________________________________________

sub dot($$)
 {my ($a, $b) = @_;

  new(re($a) * re($b) + im($a)* im($b));
 }

#______________________________________________________________________
# Dot Product operator.
#______________________________________________________________________

sub dot3
 {my ($a, $b, $c) = @_;
  dot($a, new($b));
 }

#______________________________________________________________________
# Unit: intersection with unit circle.
#______________________________________________________________________

sub unit($)
 {my $a = $_[0];
  my $l = modulus($a);
  croak "Cannot make unit out of zero" if $l == 0;
  divide($a, $l); 
 }

#______________________________________________________________________
# Unit operator.
#______________________________________________________________________

sub unit3
 {unit($_[0]);
 }

#______________________________________________________________________
# The area of the parallelogram formed by two complex vectors.
#______________________________________________________________________

sub cross($$)
 {my ($a, $b) = ($_[0], $_[1]);

  sqrt((dot($a,$a) * dot($b,$b)) - (dot($a,$b)**2)); 
 }

#______________________________________________________________________
# Cross operator.
#______________________________________________________________________

sub cross3
 {cross($_[0], new($_[1]));
 }

#______________________________________________________________________
# Simplify an equation known to be zero by multiplying out by all
# 'divide by' and eliminating common coefficients, divisors, sqrts.
#______________________________________________________________________

sub isZeroRemoveCommon($)
 {my $r = new($_[0]); # Expression

#______________________________________________________________________
# Now that multiply() checks for multiplication of a term by an
# expression which is equal to a 'divide' field, we can simplify the
# code to:
#______________________________________________________________________

  L: for(;;)
   {for my $a(@$r)
     {my $d = $a->{divide};
      next unless defined($d);
      $r *= $d;
      next L;
     }
    last L;  
   }
#
#______________________________________________________________________
# Each term: multiply out all negative powers
#______________________________________________________________________

  my %v = ();                          
  for my $a(@$r)                      
   {for my $vp(getVP($a))
     {my ($v, $p) = @$vp;
      $v{$v} += -$p if $p < 0;
     }
   }

  for my $a(@$r)                      
   {for my $v(keys(%v))
     {$a->{v}{$v} += $v{$v};
      delete $a->{v}{$v} unless $a->{v}{$v};
     }
   }

#______________________________________________________________________
# Result - remove common factors
#______________________________________________________________________

  removeCommonCD     ($r); # Common coefficients and divisors
  removeCommonI      ($r); # Common i                          
  removeCommonField  ($r); # Common fields         
  removeCommonFactor ($r); # Common variable powers
  $r;
 }

#______________________________________________________________________
# Simplify an equation known to equal zero.
#______________________________________________________________________

sub isZero($);
sub isZero($)
 {my $E = add(new($_[0]));      # Expression
  return $E unless scalar(@$E); # Immediate return if empty (0) expression

#______________________________________________________________________
# Remove square roots.
#______________________________________________________________________

  for my $h(1..100)               # 100  is unlikely to be exceeded
   {$E = isZeroRemoveCommon($E);  # Remove common factors
    return $E unless scalar(@$E); # Immediate return if empty (0) expression

#______________________________________________________________________
# Partition by square roots.
#______________________________________________________________________

    my %S = ();
    for my $e(@$E)
     {my $s = $e->{sqrt};
      push @{$S{"$s"}}, $e if $s;      # Square root
      push @{$S{""}},   $e unless $s;  # Non square root
     }

#______________________________________________________________________
# Return immediately if there are no square roots.
#______________________________________________________________________

    my $ns =  scalar(keys(%S)); 
    return $E unless $ns;
    return $E if $ns == 1 and $S{''}; 

#______________________________________________________________________
# Square each partitions, as required by the formulae below.
# Convert: sqrt(a)*b + sqrt(a)*c to sqrt(a)*(b+c) and then square to 
# get:     a*(b+c)**2.
#______________________________________________________________________

    my @t;
    for my $s(keys(%S))
     {if ($s eq '')
       {my $r = add(new([$S{$s}]))**2;
        push @t, $r;
       }
      else
       {my @s = @{$S{$s}};
        my @R;  # Result of squaring this partition
        my $q;  # The sqrt, common to all terms, characterizing this partition
        for my $t(@s)
         {my $A = new($t);
          for my $a(@$A)
           {$q = delete $a->{sqrt};
           }
          push @R, $A; # Sum terms in this parition
         }
        my $s = add(new(\@R));
        my $r = add(new(\@R))**2*$q;
        push @t, $r;
       }
     }  

#______________________________________________________________________
# I can multiply out upto 4 square roots using the formulae below.     
# There is a formula for 5 sqrts, but it is big. I believe there is
# no formulae for 6 and above - rather like Galois.
# These formulae are obtained by squaring out and rearranging:
# sqrt(a)+sqrt(b)+sqrt(c)+sqrt(d) == 0 until no sqrts remain, and
# then matching terms to produce optimal execution.
#______________________________________________________________________
   
    $ns < 5 or die "There are $ns square roots present.  I can handle less than 5";

    my ($a, $b, $c, $d) = @t;

    if    ($ns == 1)
     {$E = $a;
     }
    elsif ($ns == 2)
     {$E = $a-$b;
     }
    elsif ($ns == 3)
     {$E = -$a**2+2*$a*$b-$b**2+2*$c*$a+2*$c*$b-$c**2;
     }
    elsif ($ns == 4)
     {my $a2=$a *$a;
      my $a3=$a2*$a;  
      my $a4=$a3*$a;  
      my $b2=$b *$b;
      my $b3=$b2*$b;  
      my $b4=$b3*$b;  
      my $c2=$c *$c;
      my $c3=$c2*$c;  
      my $c4=$c3*$c;  
      my $d2=$d *$d;
      my $d3=$d2*$d;  
      my $d4=$d3*$d;
      my $bpd = $b+$d;  
      my $bpc = $b+$c;  
      my $cpd = $c+$d;  
      $E =
-  ($a4 + $b4 + $c4 + $d4)
+ 4*(
   +$a3*($b+$cpd)+$b3*($a+$cpd)+$c3*($a+$bpd)+$d3*($a+$bpc)
   -$a2*($b *($cpd)+ $c*$d)   
   -$a *($b2*($cpd)+$d2*($bpc))
    )

- 6*($a2*$b2+($a2+$b2)*($c2+$d2)+$c2*$d2)

- 4*$c*($b2*$d+$b*$d2)
- 4*$c2*($a*($bpd)+$b*$d)
+40*$c*$a*$b*$d   
;   
     }
   }
 }

#______________________________________________________________________
# Solve an equation known to be equal to zero for a specified variable. 
# ($x+1)->solve(qw(x)) produces -1.  Variables whose values are known,
# and thus are in effect, known constants, should be listed after the 
# variable to be solved for.  
#______________________________________________________________________

sub solve($@)
 {my $e = shift; # Expression to solve
  my $x = shift; # Solve for this variable
  my @c = @_;    # Variables whose values are known

  my $z = isZero($e);            # Set equation to zero

# Classify variables in the expressions comprising equation

  my %v = ();
  for my $y (@{getAllExpressions($z)})
   {%v = (%v, %{$y->{v}}) if defined($y->{v});          
   }                                                                
  $_ = 0 for(values(%v)); # Set unknowns to 0 
  $v{$_} = 1 for(@c);     #   and knowns to 1 
  $v{$x} = 2;             # Solve for x            

# Consider terms which are constant with respect to x

  my @T = (); my @X = ();
  C: for my $t(@$z)
   {for my $v(keys(%{$t->{v}}))
     {next C unless $v{$v};
     }
    push @T, $t unless $t->{v}{$x};
    push @X, $t if     $t->{v}{$x};
   }
  die "Variable $x does not occur in equation to solve: $e" unless @X;
    
# Maximum power of x and gcd of power of x

   my $p = $X[0]->{v}{$x};
   for my $y(@X)
    {$p = $y->{v}{$x} if $p > $y->{v}{$x};
    }
   my $g = $p;
   for my $y(@X)
    {$g = gcd($g, $y->{v}{$x});
    }

# Proposed solution

  my $xx;

  if    ($p == 1 and $p == $g)
   {delete $_->{v}{$x} for(@X);
    $xx = divide(negate(new(bless([@T]))), new(bless([@X])));
   } 
  elsif ($p == 2 and $p == $g)
   {delete $_->{v}{$x} for(@X);
    $xx = sqrt(divide(negate(new(bless([@T]))), new(bless([@X]))));
   } 
  else
   {die "Maximum power of $x is $p/$g";
   }

# Check that it works

  my $yy = $e->sub($x=>$xx);
  $yy == 0 or die "Proposed solution \$$x=$xx does not zero equation $e";
  $xx; 
 }

#______________________________________________________________________
# Degree of a polynomial.   
#______________________________________________________________________

sub polynomialDegree($)
 {my $A = $_[0];

  my $D = 0;
  for my $a(@$A)
   {my $d = 0;
    for my $vp(getVP($a))
     {my ($v, $p) = @$vp;
      $d += abs($p);
     }
    $D = $d if $d > $D; 
   }
  return $D;
 }

#______________________________________________________________________
# Polynomial division.
# Divide by subtracting multiples of $b from $a to eliminate terms from
# $a. Proceed from highest to lowest powers of $a in order to avoid
# inadvertantly producing an infinite series.  The expression is assumed
# to be already in power order as produced by add().
#______________________________________________________________________

sub polynomialDivision($$)
 {my ($a, $b) = (new($_[0]), new($_[1]));
  my $na = polynomialDegree($a);
  my $nb = polynomialDegree($b);
  return (new(0), $a) if $na < $nb;

  my $d = new(0);       # Result
  my $B = new(pop @$b); # Highest power of b
  my $i = invert($B);   # Inverted highest power of b
  defined($i) or return (new(0), $a); # Unable to divide 

  for(my $k = 0; $k <= $na; ++$k)         # Limit the loop
   {my $A = new(pop @$a); 
    my $c = multiply($A, $i);  # Simple divide should work
    $d += $c; 
    $a -= $c * $b;
    return ($d, $a) if scalar(@$a) == 0;  # Single term
#   print "\n\nAAAA a=$a d=$d b=$b c=$c n=$n na=$na b=$nb\n";
    my $n = polynomialDegree($a);
    return ($d, $a)        if $n < $nb;   # Pointlessly small
    return (new(0), $_[0]) if $n > $na;   # Blowing up
   }
#  print "ZZZZ Result=$d  Remainder=$a\n";
  ($d, $a);
 }

#______________________________________________________________________
#   T E S T S  tests  T E S T S  tests  T E S T S  tests  T E S T S
# The following routines test the above.  These tests are run by default
# if you execute this package as opposed to using it.
#   T E S T S  tests  T E S T S  tests  T E S T S  tests  T E S T S
#______________________________________________________________________
#______________________________________________________________________
# Ellipse: Demonstrate various invariants of the ellipse algebraically.
# The expanded expressions are quite large.  Either substitution, via
# eval(), or careful choice of expresion for the locus of ellipse can
# be used to overcome this difficulty.
#______________________________________________________________________

sub testEllipse
 {my $errors = 0;

#______________________________________________________________________
# Test conjecture.
#______________________________________________________________________

  my $test = sub($$)
   {my $z = shift();              # Expression
    my $t = shift();              # Title
    my $y = $z->isZero();         # Is result zero as desired? 

    print "z=$z\ny=$y\n";
    print "FAIL: $t"    if     $y;
    print "SUCCESS: $t" unless $y;
    print "\n\n";
    $errors++ if $y;
   };

#______________________________________________________________________
# Focus trip == 2R.
#______________________________________________________________________

   {my ($i, $r, $R, $f, $x) = symbols(qw(i r R f x));

    my $y  = sqrt($R*$R-$f*$f - $x*$x +$f*$f*$x*$x / ($R*$R));  # Ellipse: rr=RR-ff
    my $a  = $x+$i*$y - $f;            # Vector from Focus to locus
    my $b  = $x+$i*$y + $f;            # Vector from other Focus to locus

    my $z  = abs($a) + abs($b) - 2*$R; # Focus trip

    $test->($z, "Focus trip == 2R");
   }

#______________________________________________________________________
# Angle of incidence equals angle of reflection via dot product with
# normal to tangent vector.                                         
#______________________________________________________________________

   {my ($i, $r, $R, $f, $x, $y) = symbols(qw(i r R f x y));

       $r  = sqrt($R*$R - $f*$f);      # Focus
       $y  = sqrt($R*$R-$f*$f - $x*$x +$f*$f*$x*$x / ($R*$R));  # Ellipse: rr=RR-ff
  
    my $p  = $x + $i * $y;             # x,y point on locus of ellipse
    my $s  = $x*$r*$r + $i*$y*$R*$R;   # Normal to tangent at locus
  
    my $a  = $p - $f;                  # Vector from Focus to locus
    my $b  = $p + $f;                  # Vector from other Focus to locus
  
    my $c  = $a * abs($b);             # Make each focus vector the same length 
    my $d  = $b * abs($a);             #   so that dot or cross will measure angle          
  
    my $A  = $c^$s;                    # Angle of Reflection vs
    my $B  = $d^$s;                    # Angle of Incidence
  
    my $z  = $A - $B;                  # Compare angle of incidence to angle of reflection
  
#      $y  = sqrt($r*$r - $r*$r*$x*$x / ($R*$R));  # Ellipse
#      $f  = sqrt($R*$R - $r*$r);      # Focus
#      $z  = eval($z);                 # Substitute for f,y
  
    $test->($z, "Angle of incidence equals angle of reflection via dot product with normal to tangent");
   }

#______________________________________________________________________
# Angle of incidence equals angle of reflection via dot product with
# tangent vector using optimized substitutions.
# NB: A+B not A-B.                
#______________________________________________________________________

   {my ($i, $r, $R, $f, $x, $y) = symbols(qw(i r R f x y));

       $r  = sqrt($R*$R - $f*$f);      # Focus
       $y  = sqrt($R*$R-$f*$f - $x*$x +$f*$f*$x*$x / ($R*$R));  # Ellipse: rr=RR-ff
  
    my $p  = $x + $i * $y;             # x,y point on locus of ellipse
    my $s  = $i*$x*$r*$r - $y*$R*$R;   # Tangent at locus
  
    my $a  = $p - $f;                  # Vector from Focus to locus
    my $b  = $p + $f;                  # Vector from other Focus to locus
  
    my $c  = $a * abs($b);             # Make each focus vector the same length 
    my $d  = $b * abs($a);             #   so that dot or cross will measure angle          
  
    my $A  = $c ^ $s;                  # Angle of Reflection vs
    my $B  = $d ^ $s;                  # Angle of Incidence
  
    my $z  = $A + $B;                  # Compare angle of incidence to angle of reflection
                                       # NB: Need A+B here due to antisymmetry of cosine around pi/2
#      $r  = sqrt($R*$R - $f*$f);      # Focus
#      $y  = sqrt($R*$R-$f*$f - $x*$x +$f*$f*$x*$x / ($R*$R));  # Ellipse: rr=RR-ff
#      $z  = eval($z);                 # Substitute for r,y
  
    $test->($z, "Angle of incidence equals angle of reflection via dot product with tangent");
   }

#______________________________________________________________________
# Angle of incidence equals angle of reflection via cross product with
# normal to tangent vector.
#______________________________________________________________________

   {my ($i, $r, $R, $f, $x, $y) = symbols(qw(i r R f x y));

       $r  = sqrt($R*$R - $f*$f);      # Focus
       $y  = sqrt($R*$R-$f*$f - $x*$x +$f*$f*$x*$x / ($R*$R));  # Ellipse: rr=RR-ff
  
    my $p  = $x + $i * $y;             # x,y point on locus of ellipse
    my $s  = $x*$r*$r + $y*$R*$R*$i;   # Normal to tangent at locus
  
    my $a  = $p - $f;                  # Vector from Focus to locus
    my $b  = $p + $f;                  # Vector from other Focus to locus
  
    my $c  = $a * abs($b);             # Make each focus vector the same length 
    my $d  = $b * abs($a);             #   so that dot or cross will measure angle          
  
    my $A  = $c x $s;                  # Angle of Reflection vs
    my $B  = $d x $s;                  # Angle of Incidence
  
    my $z  = $A - $B;                  # Compare angle of incidence to angle of reflection
  
 #     $y  = sqrt($r*$r - $r*$r*$x*$x / ($R*$R));  # Ellipse
 #     $f  = sqrt($R*$R - $r*$r);      # Focus
 #     $z  = eval($z);                 # Substitute for f,y
  
    $test->($z, "Angle of incidence equals angle of reflection via cross product with normal to tangent");
   }

#______________________________________________________________________
# Angle of incidence equals angle of reflection via cross product with
# tangent vector.
#______________________________________________________________________

   {my ($i, $r, $R, $f, $x, $y) = symbols(qw(i r R f x y));

       $r  = sqrt($R*$R - $f*$f);      # Focus
       $y  = sqrt($R*$R-$f*$f - $x*$x +$f*$f*$x*$x / ($R*$R));  # Ellipse: rr=RR-ff
  
    my $p  = $x + $i * $y;             # x,y point on locus of ellipse
    my $s  = $i*($x*$r*$r + $y*$R*$R*$i);   # Normal to tangent at locus
  
    my $a  = $p - $f;                  # Vector from Focus to locus
    my $b  = $p + $f;                  # Vector from other Focus to locus
  
    my $c  = $a * abs($b);             # Make each focus vector the same length 
    my $d  = $b * abs($a);             #   so that dot or cross will measure angle          
  
    my $A  = $c x $s;                  # Angle of Reflection vs
    my $B  = $d x $s;                  # Angle of Incidence
  
    my $z  = $A - $B;                  # Compare angle of incidence to angle of reflection

#      $y  = sqrt($r*$r - $r*$r*$x*$x / ($R*$R));  # Ellipse
#      $f  = sqrt($R*$R - $r*$r);      # Focus
#      $z  = eval($z);                 # Substitute for f,y
  
    $test->($z, "Angle of incidence equals angle of reflection via cross product with tangent");
   }

#______________________________________________________________________
# Return number of errors.
#______________________________________________________________________

  return [$errors, 'Ellipse'];
 }

#______________________________________________________________________
# General tests.
#______________________________________________________________________

sub testGeneral()
 {my $errors = 0;
 
#______________________________________________________________________
# Test each expression.
#______________________________________________________________________

  my $t = sub ($$$)
   {my ($t, $a, $b) = @_;
    my $c = $a-$b;

    if ($c == 0)
     {print "OK $t\n";
     }
    else
     {print "ERROR :$t! Following two expressions not equal!\n$a\n\n$b\n\n",
         "Difference:\n$c\n\n";
      ++$errors;
     }
   };

#______________________________________________________________________
# Test these expressions.
#______________________________________________________________________

  my ($a, $b, $x, $y, $i, $o, $c2, $c3, $pi) = symbols(qw(a b x y i 1 2 3 pi));

#______________________________________________________________________
# Complex number basics.
#______________________________________________________________________

  &$t('aa', $i x 1,  1);
  &$t('ab', $i^1,    0);
  &$t('ac', $i^$i,   1);
  &$t('ad', !$i,     $i);
  &$t('ae', abs $i,  1);
  &$t('af', re $i,   0);
  &$t('ag', im $i,   1);
  &$t('ah', re $o,   1);
  &$t('ai', im $o,   0);
  &$t('aj', ~($a+$b) == ~ $a + ~ $b, 1); # Conjugation distributes over addition
  &$t('ak', ~($a*$b) == ~ $a * ~ $b, 1); # Conjugation distributes over times
  &$t('al', ~($a**2) == (~ $a)**2,   1); # Conjugation distributes over power
  &$t('am', abs(!($x+$y*$i)),        1); # Length of unit vector
  &$t('an', abs(($a+$i*sqrt(1-$a*$a))*($b+$i*sqrt(1-$b*$b))), 1);
  &$t('ao', abs($a+$i*$b)*abs($x+$i*$y),
           abs(($a+$i*$b)*($x+$i*$y)));  # Length of product = product of lengths
  my $q = ($i+1) x ($i-1); # For some strange reason, does not work in parameter list
  &$t('ap', $q,  2);
  &$t('aq', (1+$i)^(-1+$i),       0);

#______________________________________________________________________
# Cosine, Sine and related trigonometric identities
#______________________________________________________________________
   
# Reciprocals

  &$t('caa', sin($x), 1/csc($x));
  &$t('cab', cos($x), 1/sec($x));                            
  &$t('cac', tan($x), 1/cot($x));                            
  &$t('cad', csc($x), 1/sin($x));                            
  &$t('cae', sec($x), 1/cos($x));                            
  &$t('caf', cot($x), 1/tan($x));
                           
# Pythagoras

  &$t('cba', sin($x)**2 +  cos($x)**2, 1);
  &$t('cbb', tan($x)**2+1, sec($x)**2); 
  &$t('cbc', cot($x)**2+1, csc($x)**2); 

# Quotient  

  &$t('cca', tan($x), sin($x)/cos($x));
  &$t('ccb', cot($x), cos($x)/sin($x));   

# Co-Function Identities

  &$t('cda', sin($x), cos($pi/2-$x)); 
  &$t('cdb', cos($x), sin($pi/2-$x));      
  &$t('cdc', cot($x), tan($pi/2-$x)); 
  &$t('cdd', sec($x), csc($pi/2-$x));
  &$t('cde', csc($x), sec($pi/2-$x));
  &$t('cdf', tan($x), cot($pi/2-$x));

# Even-Odd Identities

  &$t('cea', cos($x),  cos(-$x));
  &$t('ceb', sin($x), -sin(-$x));
  &$t('cec', tan($x), -tan(-$x));
  &$t('ced', cot($x), -cot(-$x));
  &$t('cee', csc($x), -csc(-$x));  
  &$t('cef', sec($x),  sec(-$x));  

# Values of sin, cos at well known points

  &$t('cfa', cos(0),       1);
  &$t('cfb', cos($pi/2),   0);
  &$t('cfc', cos($pi),    -1);
  &$t('cfd', cos(3*$pi/2), 0);
  &$t('cfe', cos(4*$pi/2), 1);
  &$t('cff', sin(0),       0);
  &$t('cfg', sin($pi/2),   1);
  &$t('cfh', sin($pi),     0);
  &$t('cfi', sin(3*$pi/2),-1);
  &$t('cfj', sin(4*$pi/2), 0);

# Sums and Differences

  &$t('cga', sin($x+$y), sin($x)*cos($y)+cos($x)*sin($y));
  &$t('cgb', sin($x-$y), sin($x)*cos($y)-cos($x)*sin($y));
  &$t('cgc', cos($x+$y), cos($x)*cos($y)-sin($x)*sin($y));
  &$t('cgd', cos($x-$y), cos($x)*cos($y)+sin($x)*sin($y));
  &$t('cge', tan($x+$y), (tan($x)+tan($y))/(1-tan($x)*tan($y)));
  &$t('cgf', tan($x-$y), (tan($x)-tan($y))/(1+tan($x)*tan($y)));

# Double angles        

  &$t('cha', sin(2*$x), 2*sin($x)*cos($x));
  &$t('chb', cos(2*$x), cos($x)**2-sin($x)**2);
  &$t('chc', cos(2*$x), 2*cos($x)**2-1);
  &$t('chd', cos(2*$x), 1-2*sin($x)**2);
  &$t('che', tan(2*$x), 2*tan($x)/(1-tan($x)**2));

# Power-Reducing/Half Angle Formulas       

  &$t('cia', sin($x)**2, (1-cos(2*$x))/2);
  &$t('cib', cos($x)**2, (1+cos(2*$x))/2);
  &$t('cic', tan($x)**2, (1-cos(2*$x))/(1+cos(2*$x)));

# Sum-to-Product Formulas      

  &$t('cja', sin($x)+sin($y), 2*sin(($x+$y)/2)*cos(($x-$y)/2));
  &$t('cjb', sin($x)-sin($y), 2*cos(($x+$y)/2)*sin(($x-$y)/2));
  &$t('cjc', cos($x)+cos($y), 2*cos(($x+$y)/2)*cos(($x-$y)/2));
  &$t('cjd', cos($x)-cos($y),-2*sin(($x+$y)/2)*sin(($x-$y)/2));

# Product-to-Sum Formulas       

  &$t('cka', sin($x)*sin($y), cos($x-$y)/2-cos($x+$y)/2);
  &$t('ckb', cos($x)*cos($y), cos($x-$y)/2+cos($x+$y)/2);
  &$t('ckc', sin($x)*cos($y), sin($x+$y)/2+sin($x-$y)/2);
  &$t('ckd', cos($x)*sin($y), sin($x+$y)/2-sin($x-$y)/2);


#______________________________________________________________________
# Differentials.
#______________________________________________________________________

  &$t('da', sqrt($x**3)->d, '3/2'*sqrt($x));
  &$t('db', (1/$x**10) ->d,  -10/$x**11);
  &$t('dc', ((1+$x)/sqrt(1+$x))->d, (sqrt(1+$x))->d);
  &$t('dd', exp($i*$x), exp($i*$x)->d->d->d->d);

  &$t('de', cos($x),   -cos($x)->d->d);
  &$t('df', sin($x),   -sin($x)->d->d);

  &$t('dg', sin($x)->d,  cos($x));
  &$t('dh', cos($x)->d, -sin($x));
  &$t('di', tan($x)->d,  tan($x)**2 + 1);
  &$t('dj', tan($x)->d,  sec($x)**2);
  &$t('dk', cot($x)->d, -csc($x)**2);
  &$t('dl', sec($x)->d,  sec($x)*tan($x));
  &$t('dm', csc($x)->d, -csc($x)*cot($x));

#______________________________________________________________________
# Hyperbolic functions
#______________________________________________________________________

  &$t('ha', cosh($x)->d, sinh($x));
  &$t('hb', sinh($x)->d, cosh($x));

  &$t('hc', cosh($x)**2-sinh($x)**2, 1);
  &$t('hd', cosh($x+$y), cosh($x)*cosh($y)+sinh($x)*sinh($y));
  &$t('he', sinh($x+$y), sinh($x)*cosh($y)+cosh($x)*sinh($y));
   
# Reciprocals

  &$t('haa', sinh($x), 1/csch($x));
  &$t('hab', cosh($x), 1/sech($x));                            
  &$t('hac', tanh($x), 1/coth($x));                            
  &$t('had', csch($x), 1/sinh($x));                            
  &$t('hae', sech($x), 1/cosh($x));                            
  &$t('haf', coth($x), 1/tanh($x));

# Pythagoras

  &$t('hba', cosh($x)**2 - sinh($x)**2, 1);
  &$t('hbb', tanh($x)**2 + sech($x)**2, 1);
  &$t('hbc', coth($x)**2 - csch($x)**2, 1);
                            
# Relations to Trigonometric Functions

  &$t('hza', sinh($x), -$i*sin($i*$x));
  &$t('hzb', csch($x),  $i*csc($i*$x));
  &$t('hzc', cosh($x),     cos($i*$x));
  &$t('hzd', sech($x),     sec($i*$x));
  &$t('hze', tanh($x), -$i*tan($i*$x));
  &$t('hzf', coth($x),  $i*cot($i*$x));

#______________________________________________________________________
# Exp.
#______________________________________________________________________
   
  &$t('ea',  exp($x)*exp($i*$x)*exp($x)*exp(-$i*$x)-exp(2*$x), 0);

  &$t('eb', 1+$o+'1/2'*$o**2+'1/6'*$o**3+'1/24'*$o**4+'1/120'*$o**5+
            '1/720'*$o**6+'1/5040'*$o**7+'1/40320'*$o**8,
            '109601/40320'); # Approximate exp(1)

  &$t('ed', exp(log($x)), $x);
  &$t('ee', log(exp($x)), $x);
  &$t('ef', exp($i*$pi),  -1);
  &$t('eg', $i*exp(3*$i*$pi/2), 1);

#______________________________________________________________________
# Polynomials.
#______________________________________________________________________
   
  &$t('pa', ($x+$x*$x)*$y/($x*$y),                  1+$x);
  &$t('pb', (2*$a*$b**20) / (4*$b**19+4*$b**19),     ($a*$b)/4);
  &$t('pc', (4*$b+4*$a*$b)/(4*$b+4*$a*$b),          1/($a+1)*$a+1/($a+1));
  &$t('pd', (($x+$i*sqrt(1-$x*$x))**3 -
             ($x+$i*sqrt(1-$x*$x))**2)->im->isZero == -1-2*$x+4*$x**2, 1); # Side of pentagon crosses -x axis in  unit circle.  
  &$t('pe', (sqrt($c2)+sqrt($c3))**4-10*(sqrt($c2)+sqrt($c3))**2,     -1); # Polynomial with sqrt(2)+sqrt(3) as a zero
  &$t('sf', ($a**16-1)/($a**8-1),                   ($a**8+1));
  &$t('pg', ($a+1)**11 / (1+$a)**12,                1/($a+1));
  &$t('ph', ($a**2 + $b**2)/($a**2 + $b**2),        1);
  &$t('pi', ($a**2 + 2*$a*$b +$b**2) / ($a+$b),     $a+$b);
  &$t('pj', (($x**2-1)/(($x+1)*($x-1)))->print eq "1", 1);  # checks polynomial division 

#______________________________________________________________________
# Square roots.
#______________________________________________________________________
   
  &$t('sc', sqrt($a+1) / sqrt(1+$a),                1);
  &$t('sd', 2*$b**2*sqrt($a+1) / (4*$b*sqrt(1+$a)), $b/2);
  &$t('se', 1/sqrt(1+$a),                           1/sqrt(1+$a)); 
  &$t('sf', 1/sqrt(1+$a)**3,                        1/(sqrt(1+$a)+sqrt(1+$a)*$a));
  &$t('sg', sqrt($a+1)**3 / sqrt(1+$a)**3,          1);

#______________________________________________________________________
# Improvements pending.
#______________________________________________________________________

  &$t('za',  sqrt($a+1)**2 / sqrt(1+$a), sqrt(1+$a)); # Poor representation of #1

  return [$errors, 'General Tests'];
 }

#______________________________________________________________________
# Check test results
#______________________________________________________________________

sub checkTest($$$)
 {my $t = shift;       # Test number
  my @a = @{shift()};  # Tests
  my $b = shift();     # Expected results
  my $l = '';
  my $e = 0;           # Error state

# Very crude formatting of results

  for my $e(@a)
   {my $t = $e;
    $t  = "  $e\n" if ref($e) or $e =~ /^\d+$/;
    $t .= "\n\n"   if length($t) > 40 and ref($e);
    $l .= $t;
   }
  $l =~ s/\=\ \ /\=/g;

  print "\n", substr("Test $t".'-'x80, 0, 79)."\n$l\nTest ";

# Remove spaces and compare results - error location would be helpful        

  my $c = $b;
     $c =~ s/\s+//sg;
     $l =~ s/\s+//sg;

# Print and return test results

  print("$t: Fail:\n\n$b\n"), ++$e unless $l eq $c;
  print "$t: OK\n"                 if     $l eq $c;

# Approximate location of error

  unless ($l eq $c)
   {for(my $i = 0; $i < length($l); ++$i)
     {if (substr($l, $i, 1) ne substr($c, $i, 1))
       {print "\n\nERROR:\n". substr($l, 0, $i). "<<ERROR>>". substr($l, $i), "\n\n";
        last;
       }
     } 
   }

  $e;
 }

#______________________________________________________________________
# Tests replicating the work of Steffen Muller from CPAN.
#______________________________________________________________________

sub testSM
 {my $e = 0;
  my $t = sub {$e += checkTest($_[0],$_[1],$_[2])};

#______________________________________________________________________
# SM: Test 01
#______________________________________________________________________

   {my ($a, $b, $n, $x) = symbols(qw(a b 10 x));
    &$t('SM01',  [ #---------------------------------------------------
"Differentiate 10**(x**2)) and check for eigenvalue:\n", 
"  A = t**($x**2)      = ", $a = $n**($x**2),             
"  B = (dA/dx)         = ", $b = $a->d, 
"  B/A                 = ", $b/$a, 
"  Should be equal to:   2*$x*log(10) ? ", $b/$a == 2*$x*log($n) ? 'True' : 'FALSE', "\n", 

], << 'END' #----------------------------------------------------------

Differentiate 10**(x**2)) and check for eigenvalue:
  A = t**($x**2)      = exp(log(10)*$x**2)
  B = (dA/dx)         = 2*exp(log(10)*$x**2)*log(10)*$x
  B/A                 = 2*log(10)*$x
  Should be equal to:   2*$x*log(10) ? True
END
); #-------------------------------------------------------------------
   }

#______________________________________________________________________
# SM: Test 02
#______________________________________________________________________

   {my ($a, $b, $c, $x) = symbols(qw(a b c x));
    &$t('SM02',  [ #---------------------------------------------------
"Differentiate (x+c)**2/(x+c)\n", 
"  A =           ", $a = ($x+$c)**2/($x+$c),             
"  B = (dA/dx) = ", $b = $a->d, 
"  Should be equal to: 1 ? ", $b == 1 ? 'True' : 'FALSE', "\n", 

], << 'END' #----------------------------------------------------------

Differentiate (x+c)**2/(x+c)
  A =           $c+$x
  B = (dA/dx) = 1
  Should be equal to: 1 ? True
END
); #-------------------------------------------------------------------
   }

#______________________________________________________________________
# SM: Test 03
#______________________________________________________________________

   {my ($a, $b, $x) = symbols(qw(a b x));
    &$t('SM03',  [ #---------------------------------------------------
"Differentiate log(x*x)\n", 
"  A =           ", $a = log($x*$x),             
"  B = (dA/dx) = ", $b = $a->d, 
"  Should be equal to: 2/$x ? ", $b == 2/$x ? 'True' : 'FALSE', "\n", 

], << 'END' #----------------------------------------------------------
Differentiate log(x*x)
  A =           log($x**2)
  B = (dA/dx) = 2/$x
  Should be equal to: 2/$x ? True
END
); #-------------------------------------------------------------------
   }

#______________________________________________________________________
# SM: Test 04
#______________________________________________________________________

   {my ($a, $b, $x) = symbols(qw(a b x));
    &$t('SM04',  [ #---------------------------------------------------
"Differentiate exp(2*$x) 20 times and check for eigenvalue\n", 
"  A =           ", $a = exp(2*$x),             
"  B = (dA/dx) = ", eval ('$b = $a; $b = $b->d for(1..20)'), $b, 
"  B/A         = ", $b/$a, 
"  Should be equal to: 1048576 ? ", $b/$a == 1048576 ? 'True' : 'FALSE', "\n", 

], << 'END' #----------------------------------------------------------
Differentiate exp(2*$x) 20 times and check for eigenvalue
  A =           exp(2*$x)
  B = (dA/dx) = 1048576*exp(2*$x)
  B/A         = 1048576
  Should be equal to: 1048576 ? True
END
); #-------------------------------------------------------------------
   }

#______________________________________________________________________
# SM: Test 05
#______________________________________________________________________

   {my ($a, $b, $x) = symbols(qw(a b x));
    &$t('SM05',  [ #---------------------------------------------------
"Differentiate exp($x**2) and check for eigenvalue\n", 
"  A =           ", $a = exp(2*$x),             
"  B = (dA/dx) = ", $b = $a->d, 
"  B/A         = ", $b/$a, 
"  Should be equal to: 2 ? ", $b/$a == 2 ? 'True' : 'FALSE', "\n", 

], << 'END' #----------------------------------------------------------
Differentiate exp($x**2) and check for eigenvalue
  A =           exp(2*$x)
  B = (dA/dx) = 2*exp(2*$x)
  B/A         = 2
  Should be equal to: 2 ? True
END
); #-------------------------------------------------------------------
   }

#______________________________________________________________________
# SM: Test 06
#______________________________________________________________________

   {my ($a, $b, $x) = symbols(qw(a b x));
    &$t('SM06',  [ #---------------------------------------------------
"Differentiate x/x+x*x+x+x+x-x\n", 
"  A =           ", $a = $x/$x+$x*$x+$x+$x+$x-$x,             
"  B = (dA/dx) = ", $b = $a->d, 
"  Should be equal to: 2+2*$x ? ", $b == 2+2*$x ? 'True' : 'FALSE', "\n", 

], << 'END' #----------------------------------------------------------
Differentiate x/x+x*x+x+x+x-x
  A =           1+2*$x+$x**2
  B = (dA/dx) = 2+2*$x
  Should be equal to: 2+2*$x ? True
END
); #-------------------------------------------------------------------
   }

#______________________________________________________________________
# SM: Test 07
#______________________________________________________________________

   {my ($a, $b, $c, $n, $x) = symbols(qw(a b c n x));
    &$t('SM07',  [ #---------------------------------------------------

"Differentiate sin(nx)+cos(nx) 4 times and check for eigenvalue:\n", 
"  A = sin(nx)+cos(nx) = ", $a = sin($n*$x) + cos($n*$x), 
"  B = (d/dx)**4 of A  = ", $b = $a->d->d->d->d, 
"  B/A                 = ", $b/$a, 
"  Should be equal to:   $n**4 ? ", $b/$a == $n**4 ? 'True' : 'FALSE', "\n", 

], << 'END' #----------------------------------------------------------

Differentiate sin(nx)+cos(nx) 4 times and check for eigenvalue:
  A = sin(nx)+cos(nx) = 1/2*$i*exp(-$i*$n*$x)-1/2*$i*exp( $i*$n*$x)
                       +1/2*   exp($i*$n*$x) +1/2*   exp(-$i*$n*$x)

  B = (d/dx)**4 of A  = 1/2*$i*exp(-$i*$n*$x)*$n**4-1/2*$i*exp( $i*$n*$x)*$n**4
                       +1/2*   exp( $i*$n*$x)*$n**4+1/2*   exp(-$i*$n*$x)*$n**4

  B/A                 = $n**4
  Should be equal to:   $n**4 ? True

END
); #-------------------------------------------------------------------
   }

#______________________________________________________________________
# SM: Test 08
#______________________________________________________________________

   {my ($a, $b, $x) = symbols(qw(a b x));
    &$t('SM08',  [ #---------------------------------------------------
"Differentiate sinh(2*x) four times and check for eigenvalue\n", 
"  A =           ", $a = sinh(2*$x),             
"  B = (dA/dx) = ", $b = $a->d->d->d->d, 
"  B/A         = ", $b/$a, 
"  Should be equal to: 16 ? ", $b/$a == 16 ? 'True' : 'FALSE', "\n", 

], << 'END' #----------------------------------------------------------
Differentiate sinh(2*x) four times and check for eigenvalue
  A =           1/2*exp(2*$x)-1/2*exp(-2*$x)
  B = (dA/dx) = 8*exp(2*$x)-8*exp(-2*$x)
  B/A         = 16
  Should be equal to: 16 ? True
END
); #-------------------------------------------------------------------
   }

#______________________________________________________________________
# SM: Test 09 - Fail need to recognize sin, cos, sinh etc.
#______________________________________________________________________

   {my ($a, $b, $x) = symbols(qw(a b x));
    &$t('SM09',  [ #---------------------------------------------------
"Differentiate tan(2*x) four times\n", 
"  A =           ", $a = tan(2*$x),             
"  B = (dA/dx) = ", $b = $a->d, 

], << 'END' #----------------------------------------------------------
Differentiate tan(2*x) four times 
  A =           -$i*exp(4*$i*$x)+$i*exp(-2*$i*$x)/(exp(2*$i*$x)+exp(-2*$i*$x))+$i*exp(6*$i*$x)/(exp(2*$i*$x)+exp(-2*$i*$x))

  B = (dA/dx) = 4*exp(4*$i*$x)-2+6/(exp(4*$i*$x)+2+exp(-4*$i*$x))+2*exp(4*$i*$x)/(exp(4*$i*$x)+2+exp(-4*$i*$x))+2*exp(-2*$i*$x)/(exp(2*$i*$x)+exp(-2*$i*$x))-2*exp(8*$i*$x)+6*exp(8*$i*$x)/(exp(4*$i*$x)+2+exp(-4*$i*$x))+2*exp(12*$i*$x)/(exp(4*$i*$x)+2+exp(-4*$i*$x))-6*exp(6*$i*$x)/(exp(2*$i*$x)+exp(-2*$i*$x))

END
); #-------------------------------------------------------------------
   }

#______________________________________________________________________
# SM: Test 10 
#______________________________________________________________________

   {my ($a, $b, $x) = symbols(qw(a b x));
    &$t('SM10',  [ #---------------------------------------------------
"Differentiate 2x+1\n", 
"  A =           ", $a = 2*$x+1,             
"  B = (dA/dx) = ", $b = $a->d, 
"  Should be equal to: 2 ? ", $b == 2 ? 'True' : 'FALSE', "\n", 

], << 'END' #----------------------------------------------------------
Differentiate 2x+1
  A =           1+2*$x
  B = (dA/dx) = 2
  Should be equal to: 2 ? True
END
); #-------------------------------------------------------------------
   }

#______________________________________________________________________
# SM: Test 11
#______________________________________________________________________

   {my ($a, $b, $n, $x) = symbols(qw(a b 10 x));
    &$t('SM11',  [ #---------------------------------------------------
"Differentiate 10**(x**4)\n", 
"  A =           ", $a = 10**($x**4),             
"  B = (dA/dx) = ", $b = $a->d, 

], << 'END' #----------------------------------------------------------
Differentiate 10**(x**4)
  A =           exp(log(10)*$x**4)
  B = (dA/dx) = 4*exp(log(10)*$x**4)*log(10)*$x**3
END
); #-------------------------------------------------------------------
   }
#______________________________________________________________________
# SM: Test 12 - no analog.
# SM: Test 13 - no analog.
# SM: Test 14 - need to revise electronic circuits to understand
# SM: Test 15 - grad operator - no analog yet
# SM: Test 16 - taylor series for a function                - add todo.
# SM: Test 17 - taylor series for a function two dimensions - add todo.
# SM: Test 18 - Matrix determinant                                     
# SM: Test 19 - Unsure what this is doing                              
#______________________________________________________________________

#______________________________________________________________________
# Return error count for this test suite
#______________________________________________________________________

  [$e, 'Steffen Mueller Tests'];
 }

#______________________________________________________________________
# Conics tests.
#______________________________________________________________________

sub testConics
 {my $e = 0;
  my $t = sub {$e += checkTest($_[0],$_[1],$_[2])};

#______________________________________________________________________
# Symbolic algebra.
#______________________________________________________________________

   {my ($a, $b, $x, $y, $R, $f, $i, $o) = symbols(qw(a b x y R f i 1));

    &$t(1,  [ #--------------------------------------------------------

"Algebraic operations:\n\n", 
  sin($x)**2 + cos($x)**2,           # Pythagoras 
  $x**8 - 1,                         # Symbolic multiplication
 ($x**8 - 1) /  ($x**4+1),           # Polynomial division
 ($x**8 - 1) /  ($x-1),                 
 ($x**2 - 1) / (($x-1) * ($x+1)),                        
 ($x + $i)**8,                       # i = sqrt(-1)
  abs(!($x+$y*$i)*!($a+$b*$i)) == 1, # Length of product of units 

], << 'END' #----------------------------------------------------------

Algebraic operations:
  1
  -1+$x**8
  -1+$x**4
  1+$x+$x**2+$x**3+$x**4+$x**5+$x**6+$x**7
  1
  1-8*$i*$x-28*$x**2+56*$i*$x**3+70*$x**4-56*$i*$x**5-28*$x**6+8*$i*$x**7+$x**8
  1

END
);          #----------------------------------------------------------

   }

#______________________________________________________________________
# Ellipse: Focus Trip: Distance from focus to locus to other focus
#______________________________________________________________________

  print "\nConic invariants:\n";

   {my ($a, $b, $x, $y, $z, $R, $f, $i, $o) = symbols(qw(a b x y z R f i 1));

    &$t(2,  [ #--------------------------------------------------------

"Ellipse:\n",
"  Locus:          y=",
      $y = sqrt($R*$R-$f*$f - $x*$x+$f*$f*$x*$x / ($R*$R)),

"  At x=0:         y=",     $y->sub(x=>0),
"  At x=1 f=1 R=2: y=",     $y->sub(x=>1, f=>1, R=>2),
"  at x=R:         y=",     $y->sub(x=>$R), 

"\nFocus trip: distance from focus to locus to other focus =\n",

  $z =  abs($x+$i*$y - $f) + abs($x+$i*$y + $f),
 ($z == 2*$R ? "  Equals" : "  DOES NOT EQUAL"). " 2R\n",

], << 'END' #----------------------------------------------------------

Ellipse:
  Locus:          y=sqrt($R**4-$R**2*$f**2-$R**2*$x**2+$f**2*$x**2)/$R
  At x=0:         y=sqrt($R**4-$R**2*$f**2)/$R
  At x=1 f=1 R=2: y=3/2
  at x=R:         y=0

Focus trip: distance from focus to locus to other focus =
     sqrt($R**4-2*$R**2*$f*$x+$f**2*$x**2)/$R
    +sqrt($R**4+2*$R**2*$f*$x+$f**2*$x**2)/$R
  Equals 2R
END
);          #----------------------------------------------------------
   }
 
#______________________________________________________________________
# Parabola:  Focusing to infinity
#______________________________________________________________________

   {my ($a, $b, $d, $x, $y, $z, $R, $f, $i, $o) = symbols(qw(a b d x y z R f i 1));

    &$t(3,  [ #--------------------------------------------------------

"Parabola: Focussing to infinity\n",
"  From focus to locus:    ",        $a = $x + $i * $x**2 - $i/4,
"  Vertical of same length:",        $b = $i * abs($a),
"  Tangent vector to locus:",        $d =  1 + 2*$x*$i,
"  Compare angles via dot: ",        $z = ($a ^ $d) - ($b ^ $d),
($z == 0 ? "  Focusses to infinity\n"
         : "  DOES NOT FOCUS TO INFINITY\n"),

], << 'END' #----------------------------------------------------------

Parabola: Focussing to infinity
  From focus to locus:      -1/4*$i+$x+$i*$x**2
  Vertical of same length:  $i*sqrt(1/16+1/2*$x**2+$x**4)
  Tangent vector to locus:  1+2*$i*$x
  Compare angles via dot:   1/2*$x-2*sqrt(1/16+1/2*$x**2+$x**4)*$x+2*$x**3
  Focusses to infinity

END
);          #----------------------------------------------------------
   }

#______________________________________________________________________
# Parabola: Distance from focus to locus to directrix
#______________________________________________________________________

   {my ($a, $b, $A, $B, $x, $y, $R, $f, $i, $o) = symbols(qw(a b A B x y R f i 1));

    &$t(4,  [ #--------------------------------------------------------

"Parabola:  Distance from focus to locus to directrix\n",
"  From focus to locus:            ",      $a = $x + $i * $x**2 - $i/4,
"  From focus to locus squared:    ",      $A = $a^$a,
"  From locus to directrix squared:",      $B = ($x**2+'1/4')**2, 

($A == $B ? "  Equal lengths\n" : "  UNEQUAL LENGTHS\n"),

], << 'END' #----------------------------------------------------------

Parabola:  Distance from focus to locus to directrix
  From focus to locus:              -1/4*$i+$x+$i*$x**2
  From focus to locus squared:      1/16+1/2*$x**2+$x**4
  From locus to directrix squared:  1/16+1/2*$x**2+$x**4
  Equal lengths

END
);          #----------------------------------------------------------
   }

#______________________________________________________________________
# Hyperbola: Constant difference between distances from focii to locus.
#______________________________________________________________________

   {my ($a, $b, $A, $B, $f1, $f2, $x, $y, $R, $f, $i, $o) = symbols(qw(a b A B f1 f2 x y R f i 1));

    &$t(5,  [ #--------------------------------------------------------

"Hyperbola:  Constant difference between distances from focii to locus of y=1/x\n",
"  Assume by symmetry the focii are on\n",
"    the line y=x:                    ",   $f1 = $x + $i * $x,
"    and equidistant from the origin: ",   $f2 = -$f1,
"\n  Choose a convenient point on y=1/x:", $a = $o+$i,
"    and another point:               ",   $b = $y+$i/$y,
"\n  Difference in distances from focii\n",
"    From first point:                ",   $A = abs($a - $f2) - abs($a - $f1),  
"    From second point:               ",   $B = abs($b - $f2) + abs($b - $f1),
"\n  Assuming the difference is constant,\n",
"    and solving for x, we get:       x=", ($A eq $B)->solve(qw(x)),                        
"\n  Which is indeed constant, as was to be demonstrated\n",                                                

], << 'END' #----------------------------------------------------------

Hyperbola:  Constant difference between distances from focii to locus of y=1/x
  Assume by symmetry the focii are on
    the line y=x:                       $x+$i*$x
    and equidistant from the origin:   -$x-$i*$x

  Choose a convenient point on y=1/x:  1+$i
    and another point:                 $y+$i/$y

  Difference in distances from focii
    From first point:                  sqrt(2+4*$x+2*$x**2)
                                      -sqrt(2-4*$x+2*$x**2)

    From second point:
      sqrt(2*$x**2*$y**2+2*$x*$y+2*$x*$y**3+1+$y**4)/$y
     +sqrt(2*$x**2*$y**2-2*$x*$y-2*$x*$y**3+1+$y**4)/$y

  Assuming the difference is constant,
    and solving for x, we get:       x=sqrt(2)

  Which is indeed constant, as was to be demonstrated
END
);          #----------------------------------------------------------
   }

#______________________________________________________________________
# Return error count for this test suite
#______________________________________________________________________

  [$e, 'Conic Tests'];
 }

#______________________________________________________________________
# Tests collected together.
#______________________________________________________________________

sub test()
 {my @e;
# import('symbols', BigInt=>1);
  push @e, testSM();
  push @e, testGeneral();
  push @e, testConics();
  push @e, testEllipse();

  my $n = 0;
  for my $e(@e)
   {my ($c, $m) = @$e;
    print "OK:   $m\n"                 unless $c; 
    print "FAIL: $c error(s) in: $m\n" if     $c;
    $n += $c;
   }
  print STDERR "No Errors\n"           unless $n;
  print STDERR "DANGER: $n error(s)\n" if     $n;
  $n; 
 }

#______________________________________________________________________
# Write to a file.
#______________________________________________________________________

sub writeFile($$)
 {my $f = shift; # File to write to
  my $t = shift; # Text to be written
  my $o;

  open  $o, ">i/$f";
  print $o $t;
  close $o;
 }

#______________________________________________________________________
# Set up install.
#______________________________________________________________________

sub install()
 {my $package = 'Math::Algebra::Symbols';

#______________________________________________________________________
# Create documentation.
#______________________________________________________________________
 
  print `mkdir i` unless -e 'i';
  print `rm -vr i/*`;
  print `pod2html.bat --infile=symbols.pm --outfile=symbols.html`;
  print `pod2html.bat --infile=symbols.pm --outfile=i/symbols.html`;

#______________________________________________________________________
# Make file.
#______________________________________________________________________
 
   writeFile("Makefile.PL", << "END");
use ExtUtils::MakeMaker;

WriteMakefile
 (NAME		=> '$package',
  VERSION	=> '$symbols::VERSION',	
  ABSTRACT=> 'Symbolic Manipulation using Perl',
  AUTHOR 	=> 'PhilipRBrenan\@yahoo.com',
 );
END

#______________________________________________________________________
# test.pl
#______________________________________________________________________

  writeFile("test.pl", <<'END');
use Math::Algebra::Symbols;

$x = symbols(qw(x));

$x->test();
END

#______________________________________________________________________
# Copy and edit source files.
#______________________________________________________________________

  for my $f([qw(symbols.pm Symbols.pm)], [qw(i/test.pl test.pl)])
   {my ($if, $of) = @$f;
    my ($i,  $o);

    open $i, "<$if";
    my @l = <$i>;
    close $i;

    for (@l)
     {s/^package symbols/package $package/;
      s/^use symbols/use $package/;
      s/^ use symbols/ use $package/;
     }
 
    open  $o, ">i/$of";
    print $o join('', @l);
    close $o;
   }

#______________________________________________________________________
# README
#______________________________________________________________________

  writeFile("README", <<'END');
Math::Algebra::Symbols - Symbolic Algebra using Perl.

Copyright Philip R Brenan, 2004

This package supplies a set of functions and operators to manipulate
Perl expressions algebraically:

 use Math::Algebra::Symbols hyper=>1;

 ($n, $x, $y) = symbols(qw(n x y));

 $a = sin($x)**2 + cos($x)**2; 
 $b = ($x**8-1) / ($x-1);
 $c = (sin($n*$x)+cos($n*$x))->d->d->d->d/(sin($n*$x)+cos($n*$x));
 $d = tanh($x+$y)==(tanh($x)+tanh($y))/(1+tanh($x)*tanh($y));

 print "$a\n$b\n$c\n$d\n";

 # 1                                        
 # 1+$x+$x**2+$x**3+$x**4+$x**5+$x**6+$x**7
 # $n**4                                   
 # 1  

This program is free software; you can redistribute it and/or modify it
under the same terms as Perl itself. 

This is alpha code. It is written in pure Perl. It uses the standard
Perl install mechanism. Documentation and Examples in pod at end of
module.

I believe that we should try to capture all known Mathematics
symbolically in Perl. Indeed, can you say that you know any Mathematics
at all if you cannot explain it in Perl?

Help with this project would be appreciated.

For bug reports or suggestions please send email to:
philiprbrenan@yahoo.com

END

#______________________________________________________________________
# TODO
#______________________________________________________________________

  writeFile("TODO", <<'END');

Recognize sin, cos, sinh, cosh etc. in expressions involving exp.
Sigma,Product
Taylor series
Integrals
Fourier
Laplace
Groups
Sets
Graphing using Tk.

END

#______________________________________________________________________
# CHANGES
#______________________________________________________________________

  writeFile("CHANGES", <<'END');

2004/03/14 Fixed power() so that it recognizes constant powers. Added
TODO List. Finished testSM(): new requirements in TODO.

2004/03/13 Added change log on esteemed advice of Steffen Müller. Made
yet another attempt to stop polynomialDivide() from producing an
infinite series as a representation of a single term. Most of
mathematics seems to erupt from the division of one polynomial by
another.

I am carefully studying SM's work. Started testSM() to see whether I can
reproduce his results.  Have reached test11.

END

#______________________________________________________________________
# Manifest.
#______________________________________________________________________

  writeFile("MANIFEST", <<'END');
Makefile.PL
Symbols.pm
symbols.html
test.pl
README
CHANGES
TODO   
MANIFEST
END

#______________________________________________________________________
# Create distribution.
#______________________________________________________________________

  `rm *.x~~ symbols.htmlpod.pl`;
  print << "END";
Goto directory ./i under cygwin and run:
  perl Makefile.PL
  make
  make test
  make dist
END
 }

#______________________________________________________________________
# Perform tests or install if necessary
#______________________________________________________________________

unless (caller())
 {unless (scalar(@ARGV))
   {test() unless caller();
   }
  else 
   {for(;my $p = shift(@ARGV);)
     {&install() if $p =~ /install/i;
      &testSM()  if $p =~ /steffen|mueller/i;
     }
   }
 }

#______________________________________________________________________
# Package installed successfully.
#______________________________________________________________________

1;
 
__END__

#______________________________________________________________________
# User guide.
#______________________________________________________________________

=head1 NAME

Math::Algebra::Symbols - Symbolic Algebra using Perl

=head1 SYNOPSIS

 use Math::Algebra::Symbols hyper=>1;

 ($n, $x, $y) = symbols(qw(n x y));

 $a = sin($x)**2 + cos($x)**2; 
 $b = ($x**8-1) / ($x-1);
 $c = (sin($n*$x)+cos($n*$x))->d->d->d->d/(sin($n*$x)+cos($n*$x));
 $d = tanh($x+$y)==(tanh($x)+tanh($y))/(1+tanh($x)*tanh($y));

 print "$a\n$b\n$c\n$d\n";

 # 1                                        
 # 1+$x+$x**2+$x**3+$x**4+$x**5+$x**6+$x**7
 # $n**4                                   
 # 1                                        

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

If you wish to use symbols constructed with big integers from L<Math::BigInt>:

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

=head4 Relational operator: B<==> 

 use Math::Algebra::Symbols;

 ($x, $y) = symbols(qw(x y));

 $z = ($x**2-$y**2)/($x+$y) == $x - $y;

 print "$z\n";

 # 1

The relational equality operator B<==> compares two symbolic expressions
and returns TRUE(1) or FALSE(0) accordingly.

=head4 Relational operator: B<eq> 

 use Math::Algebra::Symbols;

 ($x, $v, $t) = symbols(qw(x v t));

 $z = ($v eq $x / $t)->solve(qw(x in terms of v t));

 print "x=$z\n";

 # x=$v*$t

The relational operator B<eq> is in fact a synonym for the minus B<->
operator, with the expectation that later on the L<solve()|/Solving equations>
function will be used to simplify and rearrange the equation.

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

=head4 Simplifying equations: B<sub()>

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
acuracy, however:

 $e3 =~ /^(\d+)\/(\d+)$/;
 $result = $1/$2;

or similar will produce approximate results.

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

=head3 Methods for performing Calculus

=head4 Differentiation: B<d()>

 use Math::Algebra::Symbols;

 ($x, $i) = S(qw(x i));

 $z = exp($x)->d->d('x')->d($x)->d();

 print "$z\n";

 # exp($x)

B<d()> differentiates the equation on the left hand side by the named
variable.

The variable to be differentiated by may be explicitly specifed,
either as a string or as single symbol; or it may be heuristically
guessed as follows:

=over

If the equation to be differentiated refers to only one symbol, then
that symbol is used. If several symbols are present in the equation, but
only one of B<t>, B<x>, B<y>, B<z> is present, then that variable is
used in honor of Newton, Leibnitz, Cauchy.

=back

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
 "\n\n  Solving for x we get:            x=", ($A eq $B)->solve(qw(x)),
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

 use Maths::Algebra::Symbols symbols=>'S', BigInt=>0, trig=>1 hyper=>1,
   complex=>1;

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

=head1 AUTHOR

Philip R Brenan at B<philiprbrenan@yahoo.com>

=cut
#:folding=indent:
