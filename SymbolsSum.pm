#!perl -w
#_ Sum __________________________________________________________________
# Symbolic algebra: sums.
# Perl License.
# PhilipRBrenan@yahoo.com, 2004.
#________________________________________________________________________

package Math::Algebra::SymbolsSum;
$VERSION = 1.11;

use Math::Algebra::SymbolsTerm;
use IO::Handle;
use Carp;
use Hash::Util qw(lock_hash);
sub factorize($); 

#_ Sum __________________________________________________________________
# Constructer
#________________________________________________________________________

sub new
 {bless {t=>{}};
 }

#_ Sum __________________________________________________________________
# New from String
#________________________________________________________________________

sub newFromString($)
 {my ($a) = @_;
  return $zero unless $a;
  $a .='+';
  my @a = $a =~ /(.+?)[\+\-]/g;
  my @t = map {term($_)} @a;
  sigma(@t);
 }

#_ Sum __________________________________________________________________
# New from Strings
#________________________________________________________________________

sub n(@)
 {return $zero unless @_;
  my @a = map {newFromString($_)} @_;
  return @a if wantarray;
  $a[0];
 }

#_ Sum __________________________________________________________________
# Confirm type
#________________________________________________________________________

sub isSum($) {1}; 

#_ Sum __________________________________________________________________
# Get list of terms from existing sum
#________________________________________________________________________

sub t($)
 {my ($a) = @_;
  (map {$a->{t}{$_}} sort(keys(%{$a->{t}})));
 }

#_ Sum __________________________________________________________________
# Count terms in sum              
#________________________________________________________________________

sub count($)
 {my ($a) = @_;
  scalar(keys(%{$a->{t}}));
 }

#_ Sum __________________________________________________________________
# Get the single term from a sum containing just one term
#________________________________________________________________________

sub st($)
 {my ($a) = @_;
  return (values(%{$a->{t}}))[0] if scalar(keys(%{$a->{t}})) == 1;
  undef;
 }

#_ Sum __________________________________________________________________
# Create a sum from a list of terms.  Cannot be called as a method.
#________________________________________________________________________

sub sigma(@)
 {return $zero unless scalar(@_);
  my $z = new();
  for my $t(@_)
   {my $s = $t->signature;
    if (exists($z->{t}{$s}))
     {my $a = $z->{t}{$s}->add($t);
      if ($a->c == 0) 
       {delete $z->{t}{$s};
       }
      else
       {$z->{t}{$s} = $a;
       }
     }
    else
     {$z->{t}{$s} = $t
     }
   }
  $z->z;
 }

#_ Sum __________________________________________________________________
# Negate: multiply each term in a sum by -1
#________________________________________________________________________

sub negate($)
 {my ($s) = @_;
  my  @t;
  for my $t($s->t)
   {push @t, $t->clone->timesInt(-1)->z;
   }
  sigma(@t);
 }

#_ Sum __________________________________________________________________
# Add two sums together to make a new sum
#________________________________________________________________________

sub add($$)
 {my ($a, $b) = @_;
  sigma($a->t, $b->t);
 }

#_ Sum __________________________________________________________________
# Subtract one sum from another
#________________________________________________________________________

sub subtract($$)
 {my ($a, $b) = @_;
  return $b->negate if $a->{id} == $zero->{id};
  $a->add($b->negate);
 }

#_ Sum __________________________________________________________________
# Conditional multiply
#________________________________________________________________________

sub multiplyC($$)
 {my ($a, $b) = @_;
  return $a unless defined($b);
  return $b unless defined($a);
  $a->multiply($b);
 }

#_ Sum __________________________________________________________________
# Multiply two sums together to make a new sum
#________________________________________________________________________

my %M; # Memoize multiplication

sub multiply($$)
 {my ($A, $B) = @_;

  my $m = $M{$A->{id}}{$B->{id}}; return $m if defined($m);

  return $A if $A->{id} == $zero->{id} or $B->{id} == $one->{id};
  return $B if $B->{id} == $zero->{id} or $A->{id} == $one->{id};

  my @t;

# Check for divides that match multiplier
  my @a = $A->t;
  for my $a(@a)
   {my $d = $a->Divide;
    next unless $d;
    if ($d->{id} == $B->{id})
     {push @t, $a->removeDivide;
      $a = undef;
     }
   }

  my @b = $B->t;
  for my $b(@b)
   {my $d = $b->Divide;
    next unless $d;
    if ($d->{id} == $A->{id})
     {push @t, $b->removeDivide;
      $b = undef;
     }
   }

# Simple multiply
  for   my $aa(@a)
   {next unless $aa;
    for my $bb(@b)
     {next unless $bb;
      my $m = $aa->multiply($bb);
      push (@t, $m), next if $m;

# Complicated multiply
      my %a = $aa->split; my %b = $bb->split;
      my $a = $a{t};      my $b = $b{t};

# Sqrt  
      my $s = 0;
         $s = $a{s} if $a{s} and $b{s} and $a{s}->{id} == $b{s}->{id}; # Equal sqrts  
      $a->Sqrt(multiplyC($a{s}, $b{s}))     unless $s;

# Divide
      $a->Divide(multiplyC($a{d}, $b{d}))   if $a{d} or  $b{d};

# Exp    
      $a->Exp($a{e} ? $a{e} : $b{e})        if $a{e} xor $b{e};
      my $e = 0;
      if ($a{e} and $b{e})
       {my $s = $a{e}->add($b{e});
        $e = $s->st;
        $e = $e->exp2 if     $e;
        $a->Exp($s)   unless $e;
       }
# Log    
      $a->Log($a{l} ? $a{l} : $b{l})        if $a{l} xor $b{l};
      die "Cannot multiply logs yet"        if $a{l} and $b{l};

# Combine results
      $a = $a->z;
      $b = $b->z;
      $a = $a->multiply($b);
      $a = $a->multiply($e) if $e;
      $a or die "Bad multiply";
     
      push @t, $a                         unless $s;
      push @t, sigma($a)->multiply($s)->t if     $s;
     }
   }
# Result  
  my $C = sigma(@t);
  $M{$A->{id}}{$B->{id}} = $C;
  $C;
 }

#_ Sum __________________________________________________________________
# Divide one sum by another
#________________________________________________________________________

sub divide($$)
 {my ($A, $B) = @_;

  $B->{id} == $zero->{id} and croak "Cannot divide by zero";
  return $zero      if $A->{id} == $zero->{id};
  return $A         if $B->{id} == $one->{id};
  return $A->negate if $B->{id} == $mOne->{id};

# Divide term by term
  my $a = $A->st; my $b = $B->st;
  if (defined($a) and defined($b))
   {my $c = $a->divide2($b);
    return sigma($c) if $c;
   } 

# Divide sum by term
  elsif ($b)
   {ST: for(1..1)
     {my @t;
      for my $t($A->t)
       {my $c = $t->divide2($b);
        last ST unless $c;
        push @t, $c;
       }
      return sigma(@t);
     }
   }

# Divide sum by sum

  my @t;
  for   my $aa($A->t)
   {my $a = $aa->clone;
    my $d = $a->Divide;
    $a->Divide($d->multiply($B)) if     $d;
    $a->Divide($B)               unless $d;
    push @t, $a->z;
   }

# Result  
  sigma(@t);
 }

#______________________________________________________________________
# Make an integer
#______________________________________________________________________

sub makeInt($)
 {sigma(term()->one->clone->c(shift())->z)
 }

#______________________________________________________________________
# Substitute.
#______________________________________________________________________

sub sub($@)
 {my $E = shift();
  my @R = @_;
  my $Z = $zero;

# Each replacement
  for(;@R > 0;)
   {my $s = shift @R; # Replace this variable
    my $w = shift @R; # With this expression

    $s =~ /^[a-z]+$/i or croak "Can only substitute an expression for a variable, not $s";
    $w->isSum;

# Each expression
    for my $t($E->t)
     {my $n = $t->vp($s);
      my %t = $t->split;
      my $S = sigma($t{t}->vp($s, 0)->z);  # Remove substitution variable
      $S = $S->multiply(($t{s}->sub(@_))->Sqrt) if defined($t{s}); 
      $S = $S->divide   ($t{d}->sub(@_))        if defined($t{d}); 
      $S = $S->multiply(($t{e}->sub(@_))->Exp)  if defined($t{e}); 
      $S = $S->multiply(($t{l}->sub(@_))->Log)  if defined($t{l}); 
      $S = $S->multiply($w->power(makeInt($n))) if $n;
      $Z = $Z->add($S);
     }
   }
# Result
  $Z;
 }

#_ Sum __________________________________________________________________
# Check whether one sum is equal to another after multiplying out all
# divides and divisors.
#________________________________________________________________________

#sub isEqual($$)
# {my ($A, $B) = @_;
sub isEqual($)
 {my ($C) = @_;

# Until there are no more divides
  for(;;)
   {my (%c, $D, $N); $N = 0;

# Most frequent divisor 
#   for my $t($A->t, $B->t)
    for my $t($C->t)
     {my $d = $t->Divide;
      next unless $d;
      my $s = $d->getSignature;
      if (++$c{$s} > $N)
       {$N = $c{$s};
        $D = $d;
       }
     }
    last unless $N;
#   $A = $A->multiply($D);
#   $B = $B->multiply($D);
    $C = $C->multiply($D);
   }

# Until there are no more negative powers
  for(;;)
   {my %v;
#   for my $t($A->t, $B->t)
    for my $t($C->t)
     {for my $v($t->v)
       {my $p = $t->vp($v);
        next unless $p < 0;
        $p = -$p; 
        $v{$v} = $p if !defined($v{$v}) or $v{$v} < $p;
       }
     }
    last unless scalar(keys(%v));
    my $m = term()->one->clone;
    $m->vp($_, $v{$_}) for keys(%v);
    my $M = sigma($m->z);
#   $A = $A->multiply($M); 
#   $B = $B->multiply($M);
    $C = $C->multiply($M); 
   }

# Result
# my $z = $A->{id} == $B->{id};
# $z;
  $C;
 }

#_ Sum __________________________________________________________________
# Normalize sqrts in a sum.
#________________________________________________________________________

sub normalizeSqrts($)
 {my ($s) = @_;
  my (@t, @s);

# Find terms with single simple sqrts that can be normalized.
  for my $t($s->t)
   {push @t, $t;
    my $S  = $t->Sqrt; next unless $S;    # Check for sqrt
    my $St = $S->st;   next unless $St;   # Check for single term sqrt
    
    my %T = $St->split;                   # Split single term sqrt
    next if $T{s} or $T{d} or $T{e} or $T{l};
    pop  @t;
    push @s, {t=>$t, s=>$T{t}->z};        # Sqrt with simple single term
   }
# Already normalized unless there are several such terms
  return $s unless scalar(@s) > 1; 

# Remove divisor for each normalized term  
  for my $r(@s)
   {my $d = $r->{t}->d; next unless $d > 1; 
    for my $s(@s)
     {$s->{t} = $s->{t}->clone->divideInt($d)   ->z;
      $s->{s} = $s->{s}->clone->timesInt ($d*$d)->z;
     }
   }

# Eliminate duplicate squared factors
  for my $s(@s)
   {my $F = factorize($s->{s}->c);
    my $p = 1;
    for my $f(keys(%$F))
     {$p *= $f**(int($F->{$f}/2)) if $F->{$f} > 1;
     }
    $s->{t} = $s->{t}->clone->timesInt ($p)   ->z;
    $s->{s} = $s->{s}->clone->divideInt($p*$p)->z;

    if ($s->{s}->isOne)
     {push @t, $s->{t}->removeSqrt;
     }
    else
     {push @t, $s->{t}->clone->Sqrt($s->{$s})->z;
     }
   }
# Result
  sigma(@t);
 }

#_ Sum __________________________________________________________________
# Check whether one sum is equal to another after multiplying out sqrts.
#________________________________________________________________________

#sub isEqualSqrt($$)
# {my ($A, $B) = @_;
#  my $C = $A->subtract($B);  # Set to zero 
sub isEqualSqrt($)
 {my ($C) = @_;

#______________________________________________________________________
# Each sqrt
#______________________________________________________________________

  for(1..99)
   {$C = $C->normalizeSqrts;
    my @s = grep { defined($_->Sqrt)} $C->t;
    my @n = grep {!defined($_->Sqrt)} $C->t;
    last unless scalar(@s) > 0;

#______________________________________________________________________
# Partition by square roots.
#______________________________________________________________________

    my %S = ();
    for my $t(@s)
     {my $s = $t->Sqrt;
      my $S = $s->signature;
      push @{$S{$S}}, $t;
     }

#______________________________________________________________________
# Square each partitions, as required by the formulae below.
#______________________________________________________________________

    my @t;
    push @t, sigma(@n)->power($two) if scalar(@n);  # Non sqrt partition 
    for my $s(keys(%S))
     {push @t, sigma(@{$S{$s}})->power($two);       # Sqrt parition
     }

#______________________________________________________________________
# I can multiply out upto 4 square roots using the formulae below.     
# There are formula to multiply out more than 4 sqrts, but they are big.
# These formulae are obtained by squaring out and rearranging:
# sqrt(a)+sqrt(b)+sqrt(c)+sqrt(d) == 0 until no sqrts remain, and
# then matching terms to produce optimal execution.
#______________________________________________________________________
   
    my $ns = scalar(@t);
    $ns < 5 or die "There are $ns square roots present.  I can handle less than 5";

    my ($a, $b, $c, $d) = @t;

    if    ($ns == 1)
     {$C = $a;
     }
    elsif ($ns == 2)
     {$C = $a-$b;
     }
    elsif ($ns == 3)
     {$C = -$a**2+2*$a*$b-$b**2+2*$c*$a+2*$c*$b-$c**2;
     }
    elsif ($ns == 4)
     {my $a2  = $a  * $a;
      my $a3  = $a2 * $a;  
      my $a4  = $a3 * $a;  
      my $b2  = $b  * $b;
      my $b3  = $b2 * $b;  
      my $b4  = $b3 * $b;  
      my $c2  = $c  * $c;
      my $c3  = $c2 * $c;  
      my $c4  = $c3 * $c;  
      my $d2  = $d  * $d;
      my $d3  = $d2 * $d;  
      my $d4  = $d3 * $d;
      my $bpd = $b  + $d;  
      my $bpc = $b  + $c;  
      my $cpd = $c  + $d;  
      $C =
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

#_ Sum __________________________________________________________________
# Test result
#________________________________________________________________________

# $C->isEqual($zero);
  $C;
 }

#_ Sum __________________________________________________________________
# Transform a sum assuming that it is equal to zero
#________________________________________________________________________

sub isZero($)
 {my ($C) = @_;
  $C->isEqualSqrt->isEqual;                  
 }

#_ Sum __________________________________________________________________
# n: 2**n == N or undef 
#________________________________________________________________________

sub powerof2($)
 {my ($N) = @_;
  my $n   = 0;
  return undef unless $N > 0;
  for (;;)
   {return $n    if     $N     == 1;        
    return undef unless $N % 2 == 0;
    ++$n;  $N /= 2;
   }
 }

#_ Sum __________________________________________________________________
# Solve an equation known to be equal to zero for a specified variable. 
#________________________________________________________________________

sub solve($$)
 {my ($A, @x) = @_;
  croak 'Need variable to solve for' unless scalar(@x) > 0;
  my $x = $x[0];
  my %x; $x{$_} = 1 for @x;
  
  $B = $A->isZero;  # Eliminate sqrts and negative powers

# Strike all terms with free variables other than x: i.e. not and not one of the named constants
  my @t = ();
  for my $t($B->t)
   {my @v = $t->v;
    push @t, $t;
    for my $v($t->v)
     {next if exists($x{$v});
      pop @t;
      last;
     } 
   }
  my $C = sigma(@t);
                                                                
# Find highest and lowest power of x
  my $n = 0; my $N;
  for my $t($C->t)
   {my $p = $t->vp($x);
    $n = $p if $p > $n;
    $N = $p if !defined($N) or $p < $N;
   }
  my $D  = $C;
     $D  = $D->multiply(sigma(term()->one->clone->vp($x, -$N)->z)) if $N;
     $n -= $N if $N;
                                                                
# Find number of terms in x
  my $c = 0; 
  for my $t($D->t)
   {++$c if $t->vp($x) > 0;
   }
  
  $n == 0             and croak "Equation not dependant on $x, so cannot solve for $x";
  $n  > 4 and $c > 1  and croak "Unable to solve polynomial or power $n > 4 in $x (Galois)";
 ($n  > 2 and $c > 1) and die   "Need solver for polynomial of degree $n in $x";

# Solve linear equation
  if ($n == 1 or $c == 1)
   {my (@c, @v);
    for my $t($D->t)
     {push(@c, $t), next if $t->vp($x) == 0; # Constants
      push @v, $t;                           # Powers of x 
     }
    my $d = sigma(@v)->multiply(sigma(term()->one->clone->vp($x, -$n)->negate->z));
       $D = sigma(@c)->divide($d);

    return $D if $n == 1;

    my $p = powerof2($n);
    $p or croak "Fractional power 1/$n of $x unconstructable by sqrt";
       $D = $D->Sqrt for(1..$p);
    return $D;
   }

# Solve quadratic equation
  if ($n == 2)
   {my @c = ($one, $one, $one);
    $c[$_->vp($x)] = $_ for $D->t;
    $_ = sigma($_->clone->vp($x, 0)->z) for (@c);
    my ($c, $b, $a) = @c;
    return 
     [ (-$b->add     (($b->power($two)->subtract($four->multiply($a)->multiply($c)))->Sqrt))->divide($two->multiply($a)),
       (-$b->subtract(($b->power($two)->subtract($four->multiply($a)->multiply($c)))->Sqrt))->divide($two->multiply($a))
     ] 
   }

# Check that it works

# my $yy = $e->sub($x=>$xx);
# $yy == 0 or die "Proposed solution \$$x=$xx does not zero equation $e";
# $xx; 
 }                   

#_ Sum __________________________________________________________________
# Power
#________________________________________________________________________

sub power($$) 
 {my ($a, $b) = @_;

  return $one                   if $b->{id} == $zero->{id};
  return $a->multiply($a)       if $b->{id} == $two->{id};
  return $a                     if $b->{id} == $one->{id};
  return $one->divide($a)       if $b->{id} == $mOne->{id};
  return $a->sqrt               if $b->{id} == $half->{id};
  return $one->divide($a->sqrt) if $b->{id} == $mHalf->{id};

  my $T = $b->st;
  $T or croak "Power by expression too complicated";

  my %t = $T->split;
  croak "Power by term too complicated" if $t{s} or $t{d} or $t{e} or $t{l};

  my $t = $t{t};
  $t->i == 0 or croak "Complex power not allowed yet";

  my ($p, $d) = ($t->c, $t->d); 
  $d == 1 or $d == 2 or croak "Fractional power other than /2 not allowed yet";

  $a = $a->sqrt if $d == 2;

  return $one->divide($a)->power(sigma(term()->c($p)->z)) if $p < 0;

  $p = abs($p);
  my $r = $a; $r = $r->multiply($a) for (2..$p);
  $r;   
 }

#_ Sum __________________________________________________________________
# Differentiate.
#________________________________________________________________________

sub d($;$);
sub d($;$)
 {my $c = $_[0];  # Differentiate this expression 
  my $b = $_[1];  # With this variable

#_ Sum __________________________________________________________________
# Get differentrix. Assume 'x', 'y', 'z' or 't' if appropriate.
#________________________________________________________________________

  if (defined($b))
   {if (!ref $b)
     {$b =~ /^[a-z]+$/i or croak "Cannot differentiate by '$b'";
     }
    elsif (ref $b eq __PACKAGE__)
     {my $t = $b->st; $t              or die "Cannot differentiate by multiple terms";
      my @b = $t->v;  scalar(@b) == 1 or die "Can only differentiate by one variable";
      my $p = $t->vp($b[0]);  $p == 1 or die "Can only differentiate by variable to power 1";
      $b = $b[0];
     }
    else 
     {die "Cannot differentiate by $b";
     }
   }
  else    
   {my %b;
    for my $t($c->t)
     {my %b; $b{$_}++ for ($t->v);
     }      
    my $i = 0; my $n = scalar(keys(%b));
    ++$i, $b = 'x'     if $n == 0; # Constant expression anyway
    ++$i, $b = (%b)[0] if $n == 1;
    for my $v(qw(t x y z)) 
     {++$i, $b = 't' if $n  > 1 and exists($b{$v});
     }
    $i  == 1 or croak "Please specify a single variable to differentiate by";
   }

#_ Sum __________________________________________________________________
# Each term
#________________________________________________________________________

  my @t = ();
  for my $t($c->t)
   {my %V = $t->split;
    my $T = $V{t}->z->clone->z;
    my ($S, $D, $E, $L) = @V{qw(s d e l)};
    my $s = $S->d($b) if $S;    
    my $d = $D->d($b) if $D;      
    my $e = $E->d($b) if $E;  
    my $l = $L->d($b) if $L;  

#_ Sum __________________________________________________________________
# Differentiate Variables: A*v**n->d == A*n*v**(n-1)
#________________________________________________________________________

     {my $v = $T->clone;
      my $p = $v->vp($b);
      if ($p != 0)
       {$v->timesInt($p)->vp($b, $p-1);
        $v->Sqrt  ($S) if $S;
        $v->Divide($D) if $D;
        $v->Exp   ($E) if $E;
        $v->Log   ($L) if $L;
        push @t, $v->z;
       }
     }

#_ Sum __________________________________________________________________
# Differentiate Sqrt: A*sqrt(F(x))->d == 1/2*A*f(x)/sqrt(F(x))
#________________________________________________________________________

    if ($S)
     {my $v = $T->clone->divideInt(2);
      $v->Divide($D) if $D;
      $v->Exp   ($E) if $E;
      $v->Log   ($L) if $L;
      push @t, sigma($v->z)->multiply($s)->divide($S->Sqrt)->t;
     }

#_ Sum __________________________________________________________________
# Differentiate Divide: A/F(x)->d == -A*f(x)/F(x)**2
#________________________________________________________________________

    if ($D)
     {my $v = $T->clone->negate;
      $v->Sqrt($S) if $S;
      $v->Exp ($E) if $E;
      $v->Log ($L) if $L;
      push @t, sigma($v->z)->multiply($d)->divide($D->multiply($D))->t;
     }

#_ Sum __________________________________________________________________
# Differentiate Exp: A*exp(F(x))->d == A*f(x)*exp(F(x))
#________________________________________________________________________

    if ($E)
     {my $v = $T->clone;
      $v->Sqrt  ($S) if $S;
      $v->Divide($D) if $D;
      $v->Exp   ($E);
      $v->Log   ($L) if $L;
      push @t, sigma($v->z)->multiply($e)->t;
     }

#_ Sum __________________________________________________________________
# Differentiate Log: A*log(F(x))->d == A*f(x)/F(x)
#________________________________________________________________________

    if ($L)
     {my $v = $T->clone;
      $v->Sqrt  ($S) if $S;
      $v->Divide($D) if $D;
      $v->Exp   ($E) if $E;
      push @t, sigma($v->z)->multiply($l)->divide($L)->t;
     }
   }

#_ Sum __________________________________________________________________
# Result
#________________________________________________________________________

  sigma(@t);
 }

#_ Sum __________________________________________________________________
# Sqrt
#________________________________________________________________________

sub Sqrt($) 
 {my ($x) = @_;
  my $s = $x->st;
  if (defined($s))
   {my $r = $s->sqrt2;
    return sigma($r) if defined($r);
   }

  sigma(term()->c(1)->Sqrt($x)->z);
 }

#_ Sum __________________________________________________________________
# Exp
#________________________________________________________________________

sub Exp($) 
 {my ($x) = @_;
  my $p = term()->one;
  my @r;
  for my $t($x->t)
   {my $r = $t->exp2;
    $p = $p->multiply($r) if     $r;
    push @r, $t           unless $r;
   }
  return sigma($p) if scalar(@r) == 0;
  return sigma($p->clone->Exp(sigma(@r))->z);
 }

#_ Sum __________________________________________________________________
# Log
#________________________________________________________________________

sub Log($) 
 {my ($x) = @_;
  my $s = $x->st;
  if (defined($s))
   {my $r = $s->log2;
    return sigma($r) if defined($r);
   }

  sigma(term()->c(1)->Log($x)->z);
 }

#_ Sum __________________________________________________________________
# Sine
#________________________________________________________________________

sub Sin($) 
 {my ($x) = @_;
  my $s = $x->st;
  if (defined($s))
   {my $r = $s->sin2;
    return sigma($r) if defined($r);
   }

  my $a = $i->multiply($x);
  $i->multiply($half)->multiply($a->negate->Exp->subtract($a->Exp));
 }

#_ Sum __________________________________________________________________
# Cosine
#________________________________________________________________________

sub Cos($) 
 {my ($x) = @_;
  my $s = $x->st;
  if (defined($s))
   {my $r = $s->cos2;
    return sigma($r) if defined($r);
   }

  my $a = $i->multiply($x);
  $half->multiply($a->negate->Exp->add($a->Exp));
 }

#_ Sum __________________________________________________________________
# Tan, Sec, Csc, Cot
#________________________________________________________________________

sub tan($) {my ($x) = @_; $x->Sin()->divide($x->Cos())}
sub sec($) {my ($x) = @_; $one     ->divide($x->Cos())}
sub csc($) {my ($x) = @_; $one     ->divide($x->Sin())}
sub cot($) {my ($x) = @_; $x->Cos()->divide($x->Sin())}

#_ Sum __________________________________________________________________
# Sinh
#________________________________________________________________________

sub sinh($) 
 {my ($x) = @_;

  return $zero if $x->{id} == $zero->{id};

  my $n = $x->negate;
  sigma
   (term()->c( 1)->divideInt(2)->Exp($x)->z,
    term()->c(-1)->divideInt(2)->Exp($n)->z
   )
 }

#_ Sum __________________________________________________________________
# Cosh
#________________________________________________________________________

sub cosh($) 
 {my ($x) = @_;

  return $one if $x->{id} == $zero->{id};

  my $n = $x->negate;
  sigma
   (term()->c(1)->divideInt(2)->Exp($x)->z,
    term()->c(1)->divideInt(2)->Exp($n)->z
   )
 }

#_ Sum __________________________________________________________________
# Tanh, Sech, Csch, Coth
#________________________________________________________________________

sub tanh($) {my ($x) = @_; $x->sinh()->divide($x->cosh())}
sub sech($) {my ($x) = @_; $one      ->divide($x->cosh())}
sub csch($) {my ($x) = @_; $one      ->divide($x->sinh())}
sub coth($) {my ($x) = @_; $x->cosh()->divide($x->sinh())}

#_ Sum __________________________________________________________________
# Dot - complex dot product.
#________________________________________________________________________

sub dot($$)
 {my ($a, $b) = @_;
  $b = newFromString("$b") unless ref($b) eq __PACKAGE__;
  $a->re->multiply($b->re)->add($a->im->multiply($b->im));
 }

#_ Sum __________________________________________________________________
# The area of the parallelogram formed by two complex numbers
#________________________________________________________________________

sub cross($$)
 {my ($a, $b) = @_;
  $a->dot($a)->multiply($b->dot($b))->subtract($a->dot($b)->power($two))->Sqrt;
 }

#_ Sum __________________________________________________________________
# Unit: intersection with unit circle.
#________________________________________________________________________

sub unit($)
 {my ($a) = @_;
  my $b = $a->modulus;
  my $c = $a->divide($b);
  $a->divide($a->modulus);
 }

#_ Sum __________________________________________________________________
# Real part.
#________________________________________________________________________

sub re($)
 {my ($A) = @_;
  $A = newFromString("$A") unless ref($A) eq __PACKAGE__;
  my @r;
  for my $a($A->t)
   {next if $a->i == 1;
    push @r, $a;
   }
  sigma(@r);
 }

#_ Sum __________________________________________________________________
# Imaginary part.
#________________________________________________________________________

sub im($)
 {my ($A) = @_;
  $A = newFromString("$A") unless ref($A) eq __PACKAGE__;
  my @r;
  for my $a($A->t)
   {next if $a->i == 0;
    push @r, $a;
   }
  $mI->multiply(sigma(@r));
 }

#_ Sum __________________________________________________________________
# Modulus.
#________________________________________________________________________

sub modulus($)
 {my ($a) = @_;
  $a->re->power($two)->add($a->im->power($two))->Sqrt;
 }

#_ Sum __________________________________________________________________
# Conjugate.
#________________________________________________________________________

sub conjugate($)
 {my ($a) = @_;
  $a->re->subtract($a->im->multiply($i));
 }

#_ Sum __________________________________________________________________
# Clone
#________________________________________________________________________

sub clone($) 
 {my ($t) = @_;
  $t->{z} or die "Attempt to clone unfinalized expr";
  my $c   = bless {%$t};
  $c->{t} = {%{$t->{t}}};
  delete $c->{z};
  delete $c->{s};
  delete $c->{id};
  $c;
 }

#_ Sum __________________________________________________________________
# Sign the term. Used to optimize add().  Fix the problem of adding different logs
#________________________________________________________________________

sub signature($) 
 {my ($t) = @_;
  my $s = '';
  for my $a($t->t)
   {$s .= '+'. $a->print;
   } 
  $s;
 }

#_ Sum __________________________________________________________________
# Get the signature of a term
#________________________________________________________________________

sub getSignature($) 
 {my ($t) = @_;
  exists $t->{z} ? $t->{z} : die "Attempt to get signature of unfinalized term";
 }

#_ Sum __________________________________________________________________
# Get Id of sum    
#________________________________________________________________________

sub id($) 
 {my ($t) = @_;
  $t->{id} or die "Sum $t not yet finalized";
  $t->{id};
 }

#_ Sum __________________________________________________________________
# Check sum finalized
#________________________________________________________________________

sub zz($) 
 {my ($t) = @_;
  $t->{z} or die "Sum $t not yet finalized";
  print $t->{z}, "\n";
  $t;
 }

#_ Sum __________________________________________________________________
# Finalize creation of the sum 
#________________________________________________________________________

my $lock = 0;   # Hash locking
my $z = 0;      # Term counter
my %z;          # Terms finalized

sub z($) 
 {my ($t) = @_;
  !exists($t->{z}) or die "Already finalized this term";
  
  my $p  = $t->print;
  return $z{$p} if exists $z{$p};
  $z{$p} = $t;

  $t->{s}  = $p;
  $t->{z}  = $t->signature;
  $t->{id} = ++$z;

  lock_hash(%{$t->{v}}) if $lock;           
  lock_hash %$t         if $lock;         
  $t;
 }

sub DESTROY($)
 {my ($t) = @_;
  delete $z{$t->{s}} if exists $t->{s};
 } 

sub lockHashes() 
 {my ($l) = @_;
  for my $t(values %z)
   {lock_hash(%{$t->{v}});           
    lock_hash %$t;
   }         
  $lock = 1;
 }

#_ Sum __________________________________________________________________
# Print
#________________________________________________________________________

sub print($) 
 {my ($t) = @_;
  return $t->{s} if defined($t->{s});
  my $s = '';
  for my $a($t->t)
   {$s .= $a->print .'+';
   }
  chop($s) if $s;

  $s =~ s/^\+//;
  $s =~ s/\+\-/\-/g;
  $s =~ s/\+1\*/\+/g;                                        # change: +1*      to +
  $s =~ s/\*1\*/\*/g;                                        # remove: *1*      to *
  $s =~ s/^1\*//g;                                           # remove: 1*  at start of expression      
  $s =~ s/^\-1\*/\-/g;                                       # change: -1* at start of expression to -
  $s =~ s/^0\+//g;                                           # change: 0+  at start of expression to 
  $s =~ s#\(\+0\+#\(#g;                                      # change: (+0+     to (
  $s =~ s/\(\+/\(/g;                                         # change: (+       to (
  $s =~ s/\(1\*/\(/g;                                        # change: (1*      to (
  $s =~ s/\(\-1\*/\(\-/g;                                    # change: (-1*     to (-
  $s =~ s/([a-zA-Z0-9)])\-1\*/$1\-/g;                        # change: term-1*  to term-
  $s =~ s/\*(\$[a-zA-Z]+)\*\*\-1(?!\d)/\/$1/g;               # change:  *$y**-1 to    /$y
  $s =~ s/\*(\$[a-zA-Z]+)\*\*\-(\d+)/\/$1**$2/g;             # change:  *$y**-n to    /$y**n
  $s =~ s/([\+\-])(\$[a-zA-Z]+)\*\*\-1(?!\d)/1\/$1/g;        # change: +-$y**-1 to +-1/$y
  $s =~ s/([\+\-])(\$[a-zA-Z]+)\*\*\-(\d+)/${1}1\/$2**$3/g;  # change: +-$y**-n to +-1/$y**n
  $s = 0 if $s eq '';
  $s;
 }              

#_ Sum __________________________________________________________________
# Useful constants
#________________________________________________________________________

$zero  = sigma(term('0'));    sub zero()  {$zero}
$one   = sigma(term('1'));    sub one()   {$one}
$two   = sigma(term('2'));    sub two()   {$two}
$four  = sigma(term('4'));    sub four()  {$four}
$mOne  = sigma(term('-1'));   sub mOne()  {$mOne}
$i     = sigma(term('i'));    sub i()     {$i}
$mI    = sigma(term('-i'));   sub mI()    {$mI}
$half  = sigma(term('1/2'));  sub half()  {$half}
$mHalf = sigma(term('-1/2')); sub mHalf() {$mHalf}
$pi    = sigma(term('pi'));   sub pi()    {$pi}   

#______________________________________________________________________
# Factor a number.
#______________________________________________________________________

@primes = qw(
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

sub factorize($)
 {my ($n) = @_;
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

#_ Sum __________________________________________________________________
# Import - parameters from caller - set up as requested.
#________________________________________________________________________

sub import
 {my %P = (program=>@_);
  my %p; $p{lc()} = $P{$_} for(keys(%P));

#_ Sum __________________________________________________________________
# New symbols term constructor - export to calling package.
#________________________________________________________________________

  my $s = <<'END';
package XXXX;

BEGIN  {delete $XXXX::{NNNN}}

sub NNNN
 {return SSSS::n(@_);
 }
END

#_ Sum __________________________________________________________________
# Complex functions: re, im, dot, cross, conjugate, modulus              
#________________________________________________________________________
  
  if (exists($p{complex}))
   {$s .= <<'END';
BEGIN  {delete @XXXX::{qw(conjugate cross dot im modulus re unit)}}
END
    $s .= <<'END' if $p{complex};
sub conjugate($)  {SSSS::conjugate($_[0])}
sub cross    ($$) {SSSS::cross    ($_[0], $_[1])}
sub dot      ($$) {SSSS::dot      ($_[0], $_[1])}
sub im       ($)  {SSSS::im       ($_[0])}
sub modulus  ($)  {SSSS::modulus  ($_[0])}
sub re       ($)  {SSSS::re       ($_[0])}
sub unit     ($)  {SSSS::unit     ($_[0])}
END
   }

#_ Sum __________________________________________________________________
# Trigonometric functions: tan, sec, csc, cot              
#________________________________________________________________________

  if (exists($p{trig}) or exists($p{trigonometric}))
   {$s .= <<'END';
BEGIN  {delete @XXXX::{qw(tan sec csc cot)}}
END
    $s .= <<'END' if $p{trig} or $p{trigonometric};
sub tan($) {SSSS::tan($_[0])}
sub sec($) {SSSS::sec($_[0])}
sub csc($) {SSSS::csc($_[0])}
sub cot($) {SSSS::cot($_[0])}
END
   }
  if (exists($p{trig}) and exists($p{trigonometric}))
   {croak 'Please use specify just one of trig or trigonometric';
   }

#_ Sum __________________________________________________________________
# Hyperbolic functions: sinh, cosh, tanh, sech, csch, coth              
#________________________________________________________________________

 if (exists($p{hyper}) or exists($p{hyperbolic}))
  {$s .= <<'END';
BEGIN  {delete @XXXX::{qw(sinh cosh tanh sech csch coth)}}
END
    $s .= <<'END' if $p{hyper} or $p{hyperbolic};
sub sinh($) {SSSS::sinh($_[0])}
sub cosh($) {SSSS::cosh($_[0])}
sub tanh($) {SSSS::tanh($_[0])}
sub sech($) {SSSS::sech($_[0])}
sub csch($) {SSSS::csch($_[0])}
sub coth($) {SSSS::coth($_[0])}
END
  }
 if (exists($p{hyper}) and exists($p{hyperbolic}))
  {croak 'Please specify just one of hyper or hyperbolic';
  }

#_ Sum __________________________________________________________________
# Export to calling package.
#________________________________________________________________________

  my $name   = 'sum';
     $name   = $p{sum} if exists($p{sum});
  my ($main) = caller();
  my $pack   = __PACKAGE__;   

  $s=~ s/XXXX/$main/g;
  $s=~ s/NNNN/$name/g;
  $s=~ s/SSSS/$pack/g;
  eval($s);

#_ Sum __________________________________________________________________
# Check options supplied by user
#________________________________________________________________________

  delete @p{qw(
symbols program trig trigonometric hyper hyperbolic complex
)};

  croak "Unknown option(s): ". join(' ', keys(%p))."\n\n". <<'END' if keys(%p);

Valid options are:

  sum    =>'name' Create a routine with this name in the callers
                  namespace to create new symbols. The default is
                  'sum'.


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

#_ Sum __________________________________________________________________
# Overload.
#________________________________________________________________________

use overload
 '+'     =>\&add3,
 '-'     =>\&negate3,
 '*'     =>\&multiply3,
 '/'     =>\&divide3,
 '**'    =>\&power3,
 '=='    =>\&equals3,
 'eq'    =>\&solve3, 
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

#_ Sum __________________________________________________________________
# Add operator.
#________________________________________________________________________

sub add3
 {my ($a, $b) = @_;
  $b = newFromString("$b") unless ref($b) eq __PACKAGE__;
  $a->{z} and $b->{z} or die "Add using unfinalized sums";
  $a->add($b);
 }

#_ Sum __________________________________________________________________
# Negate operator.
#________________________________________________________________________

sub negate3
 {my ($a, $b, $c) = @_;

  if (defined($b))
   {$b = newFromString("$b") unless ref($b) eq __PACKAGE__;
    $a->{z} and $b->{z} or die "Negate using unfinalized sums";
    return $b->subtract($a) if     $c;
    return $a->subtract($b) unless $c;
   }
  else
   {$a->{z} or die "Negate single unfinalized terms";
    return $a->negate;
   }
 }

#_ Sum __________________________________________________________________
# Multiply operator.
#________________________________________________________________________

sub multiply3
 {my ($a, $b) = @_;
  $b = newFromString("$b") unless ref($b) eq __PACKAGE__;
  $a->{z} and $b->{z} or die "Multiply using unfinalized sums";
  $a->multiply($b);
 }

#_ Sum __________________________________________________________________
# Divide operator.
#________________________________________________________________________

sub divide3
 {my ($a, $b, $c) = @_;
  $b = newFromString("$b") unless ref($b) eq __PACKAGE__;
  $a->{z} and $b->{z} or die "Divide using unfinalized sums";
  return $b->divide($a) if     $c;
  return $a->divide($b) unless $c;
 }

#_ Sum __________________________________________________________________
# Power operator.
#________________________________________________________________________

sub power3
 {my ($a, $b) = @_;
  $b = newFromString("$b") unless ref($b) eq __PACKAGE__;
  $a->{z} and $b->{z} or die "Power using unfinalized sums";
  $a->power($b);
 }

#_ Sum __________________________________________________________________
# Equals operator.
#________________________________________________________________________

sub equals3
 {my ($a, $b) = @_;
  $b = newFromString("$b") unless ref($b) eq __PACKAGE__;
  $a->{z} and $b->{z} or die "Equals using unfinalized sums";

  return 1 if $a->{id} == $b->{id}; # Fast equals

  my $c = $a->subtract($b);
  return 1 if $c->isZero()->{id} == $zero->{id};
  return 0;

# return 1 if $a->isEqual($b);      # Equals after equation solving 
# return 1 if $a->isEqualSqrt($b);  # Equals after sqrts multiplied out
# return 0;
 }

#_ Sum __________________________________________________________________
# <=> operator: Test expressions for equality and die of they are not.
# Sames as == but dies if fails, and prints line number of
# caller which makes testing alot easier.
#________________________________________________________________________

sub tequals3
 {my ($a, $b) = @_;

  our $written;
  print STDOUT (caller())[2], " ";
  print " "  if ++$written %   4 == 0;
  print " "  if   $written %   8 == 0;
  print "\n" if   $written %  16 == 0;
  STDOUT->flush;

  return 1 if equals3($a, $b); 
# $b = newFromString("$b") unless ref($b) eq __PACKAGE__;
# $a->{z} and $b->{z} or die "Equals using unfinalized sums";

# return 1 if $a->{id} == $b->{id}; # Fast equals
# return 1 if $a->isEqual($b);      # Equals after equation solving 
# return 1 if $a->isEqualSqrt($b);  # Equals after sqrts multiplied out

  die "\nDied in ". (caller())[0] ." at ". (caller())[1]. " line ". (caller())[2]. "\n";
 }

#_ Sum __________________________________________________________________
# Solve operator.
#________________________________________________________________________

sub solve3
 {my ($a, $b) = @_;
  $a->{z} or die "Solve using unfinalized sum";
  $b =~ /^[a-z]+$/i or croak "Bad variable $b to solve for";
  solve($a, $b);
 }

#_ Sum __________________________________________________________________
# Print operator.
#________________________________________________________________________

sub print3
 {my ($a) = @_;
  $a->{z} or die "Print of unfinalized sum";
#print STDERR (caller())[1], " ", (caller())[2], "\n";
  $a->print();
 }

#_ Sum __________________________________________________________________
# Sqrt operator.
#________________________________________________________________________

sub sqrt3
 {my ($a) = @_;
  $a->{z} or die "Sqrt of unfinalized sum";
  $a->Sqrt();
 }

#_ Sum __________________________________________________________________
# Exp operator.
#________________________________________________________________________

sub exp3
 {my ($a) = @_;
  $a->{z} or die "Exp of unfinalized sum";
  $a->Exp();
 }

#_ Sum __________________________________________________________________
# Sine operator.
#________________________________________________________________________

sub sin3
 {my ($a) = @_;
  $a->{z} or die "Sin of unfinalized sum";
  $a->Sin();
 }

#_ Sum __________________________________________________________________
# Cosine operator.
#________________________________________________________________________

sub cos3
 {my ($a) = @_;
  $a->{z} or die "Cos of unfinalized sum";
  $a->Cos();
 }

#_ Sum __________________________________________________________________
# Tan operator.
#________________________________________________________________________

sub tan3
 {my ($a) = @_;
  $a->{z} or die "Tan of unfinalized sum";
  $a->tan();
 }

#_ Sum __________________________________________________________________
# Log operator.
#________________________________________________________________________

sub log3
 {my ($a) = @_;
  $a->{z} or die "Log of unfinalized sum";
  $a->Log();
 }

#_ Sum __________________________________________________________________
# Dot Product operator.
#________________________________________________________________________

sub dot3
 {my ($a, $b, $c) = @_;
  $b = newFromString("$b") unless ref($b) eq __PACKAGE__;
  $a->{z} and $b->{z} or die "Dot of unfinalized sum";
  dot($a, $b);
 }

#_ Sum __________________________________________________________________
# Cross operator.
#________________________________________________________________________

sub cross3
 {my ($a, $b, $c) = @_;
  $b = newFromString("$b") unless ref($b) eq __PACKAGE__;
  $a->{z} and $b->{z} or die "Cross of unfinalized sum";
  cross($a, $b);
 }

#_ Sum __________________________________________________________________
# Unit operator.
#________________________________________________________________________

sub unit3
 {my ($a, $b, $c) = @_;
  $a->{z} or die "Unit of unfinalized sum";
  unit($a);
 }

#_ Sum __________________________________________________________________
# Modulus operator.
#________________________________________________________________________

sub modulus3
 {my ($a, $b, $c) = @_;
  $a->{z} or die "Modulus of unfinalized sum";
  modulus($a);
 }

#_ Sum __________________________________________________________________
# Conjugate.
#________________________________________________________________________

sub conjugate3
 {my ($a, $b, $c) = @_;
  $a->{z} or die "Conjugate of unfinalized sum";
  conjugate($a);
 }

#_ Sum __________________________________________________________________
# Tests
#________________________________________________________________________

sub test()
 {use warnings qw(all);
  no warnings qw(void);
# lockHashes();
#goto L;
 ($a, $b, $c, $x, $y) = n(qw(1 2 3 x y));

# Simple sums
  n(0)                <=> $zero;
  n(1)                <=> $one;

 ($a, $b) = n(qw(2 3));
  $a                  <=> $two;
  $b                  <=> 3;
  $a+$a               <=> 4;                  
  $a+$b               <=> 5; 
  $a+$b+$a+$b         <=> 10;
  $a+1                <=> 3;
  $a+2                <=> 4;
  $b-1                <=> 2;
  $b-2                <=> 1;
  $b-9                <=> -6;
  $a/2                <=> $one;
  $a/4                <=> '1/2';
  $a*2/2              <=> $two;
  $a*2/4              <=> $one;
  $a**2               <=> 4; 
  $a**10              <=> 1024;
  sqrt($a**2)         <=> $a;
  sqrt(n(-1))         <=> 'i';
  sqrt(n(4))          <=> 2;
  n('1/2') + '1/3' + '1/4' - '1/12' <=> 1;

 ($a, $b, $x, $y) = n(qw(1 2 x y));
  sqrt(n('-1'))       <=> $i;
  n('x')              <=> $x;
  n('2*x**2')         <=> 2*$x**2;
  $a+$a               <=> 2*$a;
  $a+$a+$a            <=> 3*$a;
  $a-$a               <=> $zero;
  $a-$a-$a            <=> -$a;
  $a*$b*$a*$b         <=> $a**2*$b**2;
 ($b/$a)**2           <=> $b**2/$a**2;
  $a**2/$b            <=> '1/2';
  sqrt($a**4/($b/2))  <=> $a;
  $b**128             <=> '340282366920938463463374607431768211456';
           
# Sin, Cos, Exp
  sin($zero)          <=> -0;
  sin($pi/6)          <=>  $half;
  sin($pi/2)          <=>  1;
  sin(5*$pi/6)        <=>  $half;
  sin(120*$pi/120)    <=>  $zero;
  sin(7*$pi/6)        <=> -$half;
  sin(3*$pi/2)        <=> -1;
  sin(110*$pi/ 60)    <=> '-1/2';
  sin(2*$pi)          <=>  $zero;
  sin(-$zero)         <=>  $zero;
  sin(-$pi/6)         <=> -$half;
  sin(-$pi/2)         <=> -$one;
  sin(-5*$pi/6)       <=> -$half;
  sin(-120*$pi/120)   <=> -$zero;
  sin(-7*$pi/6)       <=>  $half;
  sin(-3*$pi/2)       <=>  $one;
  sin(-110*$pi/ 60)   <=>  $half;
  sin(-2*$pi)         <=>  $zero;
  cos($zero)          <=>  $one;
  cos($pi/3)          <=>  $half;
  cos($pi/2)          <=>  $zero;
  cos(4*$pi/6)        <=> -$half;
  cos(120*$pi/120)    <=> -$one;
  cos(8*$pi/6)        <=> -$half;
  cos(3*$pi/2)        <=>  $zero;
  cos(100*$pi/ 60)    <=>  $half;
  cos(2*$pi)          <=>  $one;
  cos(-$zero)         <=>  $one;
  cos(-$pi/3)         <=> +$half;
  cos(-$pi/2)         <=>  $zero;
  cos(-4*$pi/6)       <=> -$half;
  cos(-120*$pi/120)   <=> -$one;
  cos(-8*$pi/6)       <=> -$half;
  cos(-3*$pi/2)       <=>  $zero;
  cos(-100*$pi/ 60)   <=>  $half;
  cos(-2*$pi)         <=>  $one;
  exp($zero)          <=>  $one;
  exp($i*$pi/2)       <=>  $i;
  exp($i*$pi)         <=> -$one;
  exp(3*$i*$pi/2)     <=> -$i;
  exp(4*$i*$pi/2)     <=>  $one;

# Polynomials
 ($x, $y) = n(qw(x y));
  $x+$y               <=> $x+$y;
 ($x+$y)**2           <=> $x**2+2*$x*$y+$y**2;
 ($x+$y)**2/$x        <=> $x+2*$y+$y**2/$x;

 ($x+$y)**2/($x+$y)            <=> $x+$y;
 ($x*$x+2*$y*$x+$y**2)/($x+$y) <=> $x+$y;

# Differentiation
  sin($x)    <=>  sin($x)->d->d->d->d; 
  exp($x)    <=>  exp($x)->d->d->d->d;
 (1/$x)->d   <=> -1/$x**2;

  sqrt(($x+$y)**2)+$x-$y                                                <=> 2*$x;
  sqrt(($x+$y)**2)+sqrt(($x-$y)**2)                                     <=> 2*$x;
  sqrt(($x+$y)**2)+sqrt(($x-$y)**2)+sqrt((-$x+$y)**2)+sqrt((-$x-$y)**2) <=> 4*$x;
 ($x*sqrt($x))->d <=> 3*sqrt($x)/2;

# Complex
  ($i ^ 1)  <=> 0;
  ($i ^ $i) <=> 1;
  $i x 1    <=> 1;                                     
  $i x $i   <=> 0;                                     
  $one x 1  <=> 0;                                     
  !$i       <=> $i;
  abs $i    <=> 1;
  re  $i    <=> 0;
  im  $i    <=> 1;
  re  $one  <=> 1;
  im  $one  <=> 0;

  ~($x+$y)  <=>  ~$x + ~$y;
  ~($x*$y)  <=>  ~$x * ~$y;
  ~($x**2)  <=> (~$x)** 2;

  abs($x+$y*$i)    <=> sqrt($x**2+$y**2);
  !($x+$y*$i)      <=> ($x+$y*$i) / sqrt($x**2+$y**2);
  abs(!($x+$y*$i)) <=> sqrt($x**2/($x**2+$y**2)+$y**2/($x**2+$y**2));

  abs(($a+$i*sqrt(1-$a*$a))*($b+$i*sqrt(1-$b*$b))) <=> 1;
  abs($a+$i*$b)*abs($x+$i*$y) <=> abs(($a+$i*$b)*($x+$i*$y));

  ($i+1) x ($i-1) <=> 2;
  (1+$i  ^ -1+$i) <=> 0;

#______________________________________________________________________
# Trigonometric
#______________________________________________________________________
   
# Reciprocals
  $a = sin($x) <=> 1/csc($x);
  $a = cos($x) <=> 1/sec($x);
  $a = tan($x) <=> 1/cot($x);
  $a = csc($x) <=> 1/sin($x);
  $a = sec($x) <=> 1/cos($x);
  $a = cot($x) <=> 1/tan($x);
                           
# Pythagoras

  sin($x)**2 + cos($x)**2 <=> 1;
  sec($x)**2 - tan($x)**2 <=> $one; 
  csc($x)**2 - cot($x)**2 <=> 1; 

# Quotient  

  tan($x) <=> sin($x)/cos($x);
  cot($x) <=> cos($x)/sin($x);   

# Co-Function Identities

  $pi = n('pi');                  
  sin($x) <=> cos($pi/2-$x);
  cos($x) <=> sin($pi/2-$x);
  cot($x) <=> tan($pi/2-$x);
  sec($x) <=> csc($pi/2-$x);
  csc($x) <=> sec($pi/2-$x);
  tan($x) <=> cot($pi/2-$x);

# Even-Odd Identities
                         
  cos($x) <=>  cos(-$x); 
  sin($x) <=> -sin(-$x); 
  tan($x) <=> -tan(-$x); 
  cot($x) <=> -cot(-$x); 
  csc($x) <=> -csc(-$x); 
  sec($x) <=>  sec(-$x); 

# Values of sin, cos at well known points

  cos(0)         <=>   1;
  cos($pi/2)     <=>   0;
  cos($pi)       <=>  -1;
  cos(3*$pi/2)   <=>   0;
  cos(4*$pi/2)   <=>   1;
  sin(0)         <=>   0;
  sin($pi/2)     <=>   1;
  sin($pi)       <=>   0;
  sin(3*$pi/2)   <=>  -1;
  sin(4*$pi/2)   <=>   0;

# Sums and Differences
                                                 
  sin($x+$y) <=> sin($x)*cos($y)+cos($x)*sin($y);
  sin($x-$y) <=> sin($x)*cos($y)-cos($x)*sin($y);
  cos($x+$y) <=> cos($x)*cos($y)-sin($x)*sin($y);
  cos($x-$y) <=> cos($x)*cos($y)+sin($x)*sin($y);

  tan($x+$y) <=> (tan($x)+tan($y))/(1-tan($x)*tan($y));
  tan($x-$y) <=> (tan($x)-tan($y))/(1+tan($x)*tan($y));

# Double angles        
                                           
  sin(2*$x) <=> 2*sin($x)*cos($x);         
  cos(2*$x) <=> cos($x)**2-sin($x)**2;     
  cos(2*$x) <=> 2*cos($x)**2-1;            
  cos(2*$x) <=> 1-2*sin($x)**2;            
  tan(2*$x) <=> 2*tan($x)/(1-tan($x)**2);  

# Power-Reducing/Half Angle Formulas       
                                                            
  sin($x)**2 <=> (1-cos(2*$x))/2;                         
  cos($x)**2 <=> (1+cos(2*$x))/2;                         
  tan($x)**2 <=> (1-cos(2*$x))/(1+cos(2*$x));             

# Sum-to-Product Formulas      
                                                            
  sin($x)+sin($y) <=>  2*sin(($x+$y)/2)*cos(($x-$y)/2);     
  sin($x)-sin($y) <=>  2*cos(($x+$y)/2)*sin(($x-$y)/2);     
  cos($x)+cos($y) <=>  2*cos(($x+$y)/2)*cos(($x-$y)/2);     
  cos($x)-cos($y) <=> -2*sin(($x+$y)/2)*sin(($x-$y)/2);   

# Product-to-Sum Formulas       
                                                   
  sin($x)*sin($y) <=> cos($x-$y)/2-cos($x+$y)/2;   
  cos($x)*cos($y) <=> cos($x-$y)/2+cos($x+$y)/2;   
  sin($x)*cos($y) <=> sin($x+$y)/2+sin($x-$y)/2;   
  cos($x)*sin($y) <=> sin($x+$y)/2-sin($x-$y)/2;   

#______________________________________________________________________
# Differentials.
#______________________________________________________________________

  sqrt($x**3)->d         <=> '3/2'*sqrt($x);
  (1/$x**10) ->d         <=>  -10/$x**11;
  ((1+$x)/sqrt(1+$x))->d <=> sqrt(1+$x)->d;
  exp($i*$x)             <=> exp($i*$x)->d->d->d->d;

  cos($x)    <=> -cos($x)->d->d;
  sin($x)    <=> -sin($x)->d->d;

  sin($x)->d <=>  cos($x); 
  cos($x)->d <=> -sin($x);
  tan($x)->d <=>  tan($x)**2 + 1;
  tan($x)->d <=>  sec($x)**2;
  cot($x)->d <=> -csc($x)**2;
  sec($x)->d <=>  sec($x)*tan($x);
  csc($x)->d <=> -csc($x)*cot($x);

#______________________________________________________________________
# Hyperbolic functions
#______________________________________________________________________
  
  cosh($x)->d <=> sinh($x);
  sinh($x)->d <=> cosh($x);
  
  cosh($x)**2-sinh($x)**2 <=> 1;
  cosh($x+$y)             <=> cosh($x)*cosh($y)+sinh($x)*sinh($y);
  sinh($x+$y)             <=> sinh($x)*cosh($y)+cosh($x)*sinh($y);
   
# Reciprocals
          
  sinh($x) <=> 1/csch($x);
  cosh($x) <=> 1/sech($x);                            
  tanh($x) <=> 1/coth($x);                            
  csch($x) <=> 1/sinh($x);                            
  sech($x) <=> 1/cosh($x);                            
  coth($x) <=> 1/tanh($x);

# Pythagoras
                           
  cosh($x)**2 - sinh($x)**2 <=> 1;
  tanh($x)**2 + sech($x)**2 <=> 1;
  coth($x)**2 - csch($x)**2 <=> 1;
                            
# Relations to Trigonometric Functions
          
  sinh($x) <=> -$i*sin($i*$x);
  csch($x) <=>  $i*csc($i*$x);
  cosh($x) <=>     cos($i*$x);
  sech($x) <=>     sec($i*$x);
  tanh($x) <=> -$i*tan($i*$x);
  coth($x) <=>  $i*cot($i*$x);

#______________________________________________________________________
# Exp.
#______________________________________________________________________
   
  exp($x)*exp($i*$x)*exp($x)*exp(-$i*$x)-exp(2*$x) <=> 0;

  1+$one+'1/2'*$one**2+'1/6'*$one**3+'1/24'*$one**4+'1/120'*$one**5+
       '1/720'*$one**6+'1/5040'*$one**7+'1/40320'*$one**8
        <=> '109601/40320';

# exp(log($x)) <=> $x;
# log(exp($x)) <=> $x;
  exp($i*$pi)  <=> -1;
  $i*exp(3*$i*$pi/2) <=> 1;

#______________________________________________________________________
# Polynomials.
#______________________________________________________________________
   
  ($x+$x*$x)*$y/($x*$y)                <=> 1+$x;
  (2*$x*$y**20) / (4*$y**19+4*$y**19)  <=> ($x*$y)/4;
  (4*$b+4*$a*$b)/(4*$b+4*$a*$b)        <=> 1/($a+1)*$a+1/($a+1);

  ($c2, $c3) = n(qw(2 3));
  (sqrt($c2)+sqrt($c3))**4 <=> 10*(sqrt($c2)+sqrt($c3))**2 - 1; # Polynomial with sqrt(2)+sqrt(3) as a zero
  ($x**16-1)/($x**8-1)                 <=> $x**8+1;
  ($x+1)**11 / (1+$x)**12              <=> 1/($x+1);
  ($x**2 + $y**2)/($x**2 + $y**2)      <=> 1;
  ($x**2 + 2*$x*$y +$y**2) / ($x+$y)   <=> $x+$y;
  (($x**2-1)/(($x+1)*($x-1)))          <=> 1;  # checks polynomial division 

#______________________________________________________________________
# Square roots.
#______________________________________________________________________

  sqrt($x+1) / sqrt(1+$x)                <=> 1;
  2*$y**2*sqrt($x+1) / (4*$y*sqrt(1+$x)) <=> $y/2;
  1/sqrt(1+$x)                           <=> 1/sqrt(1+$x); 
  1/sqrt(1+$x)**3                        <=> 1/(sqrt(1+$x)+sqrt(1+$x)*$x);
  sqrt($x+1)**3 / sqrt(1+$x)**3          <=> 1;

#______________________________________________________________________
# Pentagon
#______________________________________________________________________

   {my ($i, $x, $f) = n(qw(i x 5));
    $x = ($one+sqrt($f)) / 4; 
    $a = ($x+$i*sqrt(1-$x*$x))**3;
    $b = ($x+$i*sqrt(1-$x*$x))**2;
    $c = $a-$b;
    $d = $c->im;
    $e = $d<=> $zero;
    $e = $e;
   }
#______________________________________________________________________
# Cot of successively halved angles, starting at pi/6.
#______________________________________________________________________

   {my ($y, $h) = n(qw(1 2));
  
    my $x = sqrt($h**2 - $y**2);
    for $i(1..5)
     {$x   += $h;
      $h    = sqrt($y**2+$x**2);
     }
    print __LINE__;
    eval("$h") eq '61.1182253094272' or die;
   }
  print "\n";
 }

test unless caller;

#_ Sum __________________________________________________________________
# Package installed successfully
#________________________________________________________________________

1;

