#!perl -w

=head1 Sums

Symbolic Algebra using Pure Perl: sums.

See user manual L</NAME>.

Operations on sums of terms.

PhilipRBrenan@yahoo.com, 2004, Perl License.

=cut


package Math::Algebra::Symbols::Sum;
$VERSION=1.21;
use Math::Algebra::Symbols::Term;
use IO::Handle;
use Carp;
#HashUtil use Hash::Util qw(lock_hash);
use Scalar::Util qw(weaken);


=head2 Constructors


=head3 new

Constructor

=cut


sub new
 {bless {t=>{}};
 }


=head3 newFromString

New from String

=cut


sub newFromString($)
 {my ($a) = @_;
  return $zero unless $a;
  $a .='+';
  my @a = $a =~ /(.+?)[\+\-]/g;
  my @t = map {term($_)} @a;
  sigma(@t);
 }


=head3 n

New from Strings

=cut


sub n(@)
 {return $zero unless @_;
  my @a = map {newFromString($_)} @_;
  return @a if wantarray;
  $a[0];
 }


=head3 sigma

Create a sum from a list of terms.

=cut


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


=head3 makeInt

Construct an integer

=cut


sub makeInt($)
 {sigma(term()->one->clone->c(shift())->z)
 }


=head2 Methods


=head3 isSum

Confirm type

=cut


sub isSum($) {1}; 


=head3 t

Get list of terms from existing sum

=cut


sub t($)
 {my ($a) = @_;
  (map {$a->{t}{$_}} sort(keys(%{$a->{t}})));
 }


=head3 count

Count terms in sum              

=cut


sub count($)
 {my ($a) = @_;
  scalar(keys(%{$a->{t}}));
 }


=head3 st

Get the single term from a sum containing just one term

=cut


sub st($)
 {my ($a) = @_;
  return (values(%{$a->{t}}))[0] if scalar(keys(%{$a->{t}})) == 1;
  undef;
 }


=head3 negate

Multiply each term in a sum by -1

=cut


sub negate($)
 {my ($s) = @_;
  my  @t;
  for my $t($s->t)
   {push @t, $t->clone->timesInt(-1)->z;
   }
  sigma(@t);
 }


=head3 add

Add two sums together to make a new sum

=cut


sub add($$)
 {my ($a, $b) = @_;
  sigma($a->t, $b->t);
 }


=head3 subtract

Subtract one sum from another

=cut


sub subtract($$)
 {my ($a, $b) = @_;
  return $b->negate if $a->{id} == $zero->{id};
  $a->add($b->negate);
 }


=head3 Conditional Multiply

Multiply two sums if both sums are defined, otherwise return
the defined sum.  Assumes that at least one sum is defined.

=cut


sub multiplyC($$)
 {my ($a, $b) = @_;
  return $a unless defined($b);
  return $b unless defined($a);
  $a->multiply($b);
 }


=head3 multiply

Multiply two sums together

=cut


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
      my $e;
      if ($a{e} and $b{e})
       {my $s = $a{e}->add($b{e});
        $e = $s->st;                      # Check for single term
        $e = $e->exp2 if     defined($e); # Simplify single term if possible
        $a->Exp($s)   unless defined($e); # Reinstate Exp as sum of terms if no simplification possible 
       }
# Log    
      $a->Log($a{l} ? $a{l} : $b{l})        if $a{l} xor $b{l};
      die "Cannot multiply logs yet"        if $a{l} and $b{l};

# Combine results
      $a = $a->z;
      $b = $b->z;
      $a = $a->multiply($b);
      $a = $a->multiply($e) if defined($e);
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


=head3 divide

Divide one sum by another

=cut


sub divide($$)
 {my ($A, $B) = @_;

# Obvious cases
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


=head3 sub

Substitute a sum for a variable.

=cut


sub sub($@)
 {my $E = shift();
  my @R = @_;

# Each replacement
  for(;@R > 0;)
   {my $s = shift @R; # Replace this variable
    my $w = shift @R; # With this expression
    my $Z = $zero;

    $s =~ /^[a-z]+$/i or croak "Can only substitute an expression for a variable, not $s";
    $w = newFromString($w) unless ref($w);
    $w->isSum;

# Each term of the sum comprising the replacement expression.
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
    $E = $Z;
   }

# Result
  $E;
 }


=head3 isEqual

Check whether one sum is equal to another after multiplying out all
divides and divisors.

=cut


sub isEqual($)
 {my ($C) = @_;

# Until there are no more divides
  for(;;)
   {my (%c, $D, $N); $N = 0;

# Most frequent divisor 
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
    $C = $C->multiply($D);
   }

# Until there are no more negative powers
  for(;;)
   {my %v;
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
    $C = $C->multiply($M); 
   }

# Result
  $C;
 }


=head3 normalizeSqrts

Normalize sqrts in a sum.

This routine needs fixing.

It should simplify square roots.

=cut


sub normalizeSqrts($)
 {my ($s) = @_;
return $s;
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

$DB::single = 1;
    if ($s->{s}->isOne)
     {

push @t, $s->{t}->removeSqrt;
     }
    else
     {

push @t, $s->{t}->clone->Sqrt($s->{$s})->z;
     }
   }

# Result
  sigma(@t);
 }


=head3 isEqualSqrt

Check whether one sum is equal to another after multiplying out sqrts.

=cut


sub isEqualSqrt($)
 {my ($C) = @_;

#_______________________________________________________________________
# Each sqrt
#_______________________________________________________________________

  for(1..99)
   {$C = $C->normalizeSqrts;
    my @s = grep { defined($_->Sqrt)} $C->t;
    my @n = grep {!defined($_->Sqrt)} $C->t;
    last unless scalar(@s) > 0;

#_______________________________________________________________________
# Partition by square roots.
#_______________________________________________________________________

    my %S = ();
    for my $t(@s)
     {my $s = $t->Sqrt;
      my $S = $s->signature;
      push @{$S{$S}}, $t;
     }

#_______________________________________________________________________
# Square each partitions, as required by the formulae below.
#_______________________________________________________________________

    my @t;
    push @t, sigma(@n)->power($two) if scalar(@n);  # Non sqrt partition 
    for my $s(keys(%S))
     {push @t, sigma(@{$S{$s}})->power($two);       # Sqrt partition
     }

#_______________________________________________________________________
# I can multiply out upto 4 square roots using the formulae below.     
# There are formula to multiply out more than 4 sqrts, but they are big.
# These formulae are obtained by squaring out and rearranging:
# sqrt(a)+sqrt(b)+sqrt(c)+sqrt(d) == 0 until no sqrts remain, and
# then matching terms to produce optimal execution.
# This remarkable result was obtained with the help of this package:
# demonstrating its utility in optimizing complex calculations written
# in Perl: which in of itself cannot optimize broadly.
#_______________________________________________________________________
   
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

#________________________________________________________________________
# Test result
#________________________________________________________________________

# $C->isEqual($zero);
  $C;
 }


=head3 isZero

Transform a sum assuming that it is equal to zero

=cut


sub isZero($)
 {my ($C) = @_;
  $C->isEqualSqrt->isEqual;                  
 }


=head3 powerOfTwo

Check that a number is a power of two

=cut


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


=head3 solve

Solve an equation known to be equal to zero for a specified variable. 

=cut


sub solve($$)
 {my ($A, @x) = @_;
  croak 'Need variable to solve for' unless scalar(@x) > 0;

  @x = @{$x[0]} if scalar(@x) == 1 and ref($x[0]) eq 'ARRAY';  # Array of variables supplied
  my %x;
  for my $x(@x)
   {if (!ref $x)
     {$x =~ /^[a-z]+$/i or croak "Cannot solve for: $x, not a variable name";
     }
    elsif (ref $x eq __PACKAGE__)
     {my $t = $x->st; $t              or die "Cannot solve for multiple terms";
      my @b = $t->v;  scalar(@b) == 1 or die "Can only solve for one variable";
      my $p = $t->vp($b[0]);  $p == 1 or die "Can only solve by variable to power 1";
      $x = $b[0];
     }
    else 
     {die "$x is not a variable name";
     }
    $x{$x} = 1;
   } 
  my $x = $x[0];
  
  $B = $A->isZero;  # Eliminate sqrts and negative powers

# Strike all terms with free variables other than x: i.e. not x and not one of the named constants
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


=head3 power

Raise a sum to an integer power or an integer/2 power.

=cut


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


=head3 d

Differentiate.

=cut


sub d($;$);
sub d($;$)
 {my $c = $_[0];  # Differentiate this sum 
  my $b = $_[1];  # With this variable

#_______________________________________________________________________
# Get differentrix. Assume 'x', 'y', 'z' or 't' if appropriate.
#_______________________________________________________________________

  if (defined($b))
   {if (!ref $b)
     {$b =~ /^[a-z]+$/i or croak "Cannot differentiate by $b";
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

#_______________________________________________________________________
# Each term
#_______________________________________________________________________

  my @t = ();
  for my $t($c->t)
   {my %V = $t->split;
    my $T = $V{t}->z->clone->z;
    my ($S, $D, $E, $L) = @V{qw(s d e l)};
    my $s = $S->d($b) if $S;    
    my $d = $D->d($b) if $D;      
    my $e = $E->d($b) if $E;  
    my $l = $L->d($b) if $L;  

#_______________________________________________________________________
# Differentiate Variables: A*v**n->d == A*n*v**(n-1)
#_______________________________________________________________________

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

#_______________________________________________________________________
# Differentiate Sqrt: A*sqrt(F(x))->d == 1/2*A*f(x)/sqrt(F(x))
#_______________________________________________________________________

    if ($S)
     {my $v = $T->clone->divideInt(2);
      $v->Divide($D) if $D;
      $v->Exp   ($E) if $E;
      $v->Log   ($L) if $L;
      push @t, sigma($v->z)->multiply($s)->divide($S->Sqrt)->t;
     }

#_______________________________________________________________________
# Differentiate Divide: A/F(x)->d == -A*f(x)/F(x)**2
#_______________________________________________________________________

    if ($D)
     {my $v = $T->clone->negate;
      $v->Sqrt($S) if $S;
      $v->Exp ($E) if $E;
      $v->Log ($L) if $L;
      push @t, sigma($v->z)->multiply($d)->divide($D->multiply($D))->t;
     }

#_______________________________________________________________________
# Differentiate Exp: A*exp(F(x))->d == A*f(x)*exp(F(x))
#_______________________________________________________________________

    if ($E)
     {my $v = $T->clone;
      $v->Sqrt  ($S) if $S;
      $v->Divide($D) if $D;
      $v->Exp   ($E);
      $v->Log   ($L) if $L;
      push @t, sigma($v->z)->multiply($e)->t;
     }

#_______________________________________________________________________
# Differentiate Log: A*log(F(x))->d == A*f(x)/F(x)
#_______________________________________________________________________

    if ($L)
     {my $v = $T->clone;
      $v->Sqrt  ($S) if $S;
      $v->Divide($D) if $D;
      $v->Exp   ($E) if $E;
      push @t, sigma($v->z)->multiply($l)->divide($L)->t;
     }
   }

#_______________________________________________________________________
# Result
#_______________________________________________________________________

  sigma(@t);
 }


=head3 simplify

Simplify just before assignment.

There is no general simplification algorithm. So try various methods and
see if any simplifications occur. This is cheating really, because the
examples will represent these specific transformations as general
features which they are not. On the other hand, Mathematics is full of
specifics so I suppose its not entirely unacceptable.

Simplification cannot be done after every operation as it is
inefficient, doing it as part of += ameliorates this inefficiency.

Note: += only works as a synonym for simplify() if the left hand side is
currently undefined. This can be enforced by using my() as in: my $z +=
($x**2+5x+6)/($x+2);

=cut


sub simplify($) 
 {my ($x) = @_;
  $x = polynomialDivision($x);
  $x = eigenValue($x);
 }

#_______________________________________________________________________
# Common factor: find the largest factor in one or more expressions
#_______________________________________________________________________

sub commonFactor(@) 
 {return undef unless scalar(@_);
  return undef unless scalar(keys(%{$_[0]->{t}}));
  my $p = (values(%{$_[0]->{t}}))[0];

  my %v = %{$p->{v}};                     # Variables
  my %s = $p->split;
  my ($s, $d, $e, $l) = @s{qw(s d e l)};  # Sub expressions
  my ($C, $D, $I) = ($p->c, $p->d, $p->i);

  my @t;
  for my $a(@_)
   {for my $b($a->t)
     {push @t, $b;
     }
   }

  for my $t(@t)
   {my %V = %v;
    %v = ();
    for my $v($t->v)
     {next unless $V{$v};
      my $p = $t->vp($v); 
      $v{$v} = ($V{$v} < $p ? $V{$v} : $p);
     }
    my %S = $t->split;
    my ($S, $D, $E, $L) = @S{qw(s d e l)};  # Sub expressions
    $s = undef unless defined($s) and defined($S) and $S->id eq $s->id;
    $d = undef unless defined($d) and defined($D) and $D->id eq $d->id;
    $e = undef unless defined($e) and defined($E) and $E->id eq $e->id;
    $l = undef unless defined($l) and defined($L) and $L->id eq $l->id;
    $C = undef unless defined($C) and $C == $t->c;
    $D = undef unless defined($D) and $D == $t->d;
    $I = undef unless defined($I) and $I == $t->i;
   }
  my $r = term()->one->clone;
  $r->c($C) if defined($C);
  $r->d($D) if defined($D);
  $r->i($I) if defined($I);
  $r->vp($_, $v{$_}) for(keys(%v));
  $r->Sqrt  ($s) if defined($s);
  $r->Divide($d) if defined($d);
  $r->Exp   ($e) if defined($e);
  $r->Log   ($l) if defined($l);
  sigma($r->z);
 }

#_______________________________________________________________________
# Find term of polynomial of highest degree.
#_______________________________________________________________________

sub polynomialTermOfHighestDegree($$) 
 {my ($p, $v) = @_;     # Polynomial, variable
  my $n = 0;            # Current highest degree  
  my $t;                # Term with this degree 
  for my $T($p->t)
   {my $N = $T->vp($v);
    if ($N > $n)
     {$n = $N;
      $t = $T;
     }
   }
  ($n, $t);
 }


=head3 polynomialDivide

Polynomial divide - divide one polynomial (a) by another (b) in variable v

=cut


sub polynomialDivide($$$) 
 {my ($p, $q, $v) = @_;

  my $r = zero()->clone()->z;
  for(;;)
   {my ($np, $mp) = $p->polynomialTermOfHighestDegree($v);
    my ($nq, $mq) = $q->polynomialTermOfHighestDegree($v);
    last unless $np >= $nq;
    my $pq = sigma($mp->divide2($mq));
    $r = $r->add($pq);
    $p = $p->subtract($q->multiply($pq));
   }
  return $r if $p->isZero()->{id} == $zero->{id};
  undef;
 }


=head3 eigenValue

Eigenvalue check

=cut


sub eigenValue($) 
 {my ($p) = @_;

# Find divisors
  my %d;
  for my $t($p->t)
   {my $d  = $t->Divide;
    next unless defined($d);
    $d{$d->id} = $d;
   }

# Consolidate numerator and denominator
  my $P = $p   ->clone()->z; $P = $P->multiply($d{$_}) for(keys(%d));
  my $Q = one()->clone()->z; $Q = $Q->multiply($d{$_}) for(keys(%d));

# Check for P=nQ i.e. for eigenvalue
  my $cP = $P->commonFactor; my $dP = $P->divide($cP);
  my $cQ = $Q->commonFactor; my $dQ = $Q->divide($cQ);

  return $cP->divide($cQ) if $dP->id == $dQ->id;
  $p;
 }


=head3 polynomialDivision

Polynomial division.

=cut


sub polynomialDivision($) 
 {my ($p) = @_;

# Find a plausible indeterminate
  my %v;                # Possible indeterminates
  my $v;                # Polynomial indeterminate
  my %D;                # Divisors for each term

# Each term
  for my $t($p->t)
   {my @v = $t->v;
    $v{$_}{$t->vp($_)} = 1 for(@v);
    my %V = $t->split;
    my ($S, $D, $E, $L) = @V{qw(s d e l)};
    return $p if defined($S) or defined($E) or defined($L);

# Each divisor term
    if (defined($D))
     {for my $T($D->t)
       {my @v = $T->v;
        $v{$_}{$T->vp($_)} = 1 for(@v);
        my %V = $T->split;
        my ($S, $D, $E, $L) = @V{qw(s d e l)};
        return $p if defined($S) or defined($D) or defined($E) or defined($L);
       }
      $D{$D->id} = $D;
     }  
   }

# Consolidate numerator and denominator
  my $P = $p   ->clone()->z; $P = $P->multiply($D{$_}) for(keys(%D));
  my $Q = one()->clone()->z; $Q = $Q->multiply($D{$_}) for(keys(%D));

# Pick a possible indeterminate
  for(keys(%v))
   {delete $v{$_} if scalar(keys(%{$v{$_}})) == 1;
   }
  return $p unless scalar(keys(%v)); 
  $v = (keys(%v))[0];

# Divide P by Q
  my $r;
     $r = $P->polynomialDivide($Q, $v); return $r                if defined($r);
     $r = $Q->polynomialDivide($P, $v); return one()->divide($r) if defined($r);
  $p;
 }


=head3 Sqrt

Square root of a sum

=cut


sub Sqrt($) 
 {my ($x) = @_;
  my $s = $x->st;
  if (defined($s))
   {my $r = $s->sqrt2;
    return sigma($r) if defined($r);
   }

  sigma(term()->c(1)->Sqrt($x)->z);
 }


=head3 Exp

Exponential (B<e> raised to the power) of a sum

=cut


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


=head3 Log

Log to base B<e> of a sum

=cut


sub Log($) 
 {my ($x) = @_;
  my $s = $x->st;
  if (defined($s))
   {my $r = $s->log2;
    return sigma($r) if defined($r);
   }

  sigma(term()->c(1)->Log($x)->z);
 }


=head3 Sin

Sine of a sum

=cut


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


=head3 Cos

Cosine of a sum

=cut


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


=head3 tan, Ssc, csc, cot

Tan, sec, csc, cot of a sum

=cut


sub tan($) {my ($x) = @_; $x->Sin()->divide($x->Cos())}
sub sec($) {my ($x) = @_; $one     ->divide($x->Cos())}
sub csc($) {my ($x) = @_; $one     ->divide($x->Sin())}
sub cot($) {my ($x) = @_; $x->Cos()->divide($x->Sin())}


=head3 sinh

Hyperbolic sine of a sum

=cut


sub sinh($) 
 {my ($x) = @_;

  return $zero if $x->{id} == $zero->{id};

  my $n = $x->negate;
  sigma
   (term()->c( 1)->divideInt(2)->Exp($x)->z,
    term()->c(-1)->divideInt(2)->Exp($n)->z
   )
 }


=head3 cosh

Hyperbolic cosine of a sum

=cut


sub cosh($) 
 {my ($x) = @_;

  return $one if $x->{id} == $zero->{id};

  my $n = $x->negate;
  sigma
   (term()->c(1)->divideInt(2)->Exp($x)->z,
    term()->c(1)->divideInt(2)->Exp($n)->z
   )
 }


=head3 Tanh, Sech, Csch, Coth

Tanh, Sech, Csch, Coth of a sum

=cut


sub tanh($) {my ($x) = @_; $x->sinh()->divide($x->cosh())}
sub sech($) {my ($x) = @_; $one      ->divide($x->cosh())}
sub csch($) {my ($x) = @_; $one      ->divide($x->sinh())}
sub coth($) {my ($x) = @_; $x->cosh()->divide($x->sinh())}


=head3 dot

Dot - complex dot product of two complex sums

=cut


sub dot($$)
 {my ($a, $b) = @_;
  $b = newFromString("$b") unless ref($b) eq __PACKAGE__;
  $a->re->multiply($b->re)->add($a->im->multiply($b->im));
 }


=head3 cross

The area of the parallelogram formed by two complex sums

=cut


sub cross($$)
 {my ($a, $b) = @_;
  $a->dot($a)->multiply($b->dot($b))->subtract($a->dot($b)->power($two))->Sqrt;
 }


=head3 unit

Intersection of a complex sum with the unit circle.

=cut


sub unit($)
 {my ($a) = @_;
  my $b = $a->modulus;
  my $c = $a->divide($b);
  $a->divide($a->modulus);
 }


=head3 re

Real part of a complex sum

=cut


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


=head3 im

Imaginary part of a complex sum

=cut


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


=head3 modulus

Modulus of a complex sum

=cut


sub modulus($)
 {my ($a) = @_;
  $a->re->power($two)->add($a->im->power($two))->Sqrt;
 }


=head3 conjugate

Conjugate of a complexs sum

=cut


sub conjugate($)
 {my ($a) = @_;
  $a->re->subtract($a->im->multiply($i));
 }


=head3 clone

Clone

=cut


sub clone($) 
 {my ($t) = @_;
  $t->{z} or die "Attempt to clone unfinalized sum";
  my $c   = bless {%$t};
  $c->{t} = {%{$t->{t}}};
  delete $c->{z};
  delete $c->{s};
  delete $c->{id};
  $c;
 }


=head3 signature

Signature of a sum: used to optimize add().
# Fix the problem of adding different logs

=cut


sub signature($) 
 {my ($t) = @_;
  my $s = '';
  for my $a($t->t)
   {$s .= '+'. $a->print;
   } 
  $s;
 }


=head3 getSignature

Get the signature (see L</signature>) of a sum

=cut


sub getSignature($) 
 {my ($t) = @_;
  exists $t->{z} ? $t->{z} : die "Attempt to get signature of unfinalized sum";
 }


=head3 id

Get Id of sum: each sum has a unique identifying number.    

=cut


sub id($) 
 {my ($t) = @_;
  $t->{id} or die "Sum $t not yet finalized";
  $t->{id};
 }


=head3 zz

Check sum finalized.  See: L</z>.

=cut


sub zz($) 
 {my ($t) = @_;
  $t->{z} or die "Sum $t not yet finalized";
  print $t->{z}, "\n";
  $t;
 }


=head3 z

Finalize creation of the sum: Once a sum has been finalized it becomes
read only.

=cut


my $lock = 0;   # Hash locking
my $z = 0;      # Term counter
my %z;          # Terms finalized

sub z($) 
 {my ($t) = @_;
  !exists($t->{z}) or die "Already finalized this term";
  
  my $p  = $t->print;
  return $z{$p} if defined($z{$p});
  $z{$p} = $t;
  weaken($z{$p}); # Reduces memory usage.

  $t->{s}  = $p;
  $t->{z}  = $t->signature;
  $t->{id} = ++$z;

#HashUtil   lock_hash(%{$t->{v}}) if $lock;           
#HashUtil   lock_hash %$t         if $lock;         
  $t;
 }

#sub DESTROY($)
# {my ($t) = @_;
#  delete $z{$t->{s}} if defined($t) and exists $t->{s};
# } 

sub lockHashes() 
 {my ($l) = @_;
#HashUtil   for my $t(values %z)
#HashUtil    {lock_hash(%{$t->{v}});           
#HashUtil     lock_hash %$t;
#HashUtil    }         
  $lock = 1;
 }


=head3 print

Print sum

=cut


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
  $s =~ s/\+0$//;                                            # remove: +0  at end   of expression
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


=head3 constants

Useful constants

=cut


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


=head3 factorize

Factorize a number.

=cut


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


=head2 import

Export L</n> with either the default name B<sums>, or a name supplied by
the caller of this package.

=cut


sub import
 {my %P = (program=>@_);
  my %p; $p{lc()} = $P{$_} for(keys(%P));

#_______________________________________________________________________
# New sum constructor - export to calling package.
#_______________________________________________________________________

  my $s = "package XXXX;\n". <<'END';
no warnings 'redefine';
sub NNNN
 {return SSSSn(@_);
 }
use warnings 'redefine';
END

#_______________________________________________________________________
# Export to calling package.
#_______________________________________________________________________

  my $name   = 'sum';
     $name   = $p{sum} if exists($p{sum});
  my ($main) = caller();
  my $pack   = __PACKAGE__ . '::';   

  $s=~ s/XXXX/$main/g;
  $s=~ s/NNNN/$name/g;
  $s=~ s/SSSS/$pack/g;
  eval($s);

#_______________________________________________________________________
# Check options supplied by user
#_______________________________________________________________________

  delete @p{qw(program sum)};

  croak "Unknown option(s): ". join(' ', keys(%p))."\n\n". <<'END' if keys(%p);

Valid options are:

  sum    =>'name' Create a routine with this name in the callers
                  namespace to create new symbols. The default is
                  'sum'.
END
 }


=head2 Operators


=head3 Operator Overloads

Overload Perl operators. Beware the low priority of B<^>.

=cut


use overload
 '+'     =>\&add3,
 '-'     =>\&negate3,
 '*'     =>\&multiply3,
 '/'     =>\&divide3,
 '**'    =>\&power3,
 '=='    =>\&equals3,
 '!='    =>\&nequal3,
 'eq'    =>\&negate3, 
 '>'     =>\&solve3, 
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


=head3 add3

Add operator.

=cut


sub add3
 {my ($a, $b) = @_;
  return simplify($a) unless defined($b); # += : simplify()
  $b = newFromString("$b") unless ref($b) eq __PACKAGE__;
  $a->{z} and $b->{z} or die "Add using unfinalized sums";
  $a->add($b);
 }


=head3 negate3

Negate operator. Used in combination with the L</add3> operator to
perform subtraction.

=cut


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


=head3 multiply3

Multiply operator.

=cut


sub multiply3
 {my ($a, $b) = @_;
  $b = newFromString("$b") unless ref($b) eq __PACKAGE__;
  $a->{z} and $b->{z} or die "Multiply using unfinalized sums";
  $a->multiply($b);
 }


=head3 divide3

Divide operator.

=cut


sub divide3
 {my ($a, $b, $c) = @_;
  $b = newFromString("$b") unless ref($b) eq __PACKAGE__;
  $a->{z} and $b->{z} or die "Divide using unfinalized sums";
  return $b->divide($a) if     $c;
  return $a->divide($b) unless $c;
 }


=head3 power3

Power operator.

=cut


sub power3
 {my ($a, $b) = @_;
  $b = newFromString("$b") unless ref($b) eq __PACKAGE__;
  $a->{z} and $b->{z} or die "Power using unfinalized sums";
  $a->power($b);
 }


=head3 equals3

Equals operator.

=cut


sub equals3
 {my ($a, $b) = @_;
  $b = newFromString("$b") unless ref($b) eq __PACKAGE__;
  $a->{z} and $b->{z} or die "Equals using unfinalized sums";

  return 1 if $a->{id} == $b->{id}; # Fast equals

  my $c = $a->subtract($b);

  return 1 if $c->isZero()->{id} == $zero->{id};
  return 0;
 }


=head3 nequal3

Not equal operator.

=cut


sub nequal3
 {my ($a, $b) = @_;
  !equals3($a, $b);
 }


=head3 tequals

Evaluate the expression on the left hand side, stringify it, then
compare it for string equality with the string on the right hand side.
This operator is useful for making examples written with Test::Simple
more readable.

=cut


sub tequals3
 {my ($a, $b) = @_;

  return 1 if "$a" eq $b;

  my $z = simplify($a);

  "$z" eq "$b";
 }


=head3 solve3

Solve operator.

=cut


sub solve3
 {my ($a, $b) = @_;
  $a->{z} or die "Solve using unfinalized sum";
# $b =~ /^[a-z]+$/i or croak "Bad variable $b to solve for";
  solve($a, $b);
 }


=head3 print3

Print operator.

=cut


sub print3
 {my ($a) = @_;
  $a->{z} or die "Print of unfinalized sum";
  $a->print();
 }


=head3 sqrt3

Sqrt operator.

=cut


sub sqrt3
 {my ($a) = @_;
  $a->{z} or die "Sqrt of unfinalized sum";
  $a->Sqrt();
 }


=head3 exp3

Exp operator.

=cut


sub exp3
 {my ($a) = @_;
  $a->{z} or die "Exp of unfinalized sum";
  $a->Exp();
 }


=head3 sin3

Sine operator.

=cut


sub sin3
 {my ($a) = @_;
  $a->{z} or die "Sin of unfinalized sum";
  $a->Sin();
 }


=head3 cos3

Cosine operator.

=cut


sub cos3
 {my ($a) = @_;
  $a->{z} or die "Cos of unfinalized sum";
  $a->Cos();
 }


=head3 tan3

Tan operator.

=cut


sub tan3
 {my ($a) = @_;
  $a->{z} or die "Tan of unfinalized sum";
  $a->tan();
 }


=head3 log3

Log operator.

=cut


sub log3
 {my ($a) = @_;
  $a->{z} or die "Log of unfinalized sum";
  $a->Log();
 }


=head3 dot3

Dot Product operator.

=cut


sub dot3
 {my ($a, $b, $c) = @_;
  $b = newFromString("$b") unless ref($b) eq __PACKAGE__;
  $a->{z} and $b->{z} or die "Dot of unfinalized sum";
  dot($a, $b);
 }


=head3 cross3

Cross operator.

=cut


sub cross3
 {my ($a, $b, $c) = @_;
  $b = newFromString("$b") unless ref($b) eq __PACKAGE__;
  $a->{z} and $b->{z} or die "Cross of unfinalized sum";
  cross($a, $b);
 }


=head3 unit3

Unit operator.

=cut


sub unit3
 {my ($a, $b, $c) = @_;
  $a->{z} or die "Unit of unfinalized sum";
  unit($a);
 }


=head3 modulus3

Modulus operator.

=cut


sub modulus3
 {my ($a, $b, $c) = @_;
  $a->{z} or die "Modulus of unfinalized sum";
  modulus($a);
 }


=head3 conjugate3

Conjugate.

=cut


sub conjugate3
 {my ($a, $b, $c) = @_;
  $a->{z} or die "Conjugate of unfinalized sum";
  conjugate($a);
 }

#________________________________________________________________________
# Package installed successfully
#________________________________________________________________________

1;

__DATA__


#______________________________________________________________________
# User guide.
#______________________________________________________________________

=head1 NAME

Math::Algebra::Symbols - Symbolic Algebra in Pure Perl.

User guide.

=head1 SYNOPSIS

Example symbols.pl

 #!perl -w -I..
 #______________________________________________________________________
 # Symbolic algebra.
 # Perl License.
 # PhilipRBrenan@yahoo.com, 2004.
 #______________________________________________________________________
 
 use Math::Algebra::Symbols hyper=>1;
 use Test::Simple tests=>5;
 
 ($n, $x, $y) = symbols(qw(n x y));
 
 $a     += ($x**8 - 1)/($x-1);
 $b     +=  sin($x)**2 + cos($x)**2; 
 $c     += (sin($n*$x) + cos($n*$x))->d->d->d->d / (sin($n*$x)+cos($n*$x));
 $d      =  tanh($x+$y) == (tanh($x)+tanh($y))/(1+tanh($x)*tanh($y));
 ($e,$f) =  @{($x**2 eq 5*$x-6) > $x};
 
 print "$a\n$b\n$c\n$d\n$e,$f\n";
 
 ok("$a"    eq '$x+$x**2+$x**3+$x**4+$x**5+$x**6+$x**7+1');
 ok("$b"    eq '1'); 
 ok("$c"    eq '$n**4'); 
 ok("$d"    eq '1'); 
 ok("$e,$f" eq '2,3');
 


=head1 DESCRIPTION

This package supplies a set of functions and operators to manipulate
operator expressions algebraically using the familiar Perl syntax.

These expressions are constructed
from L</Symbols>, L</Operators>, and L</Functions>, and processed via
L</Methods>.  For examples, see: L</Examples>.

=head2 Symbols

Symbols are created with the exported B<symbols()> constructor routine:

Example t/constants.t

 #!perl -w
 #______________________________________________________________________
 # Symbolic algebra: examples: constants.
 # PhilipRBrenan@yahoo.com, 2004, Perl License.
 #______________________________________________________________________
 
 use Math::Algebra::Symbols;
 use Test::Simple tests=>1;
 
 my ($x, $y, $i, $o, $pi) = symbols(qw(x y i 1 pi));
 
 ok( "$x $y $i $o $pi"   eq   '$x $y i 1 $pi'  );
 


The B<symbols()> routine constructs references to symbolic variables and
symbolic constants from a list of names and integer constants.

The special symbol B<i> is recognized as the square root of B<-1>.

The special symbol B<pi> is recognized as the smallest positive real
that satisfies:

Example t/ipi.t

 #!perl -w
 #______________________________________________________________________
 # Symbolic algebra: examples: constants.
 # PhilipRBrenan@yahoo.com, 2004, Perl License.
 #______________________________________________________________________
 
 use Math::Algebra::Symbols;
 use Test::Simple tests=>2;
 
 my ($i, $pi) = symbols(qw(i pi));
 
 ok(  exp($i*$pi)  ==   -1  );
 ok(  exp($i*$pi) <=>  '-1' );
 


=head3 Constructor Routine Name

If you wish to use a different name for the constructor routine, say
B<S>:

Example t/ipi2.t

 #!perl -w
 #______________________________________________________________________
 # Symbolic algebra: examples: constants.
 # PhilipRBrenan@yahoo.com, 2004, Perl License.
 #______________________________________________________________________
 
 use Math::Algebra::Symbols symbols=>'S';
 use Test::Simple tests=>2;
 
 my ($i, $pi) = S(qw(i pi));
 
 ok(  exp($i*$pi)  ==   -1  );
 ok(  exp($i*$pi) <=>  '-1' );


=head3 Big Integers

Symbols automatically uses big integers if needed.

Example t/bigInt.t

 #!perl -w
 #______________________________________________________________________
 # Symbolic algebra: examples: bigInt.
 # PhilipRBrenan@yahoo.com, 2004, Perl License.
 #______________________________________________________________________
 
 use Math::Algebra::Symbols;
 use Test::Simple tests=>1;
 
 my $z = symbols('1234567890987654321/1234567890987654321');
 
 ok( eval $z eq '1');
 


=head2 Operators

L</Symbols> can be combined with L</Operators> to create symbolic expressions:

=head3 Arithmetic operators


=head4 Arithmetic Operators: B<+> B<-> B<*> B</> B<**> 
            
Example t/x2y2.t

 #!perl -w
 #______________________________________________________________________
 # Symbolic algebra: examples: simplification.
 # PhilipRBrenan@yahoo.com, 2004, Perl License.
 #______________________________________________________________________
 
 use Math::Algebra::Symbols;
 use Test::Simple tests=>3;
 
 my ($x, $y) = symbols(qw(x y));
 
 ok(  ($x**2-$y**2)/($x-$y)  ==  $x+$y  );
 ok(  ($x**2-$y**2)/($x-$y)  !=  $x-$y  );
 ok(  ($x**2-$y**2)/($x-$y) <=> '$x+$y' );
 
 


The operators: B<+=> B<-=> B<*=> B</=> are overloaded to work
symbolically rather than numerically. If you need numeric results, you
can always B<eval()> the resulting symbolic expression.

=head4 Square root Operator: B<sqrt>       

Example t/ix.t

 #!perl -w
 #______________________________________________________________________
 # Symbolic algebra: examples: sqrt(-1).
 # PhilipRBrenan@yahoo.com, 2004, Perl License.
 #______________________________________________________________________
 
 use Math::Algebra::Symbols;
 use Test::Simple tests=>2;
 
 my ($x, $i) = symbols(qw(x i));
 
 ok(  sqrt(-$x**2)  ==  $i*$x  );
 ok(  sqrt(-$x**2)  <=> 'i*$x' );
 
 


The square root is represented by the symbol B<i>, which allows complex
expressions to be processed by Math::Complex.

=head4 Exponential Operator: B<exp>       

Example t/expd.t

 #!perl -w
 #______________________________________________________________________
 # Symbolic algebra: examples: exp.
 # PhilipRBrenan@yahoo.com, 2004, Perl License.
 #______________________________________________________________________
 
 use Math::Algebra::Symbols;
 use Test::Simple tests=>2;
 
 my ($x, $i) = symbols(qw(x i));
 
 ok(   exp($x)->d($x)  ==   exp($x)  );
 ok(   exp($x)->d($x) <=>  'exp($x)' );
 
 


The exponential operator.

=head4 Logarithm Operator: B<log>       

Example t/logExp.t

 #!perl -w
 #______________________________________________________________________
 # Symbolic algebra: examples: log: need better example.
 # PhilipRBrenan@yahoo.com, 2004, Perl License.
 #______________________________________________________________________
 
 use Math::Algebra::Symbols;
 use Test::Simple tests=>1;
 
 my ($x) = symbols(qw(x));
 
 ok(   log($x) <=>  'log($x)' );
 
 


Logarithm to base B<e>.

Note: the above result is only true for x > 0.  B<Symbols> does not include domain and range
specifications of the functions it uses.

=head4 Sine and Cosine Operators: B<sin> and B<cos>       

Example t/sinCos.t

 #!perl -w
 #______________________________________________________________________
 # Symbolic algebra: examples: simplification.
 # PhilipRBrenan@yahoo.com, 2004, Perl License.
 #______________________________________________________________________
 
 use Math::Algebra::Symbols;
 use Test::Simple tests=>3;
 
 my ($x) = symbols(qw(x));
 
 ok(  sin($x)**2 + cos($x)**2  ==  1  );
 ok(  sin($x)**2 + cos($x)**2  !=  0  );
 ok(  sin($x)**2 + cos($x)**2 <=> '1' );
 
 


This famous trigonometric identity is not preprogrammed into B<Symbols>
as it is in commercial products.

Instead: an expression for B<sin()> is constructed using the complex
exponential: L</exp>, said expression is algebraically multiplied out to
prove the identity. The proof steps involve large intermediate
expressions in each step, as yet I have not provided a means to neatly
lay out these intermediate steps and thus provide a more compelling
demonstration of the ability of B<Symbols> to verify such statements
from first principles.
 

=head3 Relational operators                                   

=head4 Relational operators: B<==>, B<!=> 

Example t/x2y2.t

 #!perl -w
 #______________________________________________________________________
 # Symbolic algebra: examples: simplification.
 # PhilipRBrenan@yahoo.com, 2004, Perl License.
 #______________________________________________________________________
 
 use Math::Algebra::Symbols;
 use Test::Simple tests=>3;
 
 my ($x, $y) = symbols(qw(x y));
 
 ok(  ($x**2-$y**2)/($x-$y)  ==  $x+$y  );
 ok(  ($x**2-$y**2)/($x-$y)  !=  $x-$y  );
 ok(  ($x**2-$y**2)/($x-$y) <=> '$x+$y' );
 
 


The relational equality operator B<==> compares two symbolic expressions
and returns TRUE(1) or FALSE(0) accordingly. B<!=> produces the opposite
result.

=head4 Relational operator: B<eq> 

Example t/eq.t

 #!perl -w
 #______________________________________________________________________
 # Symbolic algebra: examples: solving.
 # PhilipRBrenan@yahoo.com, 2004, Perl License.
 #______________________________________________________________________
 
 use Math::Algebra::Symbols;
 use Test::Simple tests=>3;
 
 my ($x, $v, $t) = symbols(qw(x v t));
 
 ok(  ($v eq $x / $t)->solve(qw(x in terms of v t))  ==  $v*$t  );
 ok(  ($v eq $x / $t)->solve(qw(x in terms of v t))  !=  $v+$t  );
 ok(  ($v eq $x / $t)->solve(qw(x in terms of v t)) <=> '$v*$t' );
 
 


The relational operator B<eq> is a synonym for the minus B<-> operator,
with the expectation that later on the L<solve()|/Solving equations>
function will be used to simplify and rearrange the equation. You may
prefer to use B<eq> instead of B<-> to enhance readability, there is no
functional difference.

=head3 Complex operators

=head4 Complex operators: the B<dot> operator: B<^>       

Example t/dot.t

 #!perl -w
 #______________________________________________________________________
 # Symbolic algebra: examples: dot operator.  Note the low priority
 # of the ^ operator.
 # PhilipRBrenan@yahoo.com, 2004, Perl License.
 #______________________________________________________________________
 
 use Math::Algebra::Symbols;
 use Test::Simple tests=>3;
 
 my ($a, $b, $i) = symbols(qw(a b i));
 
 ok(  (($a+$i*$b)^($a-$i*$b))  ==  $a**2-$b**2  );
 ok(  (($a+$i*$b)^($a-$i*$b))  !=  $a**2+$b**2  );
 ok(  (($a+$i*$b)^($a-$i*$b)) <=> '$a**2-$b**2' );
 


Note the use of brackets:  The B<^> operator has low priority.

The B<^> operator treats its left hand and right hand arguments as
complex numbers, which in turn are regarded as two dimensional vectors
to which the vector dot product is applied.

=head4 Complex operators: the B<cross> operator: B<x>       

Example t/cross.t

 #!perl -w
 #______________________________________________________________________
 # Symbolic algebra: examples: cross operator.
 # PhilipRBrenan@yahoo.com, 2004, Perl License.
 #______________________________________________________________________
 
 use Math::Algebra::Symbols;
 use Test::Simple tests=>3;
 
 my ($x, $i) = symbols(qw(x i));
 
 ok(  $i*$x x $x  ==  $x**2  );
 ok(  $i*$x x $x  !=  $x**3  );
 ok(  $i*$x x $x <=> '$x**2' );
 


The B<x> operator treats its left hand and right hand arguments as
complex numbers, which in turn are regarded as two dimensional vectors
defining the sides of a parallelogram. The B<x> operator returns the
area of this parallelogram.

Note the space before the B<x>, otherwise Perl is unable to disambiguate
the expression correctly.

=head4 Complex operators: the B<conjugate> operator: B<~>       

Example t/conjugate.t

 #!perl -w
 #______________________________________________________________________
 # Symbolic algebra: examples: dot operator.  Note the low priority
 # of the ^ operator.
 # PhilipRBrenan@yahoo.com, 2004, Perl License.
 #______________________________________________________________________
 
 use Math::Algebra::Symbols;
 use Test::Simple tests=>3;
 
 my ($x, $y, $i) = symbols(qw(x y i));
 
 ok(  ~($x+$i*$y)  ==  $x-$i*$y  );
 ok(  ~($x-$i*$y)  ==  $x+$i*$y  );
 ok(  (($x+$i*$y)^($x-$i*$y)) <=> '$x**2-$y**2' );
 


The B<~> operator returns the complex conjugate of its right hand side.

=head4 Complex operators: the B<modulus> operator: B<abs>       

Example t/abs.t

 #!perl -w
 #______________________________________________________________________
 # Symbolic algebra: examples: dot operator.  Note the low priority
 # of the ^ operator.
 # PhilipRBrenan@yahoo.com, 2004, Perl License.
 #______________________________________________________________________
 
 use Math::Algebra::Symbols;
 use Test::Simple tests=>3;
 
 my ($x, $i) = symbols(qw(x i));
 
 ok(  abs($x+$i*$x)  ==  sqrt(2*$x**2)  );
 ok(  abs($x+$i*$x)  !=  sqrt(2*$x**3)  );
 ok(  abs($x+$i*$x) <=> 'sqrt(2*$x**2)' );
 


The B<abs> operator returns the modulus (length) of its right hand side.

=head4 Complex operators: the B<unit> operator: B<!>       

Example t/unit.t

 #!perl -w
 #______________________________________________________________________
 # Symbolic algebra: examples: unit operator.
 # PhilipRBrenan@yahoo.com, 2004, Perl License.
 #______________________________________________________________________
 
 use Math::Algebra::Symbols;
 use Test::Simple tests=>4;
 
 my ($i) = symbols(qw(i));
 
 ok(  !$i      == $i                         );
 ok(  !$i     <=> 'i'                        );
 ok(  !($i+1) <=>  '1/(sqrt(2))+i/(sqrt(2))' );
 ok(  !($i-1) <=> '-1/(sqrt(2))+i/(sqrt(2))' );
 


The B<!> operator returns a complex number of unit length pointing in
the same direction as its right hand side.

=head3 Equation Manipulation Operators

=head4 Equation Manipulation Operators: B<Simplify> operator: B<+=>

Example t/simplify.t

 #!perl -w
 #______________________________________________________________________
 # Symbolic algebra: examples: simplify.
 # PhilipRBrenan@yahoo.com, 2004, Perl License.
 #______________________________________________________________________
 
 use Math::Algebra::Symbols;
 use Test::Simple tests=>2;
  
 my ($x) = symbols(qw(x));
 
 ok(  ($x**8 - 1)/($x-1)  ==  $x+$x**2+$x**3+$x**4+$x**5+$x**6+$x**7+1  );      
 ok(  ($x**8 - 1)/($x-1) <=> '$x+$x**2+$x**3+$x**4+$x**5+$x**6+$x**7+1' );      
 


The simplify operator B<+=> is a synonym for the
L<simplify()|/"simplifying_equations:_simplify()"> method, if and only
if, the target on the left hand side initially has a value of undef.

Admittedly this is very strange behavior: it arises due to the shortage
of over-rideable operators in Perl: in particular it arises due to the
shortage of over-rideable unary operators in Perl. Never-the-less: this
operator is useful as can be seen in the L<Synopsis|/"synopsis">, and
the desired pre-condition can always achieved by using B<my>.

=head4 Equation Manipulation Operators: B<Solve> operator: B<E<gt>> 

Example t/solve2.t

 #!perl -w
 #______________________________________________________________________
 # Symbolic algebra: examples: simplify.
 # PhilipRBrenan@yahoo.com, 2004, Perl License.
 #______________________________________________________________________
 
 use Math::Algebra::Symbols;
 use Test::Simple tests=>2;
  
 my ($t) = symbols(qw(t));
 
 my $rabbit  = 10 + 5 * $t;
 my $fox     = 7 * $t * $t;
 my ($a, $b) = @{($rabbit eq $fox) > $t};
 
 ok( "$a" eq  '1/14*sqrt(305)+5/14'  );      
 ok( "$b" eq '-1/14*sqrt(305)+5/14'  );      
 


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

Example t/sinCos2.t

 #!perl -w
 #______________________________________________________________________
 # Symbolic algebra: examples: methods.
 # PhilipRBrenan@yahoo.com, 2004, Perl License.
 #______________________________________________________________________
 
 use Math::Algebra::Symbols;
 use Test::Simple tests=>1;
 
 my ($x, $y) = symbols(qw(x y));
 
 ok( (sin($x)**2 == (1-cos(2*$x))/2) );
 


The trigonometric functions B<cos>, B<sin>, B<tan>, B<sec>, B<csc>,
B<cot> are available, either as exports to the caller's name space, or
as methods.

=head4 Hyperbolic functions

Example t/tanh.t

 #!perl -w
 #______________________________________________________________________
 # Symbolic algebra: examples: methods.
 # PhilipRBrenan@yahoo.com, 2004, Perl License.
 #______________________________________________________________________
 
 use Math::Algebra::Symbols hyper=>1;
 use Test::Simple tests=>1;
 
 my ($x, $y) = symbols(qw(x y));
 
 ok( tanh($x+$y)==(tanh($x)+tanh($y))/(1+tanh($x)*tanh($y)));
 


The hyperbolic functions B<cosh>, B<sinh>, B<tanh>, B<sech>, B<csch>,
B<coth> are available, either as exports to the caller's name space, or
as methods.

=head3 Complex functions

=head4 Complex functions: B<re> and B<im>       

 use Math::Algebra::Symbols complex=>1;

Example t/reIm.t

 #!perl -w
 #______________________________________________________________________
 # Symbolic algebra: examples: methods.
 # PhilipRBrenan@yahoo.com, 2004, Perl License.
 #______________________________________________________________________
 
 use Math::Algebra::Symbols;
 use Test::Simple tests=>2;
 
 my ($x, $i) = symbols(qw(x i));
 
 ok( ($i*$x)->re   <=>  0    );
 ok( ($i*$x)->im   <=>  '$x' );
 


The B<re> and B<im> functions return an expression which represents the
real and imaginary parts of the expression, assuming that symbolic
variables represent real numbers.

=head4 Complex functions: B<dot> and B<cross>       

Example t/dotCross.t

 #!perl -w
 #______________________________________________________________________
 # Symbolic algebra: examples: methods.
 # PhilipRBrenan@yahoo.com, 2004, Perl License.
 #______________________________________________________________________
 
 use Math::Algebra::Symbols;
 use Test::Simple tests=>2;
 
 my $i = symbols(qw(i));
 
 ok( ($i+1)->cross($i-1)   <=>  2 );
 ok( ($i+1)->dot  ($i-1)   <=>  0 );
 


The B<dot> and B<cross> operators are available as functions, either as
exports to the caller's name space, or as methods.

=head4 Complex functions: B<conjugate>, B<modulus> and B<unit>       

Example t/conjugate2.t

 #!perl -w
 #______________________________________________________________________
 # Symbolic algebra: examples: methods.
 # PhilipRBrenan@yahoo.com, 2004, Perl License.
 #______________________________________________________________________
 
 use Math::Algebra::Symbols;
 use Test::Simple tests=>3;
 
 my $i = symbols(qw(i));
 
 ok( ($i+1)->unit      <=>  '1/(sqrt(2))+i/(sqrt(2))' );
 ok( ($i+1)->modulus   <=>  'sqrt(2)'                 );
 ok( ($i+1)->conjugate <=>  '1-i'                     );
 


The B<conjugate>, B<abs> and B<unit> operators are available as
functions: B<conjugate>, B<modulus> and B<unit>, either as exports to
the caller's name space, or as methods. The confusion over the naming of:
the B<abs> operator being the same as the B<modulus> complex function;
arises over the limited set of Perl operator names available for
overloading.


=head2 Methods

=head3 Methods for manipulating Equations             

=head4 Simplifying equations: B<simplify()>

Example t/simplify2.t

 #!perl -w
 #______________________________________________________________________
 # Symbolic algebra: examples: simplify.
 # PhilipRBrenan@yahoo.com, 2004, Perl License.
 #______________________________________________________________________
 
 use Math::Algebra::Symbols;
 use Test::Simple tests=>2;
  
 my ($x) = symbols(qw(x));
  
 my $y  = (($x**8 - 1)/($x-1))->simplify();  # Simplify method 
 my $z +=  ($x**8 - 1)/($x-1);               # Simplify via +=
 
 ok( "$y" eq '$x+$x**2+$x**3+$x**4+$x**5+$x**6+$x**7+1' );
 ok( "$z" eq '$x+$x**2+$x**3+$x**4+$x**5+$x**6+$x**7+1' );
 


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

Example t/sub.t

 #!perl -w
 #______________________________________________________________________
 # Symbolic algebra: examples: expression substitution for a variable.
 # PhilipRBrenan@yahoo.com, 2004, Perl License.
 #______________________________________________________________________
 
 use Math::Algebra::Symbols;
 use Test::Simple tests=>2;
 
 my ($x, $y) = symbols(qw(x y));
  
 my $e  = 1+$x+$x**2/2+$x**3/6+$x**4/24+$x**5/120;
 
 ok(  $e->sub(x=>$y**2, z=>2)  <=> '$y**2+1/2*$y**4+1/6*$y**6+1/24*$y**8+1/120*$y**10+1'  );
 ok(  $e->sub(x=>1)            <=>  '163/60');          
 


The B<sub()> function example on line B<#1> demonstrates replacing
variables with expressions. The replacement specified for B<z> has no
effect as B<z> is not present in this equation.

Line B<#2> demonstrates the resulting rational fraction that arises when
all the variables have been replaced by constants. This package does not
convert fractions to decimal expressions in case there is a loss of
accuracy, however:

 my $e2 = $e->sub(x=>1);
 $result = eval "$e2";

or similar will produce approximate results.

At the moment only variables can be replaced by expressions. Mike
Schilli, m@perlmeister.com, has proposed that substitutions for
expressions should also be allowed, as in:

 $x/$y => $z


=head4 Solving equations: B<solve()>

Example t/solve1.t

 #!perl -w
 #______________________________________________________________________
 # Symbolic algebra: examples: simplify.
 # PhilipRBrenan@yahoo.com, 2004, Perl License.
 #______________________________________________________________________
 
 use Math::Algebra::Symbols;
 use Test::Simple tests=>3;
  
 my ($x, $v, $t) = symbols(qw(x v t));
 
 ok(   ($v eq $x / $t)->solve(qw(x in terms of v t))  ==  $v*$t  );      
 ok(   ($v eq $x / $t)->solve(qw(x in terms of v t))  !=  $v/$t  );      
 ok(   ($v eq $x / $t)->solve(qw(x in terms of v t)) <=> '$v*$t' );      
 


B<solve()> assumes that the equation on the left hand side is equal to
zero, applies various simplifications, then attempts to rearrange the
equation to obtain an equation for the first variable in the parameter
list assuming that the other terms mentioned in the parameter list are
known constants. There may of course be other unknown free variables in
the equation to be solved: the proposed solution is automatically tested
against the original equation to check that the proposed solution
removes these variables, an error is reported via B<die()> if it does not.

Example t/solve.t

 #!perl -w -I..
 #______________________________________________________________________
 # Symbolic algebra: quadratic equation.
 # PhilipRBrenan@yahoo.com, 2004, Perl License.
 #______________________________________________________________________
 
 use Math::Algebra::Symbols;
 use Test::Simple tests => 2;
 
 my ($x) = symbols(qw(x));
 
 my  $p = $x**2-5*$x+6;        # Quadratic polynomial
 my ($a, $b) = @{($p > $x )};  # Solve for x
 
 print "x=$a,$b\n";            # Roots
 
 ok($a == 2);
 ok($b == 3);
 


If there are multiple solutions, (as in the case of polynomials), B<solve()>
returns an array of symbolic expressions containing the solutions.

=head3 Methods for performing Calculus

=head4 Differentiation: B<d()>

Example t/differentiation.t

 #!perl -w -I..
 #______________________________________________________________________
 # Symbolic algebra.
 # PhilipRBrenan@yahoo.com, 2004, Perl License.
 #______________________________________________________________________
 
 use Math::Algebra::Symbols;
 use Test::More tests => 5;
 
 $x = symbols(qw(x));
            
 ok(  sin($x)    ==  sin($x)->d->d->d->d);
 ok(  cos($x)    ==  cos($x)->d->d->d->d);
 ok(  exp($x)    ==  exp($x)->d($x)->d('x')->d->d);
 ok( (1/$x)->d   == -1/$x**2);
 ok(  exp($x)->d->d->d->d <=> 'exp($x)' );
 


B<d()> differentiates the equation on the left hand side by the named
variable.

The variable to be differentiated by may be explicitly specified,
either as a string or as single symbol; or it may be heuristically
guessed as follows:

If the equation to be differentiated refers to only one symbol, then
that symbol is used. If several symbols are present in the equation, but
only one of B<t>, B<x>, B<y>, B<z> is present, then that variable is
used in honor of Newton, Leibnitz, Cauchy.

=head2 Example of Equation Solving: the focii of a hyperbola:

 use Math::Algebra::Symbols;

 my ($a, $b, $x, $y, $i, $o) = symbols(qw(a b x y i 1));

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

=head1 EXPORTS

 use Math::Algebra::Symbols
   symbols=>'S',
   trig   => 1,
   hyper  => 1,
   complex=> 1;

=over

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

The B<Symbols> packages manipulate a sum of products representation of
an algebraic equation. The B<Symbols> package is the user interface to
the functionality supplied by the B<Symbols::Sum> and B<Symbols::Term>
packages.

=head2 Math::Algebra::Symbols::Term

B<Symbols::Term> represents a product term. A product term consists of the
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

for which package B<Symbols::Sum> is required. 


=head2 Math::Algebra::Symbols::Sum

B<Symbols::Sum> represents a sum of product terms supplied by
B<Symbols::Term> and thus behaves as a polynomial. Operations such as
equation solving and differentiation are applied at this level.

The main benefit of programming B<Symbols::Term> and B<Symbols::Sum> as two
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





=head2 Credits

=head3 Author

philiprbrenan@yahoo.com

=head3 Copyright

philiprbrenan@yahoo.com, 2004

=head3 License

Perl License.


=cut
