
=head1 Terms

Symbolic Algebra in Pure Perl: terms.

See user manual L</NAME>.

A term represents a product of: variables, coefficents, divisors,
square roots, exponentials, and logs.

PhilipRBrenan@yahoo.com, 2004, Perl License.

=cut


package Math::Algebra::Symbols::Term;
$VERSION=1.21;
use Carp;
use Math::BigInt;  
#HashUtil use Hash::Util qw(lock_hash); 
use Scalar::Util qw(weaken);


=head2 Constructors


=head3 new

Constructor

=cut 


sub new
 {bless {c=>1, d=>1, i=>0, v=>{}, sqrt=>undef, divide=>undef, exp=>undef, log=>undef};
 }


=head3 newFromString

New from String

=cut 


sub newFromString($)
 {my ($a) = @_;
  return $zero unless $a;
  my $A = $a; 

  for(;$A =~ /(\d+)\.(\d+)/;)
   {my $i = $1;
    my $j = $2;
    my $l = '0' x length($j);
#   carp "Replacing $i.$j with $i$j\/1$l in $A";
    $A =~ s/$i\.$j/$i$j\/1$l/;
   }

  if  ($A  =~ /^\s*([+-])?(\d+)?(?:\/(\d+))?(i)?(?:\*)?(.*)$/)
   {my $c  =  '';
       $c  =  '-'.$c if $1 and $1 eq '-';
       $c .=  $2     if $2;
       $c  = '1'     if $c eq '';   
       $c  = '-1'    if $c eq '-';   
    my $d  =  '';
       $d  =  $3     if $3;
       $d  =   1     if $d eq '';
    my $i  =   0;
       $i  =   1     if $4;

    my $z = new()->c($c)->d($d)->i($i);

    my $b = $5;
    for (;$b =~ /^([a-z]+)(?:\*\*)?(\d+)?(?:\*)?(.*)$/i;)
     {$b = $3;
      $z->{v}{$1} = $2 if     defined($2);
      $z->{v}{$1} = 1  unless defined($2);
     }

    croak "Cannot parse: $a" if $A eq $b;
    croak "Cannot parse: $b in $a" if $b;
    return $z->z;
   }
  croak "Unable to parse $a";
 }


=head3 n

Short name for L</newFromString>

=cut 


sub n($)
 {newFromString($_[0]);
 }


=head3 newFromStrings

New from Strings

=cut 


sub newFromStrings(@)
 {return $zero->clone() unless scalar(@_);
  map {newFromString($_)} @_;
 }


=head3 gcd

Greatest Common Divisor.

=cut 


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
 }


=head3 lcm

Least common multiple.  

=cut 


sub lcm($$)
 {my $x = abs($_[0]);
  my $y = abs($_[1]);
  return $x*$y if $x == 1 or $y == 1; 
  $x*$y / gcd($x, $y);
 }


=head3 isTerm

Confirm type

=cut 


sub isTerm($) {1}; 


=head3 intCheck

Integer check

=cut 


sub intCheck($$) 
 {my ($i, $m) = @_;
  return $i if $i == 1;
  $i =~ /^[\+\-]?\d+/ or die "Integer required for $m not $i";
  return Math::BigInt->new($i) if $i > 10_000_000;
  $i;
 }


=head3 c

Coefficient

=cut 


sub c($;$) 
 {my ($t) = @_;
  return $t->{c} unless @_ > 1;

  $t->{c} = ($_[1] == 1 ? $_[1] : intCheck($_[1], 'c'));
  $t;
 }


=head3 d

Divisor

=cut 


sub d($;$) 
 {my ($t) = @_;
  return $t->{d} unless @_ > 1;

  $t->{d} = ($_[1] == 1 ? $_[1] : intCheck($_[1], 'd'));
  $t;
 }


=head3 timesInt

Multiply term by integer

=cut 


sub timesInt($$) 
 {my ($t) = @_;
  my $m = ($_[1] ? $_[1] : intCheck($_[1], 'times'));

  $t->{c} *= $m;
  if ($t->{d} > 1)
   {my $g = gcd($t->{c}, $t->{d});
    if ($g > 1)
     {$t->{d} /= $g;
      $t->{c} /= $g;
     }
   }       
  $t;
 }


=head3 divideInt

Divide term by integer

=cut 


sub divideInt($$) 
 {my ($t) = @_;
  my $d = ($_[1] == 1 ? $_[1] : intCheck($_[1], 'divide'));
  $d != 0  or die "Cannot divide by zero";

  $t->{d} *= abs($d);
  my $g = gcd($t->{d}, $t->{c});
  if ($g > 1)
   {$t->{d} /= $g;
    $t->{c} /= $g;
   }

  $t->{c} = - $t->{c} if $d < 0;
  $t;
 }


=head3 negate

Negate term

=cut 


sub negate($) 
 {my ($t) = @_;
  $t->{c} = -$t->{c};
  $t;
 }


=head3 isZero

Zero?

=cut 


sub isZero($) 
 {my ($t) = @_;
  exists $t->{z} or die "Testing unfinalized term";
  $t->{id} == $zero->{id};
 }


=head3 notZero

Not Zero?

=cut 


sub notZero($) {return !isZero($_[0])} 


=head3 isOne

One?

=cut 


sub isOne($) 
 {my ($t) = @_;
  exists $t->{z} or die "Testing unfinalized term";
  $t->{id} == $one->{id};
 }


=head3 notOne

Not One?

=cut 


sub notOne($) {return !isOne($_[0])} 


=head3 isMinusOne

Minus One?

=cut 


sub isMinusOne($) 
 {my ($t) = @_;
  exists $t->{z} or die "Testing unfinalized term";
  $t->{id} == $mOne->{id};
 }


=head3 notMinusOne

Not Minus One?

=cut 


sub notMinusOne($) {return !isMinusOne($_[0])} 


=head3 i

Get/Set i - sqrt(-1)

=cut 


sub i($;$) 
 {my ($t) = @_;

  return $t->{i} unless(@_) > 1;

  my $i = ($_[1] == 1 ? $_[1] : intCheck($_[1], 'i'));

  my $i4  = $i % 4;
  $t->{i} = $i % 2;
  $t->{c} = -$t->{c} if $i4 == 2 or $i4 == 3;
  $t;
 }


=head3 iby

i by power: multiply a term by a power of i

=cut 


sub iby($$) 
 {my ($t, $p) = @_;

  $t->i($p+$t->{i});
  $t;
 }


=head3 Divide

Get/Set divide by.

=cut 


sub Divide($;$) 
 {my ($t, $d) = @_;
  return $t->{divide} unless @_ > 1;
  $t->{divide} = $d;
  $t;
 }


=head3 removeDivide

Remove divide

=cut 


sub removeDivide($) 
 {my ($t) = @_;
  my $z = $t->clone;
  delete $z->{divide};
  $z->z;
 }


=head3 Sqrt

Get/Set square root.

=cut 


sub Sqrt($;$) 
 {my ($t, $s) = @_;
  return $t->{sqrt} unless @_ > 1;
  $t->{sqrt} = $s;
  $t;
 }


=head3 removeSqrt

Remove square root.

=cut 


sub removeSqrt($) 
 {my ($t) = @_;
  my $z = $t->clone;
  delete $z->{sqrt};
  $z->z;
 }


=head3 Exp

Get/Set exp

=cut 


sub Exp($;$) 
 {my ($t, $e) = @_;
  return $t->{exp} unless @_ > 1;
  $t->{exp} = $e;
  $t;
 }


=head3 Log

# Get/Set log

=cut 


sub Log($$) 
 {my ($t, $l) = @_;
  return $t->{log} unless @_ > 1;
  $t->{log} = $l;
  $t;
 }


=head3 vp

Get/Set variable power.

On get: returns the power of a variable, or zero if the variable is not
present in the term.

On set: Sets the power of a variable. If the power is zero, removes the
variable from the term. =cut

=cut


sub vp($$;$) 
 {my ($t, $v) = @_;
# $v =~ /^[a-z]+$/i or die "Bad variable name $v";

  return exists($t->{v}{$v}) ? $t->{v}{$v} : 0 if @_ == 2; 

  my $p = ($_[2] == 1 ? $_[2] : intCheck($_[2], 'vp'));
  $t->{v}{$v} = $p   if $p;
  delete $t->{v}{$v} unless $p;
  $t;
 }


=head3 v

Get all variables mentioned in the term.  Variables to power zero
should have been removed by L</vp>.

=cut 


sub v($) 
 {my ($t) = @_;
  return keys %{$t->{v}};
 }


=head3 clone

Clone a term. The existing term must be finalized, see L</z>: the new
term will not be finalized, allowing modifications to be made to it.

=cut 


sub clone($) 
 {my ($t) = @_;
  $t->{z} or die "Attempt to clone unfinalized  term";
  my $c   = bless {%$t};
  $c->{v} = {%{$t->{v}}};
  delete @$c{qw(id s z)};
  $c;
 }


=head3 split

Split a term into its components

=cut 


sub split($) 
 {my ($t) = @_;
  my $c = $t->clone;
  my @c = @$c{qw(sqrt divide exp log)};
          @$c{qw(sqrt divide exp log)} = ((undef()) x 4);
 (t=>$c, s=>$c[0], d=>$c[1], e=>$c[2], l=>$c[3]);
 }


=head3 signature

Sign the term. Used to optimize addition.
Fix the problem of adding different logs

=cut 


sub signature($) 
 {my ($t) = @_;
  my $s = '';
  $s .= sprintf("%010d", $t->{v}{$_}) . $_ for keys %{$t->{v}};
  $s .= '(divide'. $t->{divide} .')' if defined($t->{divide});
  $s .= '(sqrt'.   $t->{sqrt}   .')' if defined($t->{sqrt});
  $s .= '(exp'.    $t->{exp}    .')' if defined($t->{exp});
  $s .= '(log'.    $t->{log}    .')' if defined($t->{log});
  $s .= 'i' if $t->{i} == 1;
  $s  = '1' if $s eq '';
  $s;
 }


=head3 getSignature

Get the signature of a term

=cut 


sub getSignature($) 
 {my ($t) = @_;
  exists $t->{z} ? $t->{z} : die "Attempt to get signature of unfinalized term";
 }


=head3 add

Add two finalized terms, return result in new term or undef.

=cut 


sub add($$) 
 {my ($a, $b) = @_;

  $a->{z} and $b->{z} or 
    die "Attempt to add unfinalized terms";

  return undef unless $a->{z} eq $b->{z};
  return $a->clone->timesInt(2)->z if $a == $b;

  my $z = $a->clone;
  my $c = $a->{c} * $b->{d}
        + $b->{c} * $a->{d};
  my $d = $a->{d} * $b->{d};
  return $zero if $c == 0;

  $z->c($c)->d(1)->divideInt($d)->z;
 }


=head3 subtract

Subtract two finalized terms, return result in new term or undef.

=cut 


sub subtract($$) 
 {my ($a, $b) = @_;

  $a->{z} and $b->{z} or 
    die "Attempt to subtract unfinalized terms";

  return $zero                if $a == $b;
  return $a                   if $b == $zero;
  return $b->clone->negate->z if $a == $zero;
  return undef unless $a->{z} eq $b->{z};

  my $z = $a->clone;
  my $c = $a->{c} * $b->{d}
        - $b->{c} * $a->{d};
  my $d = $a->{d} * $b->{d};

  $z->c($c)->d(1)->divideInt($d)->z;
 }


=head3 multiply

Multiply two finalized terms, return the result in a new term or undef

=cut 


sub multiply($$) 
 {my ($a, $b) = @_;

  $a->{z} and $b->{z} or 
    die "Attempt to multiply unfinalized terms";

# Check
  return undef if
   (defined($a->{divide}) and defined($b->{divide})) or
   (defined($a->{sqrt}  ) and defined($b->{sqrt}))   or
   (defined($a->{exp}   ) and defined($b->{exp}))    or
   (defined($a->{log}   ) and defined($b->{log}));

# cdi
  my $c = $a->{c} * $b->{c};
  my $d = $a->{d} * $b->{d};
  my $i = $a->{i} + $b->{i};
     $c = -$c, $i = 0 if $i == 2;
  my $z = $a->clone->c($c)->d(1)->divideInt($d)->i($i);

# v
# for my $v($b->v)
#  {$z->vp($v, $z->vp($v)+$b->vp($v));
#  }

  for my $v(keys(%{$b->{v}}))
   {$z->vp($v, (exists($z->{v}{$v}) ? $z->{v}{$v} : 0)+$b->{v}{$v});
   }

# Divide, sqrt, exp, log
  $z->{divide} = $b->{divide} unless defined($a->{divide});
  $z->{sqrt}   = $b->{sqrt}   unless defined($a->{sqrt});  
  $z->{exp}    = $b->{exp}    unless defined($a->{exp});   
  $z->{log}    = $b->{log}    unless defined($a->{log});    

# Result
  $z->z;
 }


=head3 divide2

Divide two finalized terms, return the result in a new term or undef

=cut 


sub divide2($$) 
 {my ($a, $b) = @_;

  $a->{z} and $b->{z} or 
    die "Attempt to divide unfinalized terms";

# Check
  return undef if
   (defined($b->{divide}) and (!defined($a->{divide}) or $a->{divide}->id != $b->{divide}->id));
  return undef if
   (defined($b->{sqrt}  ) and (!defined($a->{sqrt}  ) or $a->{sqrt}  ->id != $b->{sqrt}  ->id));
  return undef if
   (defined($b->{exp}   ) and (!defined($a->{exp}   ) or $a->{exp}   ->id != $b->{exp}   ->id));
  return undef if
   (defined($b->{log}   ) and (!defined($a->{log}   ) or $a->{log}   ->id != $b->{log}   ->id));

# cdi
  my $c = $a->{c} * $b->{d};
  my $d = $a->{d} * $b->{c};
  my $i = $a->{i} - $b->{i};
     $c = -$c, $i = 1 if $i == -1;
  my $g = gcd($c, $d);
  $c /= $g;
  $d /= $g;
  my $z = $a->clone->c($c)->d(1)->divideInt($d)->i($i);

# v
  for my $v($b->v)
   {$z->vp($v, $z->vp($v)-$b->vp($v));
   }

# Sqrt, divide, exp, log
  delete $z->{divide} if defined($a->{divide}) and defined($b->{divide}); 
  delete $z->{sqrt  } if defined($a->{sqrt  }) and defined($b->{sqrt  }); 
  delete $z->{exp   } if defined($a->{exp   }) and defined($b->{exp   }); 
  delete $z->{log   } if defined($a->{log   }) and defined($b->{log   }); 
  

# Result
  $z->z;
 }


=head3 invert

Invert a term

=cut 


sub invert($) 
 {my ($t) = @_;

  $t->{z} or die "Attempt to invert unfinalized term";

# Check
  return undef if
    $t->{divide} or
    $t->{sqrt}   or
    $t->{exp}    or
    $t->{log};

# cdi
  my ($c, $d, $i) = ($t->{c}, $t->{d}, $t->{i});
  $c = -$c if $i;
  my $z = clone($t)->c($d)->d(1)->divideInt($c)->i($i);

# v
  for my $v($z->v)
   {$z->vp($v, $z->vp($v));
   }

# Result
  $z->z;
 }


=head3 power

Take power of term

=cut 


sub power($$) 
 {my ($a, $b) = @_;

  $a->{z} and $b->{z} or die "Attempt to take power of unfinalized term";

# Check
  return $one if $a == $one or $b == $zero; 
  return undef if
    $a->{divide} or
    $a->{sqrt}   or
    $a->{exp}    or
    $a->{log};

  return undef if
    $b->{d} != 1 or
    $b->{i} == 1 or
    $b->{divide} or
    $b->{sqrt}   or
    $b->{exp}    or
    $b->{log};

# cdi
  my ($c, $d, $i) = ($a->{c}, $a->{d}, $a->{i});

  my  $p = $b->{c};
  if ($p < 0)
   {$a = invert($a);
    return undef unless $a;
    $p = -$p;
    return $a if $p == 1; 
   }

  my $z = $a->clone->z;
  $z = $z->multiply($a) for (2..$p);
   
  $i *= $p;
  $z = $z->clone->i($i);

# v
# for my $v($z->v)
#  {$z->vp($v, $p*$z->vp($v));
#  }

# Result
  $z->z;
 }


=head3 sqrt2

Square root of a term

=cut 


sub sqrt2($) 
 {my ($t) = @_;

  $t->{z} or die "Attempt to sqrt unfinalized term";

# Check
  return undef if   $t->{i}      or
                    $t->{divide} or
                    $t->{sqrt}   or
                    $t->{exp}    or
                    $t->{log};

# cd
  my ($c, $d, $i) = ($t->{c}, $t->{d}, 0);
  $c = -$c, $i = 1 if $c < 0;

  my $c2 = sqrt($c);  return undef unless $c2*$c2 == $c;
  my $d2 = sqrt($d);  return undef unless $d2*$d2 == $d;

  my $z = clone($t)->c($c2)->d($d2)->i($i);

# v
  for my $v($t->v)
   {my $p = $z->vp($v);
    return undef unless $p % 2 == 0; 
    $z->vp($v, $p/2);
   }

# Result
  $z->z;
 }


=head3 exp2

Exponential of a term

=cut 


sub exp2($) 
 {my ($t) = @_;

  $t->{z} or die "Attempt to use unfinalized term in exp";

  return $one  if     $t == $zero;
  return undef if     $t->{divide} or
                      $t->{sqrt}   or
                      $t->{exp}    or
                      $t->{log};
  return undef unless $t->{i} == 1;
  return undef unless $t->{d} == 1 or
                      $t->{d} == 2 or
                      $t->{d} == 4;
  return undef unless scalar(keys(%{$t->{v}})) == 1 and
                      exists($t->{v}{pi})           and
                             $t->{v}{pi}       == 1;

  my $c = $t->{c};
  my $d = $t->{d};
  $c *= 2 if $d == 1;
  $c %= 4;

  return $one  if $c == 0;
  return $i    if $c == 1;
  return $mOne if $c == 2;
  return $mI   if $c == 3;
 }


=head3 sin2

Sine of a term           

=cut 


sub sin2($) 
 {my ($t) = @_;

  $t->{z} or die "Attempt to use unfinalized term in sin";

  return $zero if   $t == $zero;
  return undef if   $t->{divide} or
                    $t->{sqrt}   or
                    $t->{exp}    or
                    $t->{log};
  return undef unless $t->{i} == 0;
  return undef unless scalar(keys(%{$t->{v}})) == 1;
  return undef unless exists($t->{v}{pi});
  return undef unless $t->{v}{pi} == 1;

  my $c = $t->{c};
  my $d = $t->{d};
  return undef unless $d== 1 or $d == 2 or $d == 3 or $d == 6;
  $c *= 6 if $d == 1;
  $c *= 3 if $d == 2;
  $c *= 2 if $d == 3;
  $c = $c % 12;

  return $zero  if $c ==  0;
  return $half  if $c ==  1;
  return undef  if $c ==  2;
  return $one   if $c ==  3;
  return undef  if $c ==  4;
  return $half  if $c ==  5;
  return $zero  if $c ==  6;
  return $mHalf if $c ==  7;
  return $undef if $c ==  8;
  return $mOne  if $c ==  9;
  return $undef if $c == 10;
  return $mHalf if $c == 11;
  return $zero  if $c == 12;
 }


=head3 cos2

Cosine of a term           

=cut 


sub cos2($) 
 {my ($t) = @_;

  $t->{z} or die "Attempt to use unfinalized term in cos";

  return $one  if   $t == $zero;
  return undef if   $t->{divide} or
                    $t->{sqrt}   or
                    $t->{exp}    or
                    $t->{log};
  return undef unless $t->{i} == 0;
  return undef unless scalar(keys(%{$t->{v}})) == 1;
  return undef unless exists($t->{v}{pi});
  return undef unless $t->{v}{pi} == 1;

  my $c = $t->{c};
  my $d = $t->{d};
  return undef unless $d== 1 or $d == 2 or $d == 3 or $d == 6;
  $c *= 6 if $d == 1;
  $c *= 3 if $d == 2;
  $c *= 2 if $d == 3;
  $c = $c % 12;

  return $half  if $c == 10;
  return $undef if $c == 11;
  return $one   if $c == 12;
  return $one   if $c ==  0;
  return undef  if $c ==  1;
  return $half  if $c ==  2;
  return $zero  if $c ==  3;
  return $mHalf if $c ==  4;
  return $undef if $c ==  5;
  return $mOne  if $c ==  6;
  return $undef if $c ==  7;
  return $mHalf if $c ==  8;
  return $zero  if $c ==  9;
 }


=head3 log2

Log of a term

=cut 


sub log2($) 
 {my ($a) = @_;

  $a->{z} or die "Attempt to use unfinalized term in log";

  return $zero if $a == $one;
  return undef;
 }


=head3 id

Get Id of a term

=cut 


sub id($) 
 {my ($t) = @_;
  $t->{id} or die "Term $t not yet finalized";
  $t->{id};
 }


=head3 zz

# Check term finalized

=cut 


sub zz($) 
 {my ($t) = @_;
  $t->{z} or die "Term $t not yet finalized";
  $t;
 }


=head3 z

Finalize creation of the term. Once a term has been finalized, it
becomes readonly, which allows optimization to be performed. =cut

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
  weaken($z{$p}); # Greatly reduces memory usage

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

Print

=cut 


sub print($) 
 {my ($t) = @_;
  return $t->{s} if defined($t->{s});
  my @k = keys %{$t->{v}};
  my $v = $t->{v};
  my $s = '';
  $s .=     $t->{c};
  $s .= '/'.$t->{d}                   if $t->{d} != 1;
  $s .= '*i'                          if $t->{i} == 1;
  $s .= '*$'.$_                       for grep {$v->{$_} ==  1} @k;
  $s .= '/$'.$_                       for grep {$v->{$_} == -1} @k;
  $s .= '*$'.$_.'**'. $v->{$_}        for grep {$v->{$_}  >  1} @k;
  $s .= '/$'.$_.'**'.-$v->{$_}        for grep {$v->{$_}  < -1} @k;
  $s .= '/('.       $t->{divide} .')' if $t->{divide};
  $s .= '*sqrt('.   $t->{sqrt}   .')' if $t->{sqrt};
  $s .= '*exp('.    $t->{exp}    .')' if $t->{exp};
  $s .= '*log('.    $t->{log}    .')' if $t->{log};
  $s;
 }


=head3 constants

Useful constants

=cut 


$zero  = new()->c(0)->z;           sub zero () {$zero} 
$one   = new()->z;                 sub one  () {$one}
$two   = new()->c(2)->z;           sub two  () {$two}
$mOne  = new()->c(-1)->z;          sub mOne () {$mOne}
$i     = new()->i(1)->z;           sub pI   () {$pI}
$mI    = new()->c(-1)->i(1)->z;    sub mI   () {$mI}
$half  = new()->c( 1)->d(2)->z;    sub half () {$half}
$mHalf = new()->c(-1)->d(2)->z;    sub mHalf() {$mHalf}
$pi    = new()->vp('pi', 1)->z;    sub pi   () {$pi}


=head2 import

Export L</newFromStrings> to calling package with a name specifed by the
caller, or as B<term()> by default. =cut

=cut


sub import
 {my %P = (program=>@_);
  my %p; $p{lc()} = $P{$_} for(keys(%P));

#_______________________________________________________________________
# New symbols term constructor - export to calling package.
#_______________________________________________________________________

  my $s = "pack"."age XXXX;\n". <<'END';
no warnings 'redefine';
sub NNNN
 {return SSSSnewFromStrings(@_);
 }
use warnings 'redefine';
END

#_______________________________________________________________________
# Export to calling package.
#_______________________________________________________________________

  my $name   = 'term';
     $name   = $p{term} if exists($p{term});
  my ($main) = caller();
  my $pack   = __PACKAGE__.'::';   

  $s=~ s/XXXX/$main/g;
  $s=~ s/NNNN/$name/g;
  $s=~ s/SSSS/$pack/g;
  eval($s);

#_______________________________________________________________________
# Check options supplied by user
#_______________________________________________________________________

  delete @p{qw(program terms)};

  croak "Unknown option(s) for ". __PACKAGE__ .": ". join(' ', keys(%p))."\n\n". <<'END' if keys(%p);

Valid options are:

  terms=>'name' Desired name of the constructor routine for creating
                new terms.  The default is 'term'.
END
 }


=head2 Operators


=head3 Operator Overloads

Operator Overloads

=cut 


use overload
 '+'     =>\&add3,
 '-'     =>\&negate3,
 '*'     =>\&multiply3,
 '/'     =>\&divide3,
 '**'    =>\&power3,
 '=='    =>\&equals3,
 'sqrt'  =>\&sqrt3,
 'exp'   =>\&exp3,
 'log'   =>\&log3,
 'sin'   =>\&sin3,
 'cos'   =>\&cos3,
 '""'    =>\&print3,
 fallback=>1;


=head3 add3

Add operator.

=cut 


sub add3
 {my ($a, $b) = @_;
  $b = newFromString("$b") unless ref($b) eq __PACKAGE__;
  $a->{z} and $b->{z} or die "Add using unfinalized terms";
  $a->add($b);
 }


=head3 negate3

Negate operator.

=cut 


sub negate3
 {my ($a, $b, $c) = @_;

  if (defined($b))
   {$b = newFromString("$b") unless ref($b) eq __PACKAGE__;
    $a->{z} and $b->{z} or die "Negate using unfinalized terms";
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
  $a->{z} and $b->{z} or die "Multiply using unfinalized terms";
  $a->multiply($b);
 }


=head3 divide3

Divide operator.

=cut 


sub divide3
 {my ($a, $b, $c) = @_;
  $b = newFromString("$b") unless ref($b) eq __PACKAGE__;
  $a->{z} and $b->{z} or die "Divide using unfinalized terms";
  return $b->divide2($a) if     $c;
  return $a->divide2($b) unless $c;
 }


=head3 power3

Power operator.

=cut 


sub power3
 {my ($a, $b) = @_;
  $b = newFromString("$b") unless ref($b) eq __PACKAGE__;
  $a->{z} and $b->{z} or die "Power using unfinalized terms";
  $a->power($b);
 }


=head3 equals3

Equals operator.

=cut 


sub equals3
 {my ($a, $b) = @_;
  if (ref($b) eq __PACKAGE__)
   {$a->{z} and $b->{z} or die "Equals using unfinalized terms";
    return $a->{id} == $b->{id};
   }
  else
   {$a->{z} or die "Equals using unfinalized terms";
    return $a->print eq "$b";
   }
 }


=head3 print3

Print operator.

=cut 


sub print3
 {my ($a) = @_;
  $a->{z} or die "Print of unfinalized term";
  $a->print();
 }


=head3 sqrt3

Square root operator.

=cut 


sub sqrt3
 {my ($a) = @_;
  $a->{z} or die "Sqrt of unfinalized term";
  $a->sqrt2();
 }


=head3 exp3

Exponential operator.

=cut 


sub exp3
 {my ($a) = @_;
  $a->{z} or die "Exp of unfinalized term";
  $a->exp2();
 }


=head3 sin3

Sine operator.

=cut 


sub sin3
 {my ($a) = @_;
  $a->{z} or die "Sin of unfinalized term";
  $a->sin2();
 }


=head3 cos3

Cosine operator.

=cut 


sub cos3
 {my ($a) = @_;
  $a->{z} or die "Cos of unfinalized term";
  $a->cos2();
 }


=head3 log3

Log operator.

=cut 


sub log3
 {my ($a) = @_;
  $a->{z} or die "Log of unfinalized term";
  $a->log2();
 }


=head2 test

Tests

=cut


sub test()
 {my ($a, $b, $c);
# lockHashes();
  $a = n(0);                $a == $zero                 or die "100";
  $a = n(1);                $a == $one                  or die "101";
  $a = n(2);                $a == $two                  or die "102";
  $b = n(3);                $b == 3                     or die "103";
  $c = $a+$a;               $c == 4                     or die "104";
  $c = $a+$b;               $c == 5                     or die "105";
  $c = $a+$b+$a+$b;         $c == 10                    or die "106";
  $c = $a+1;                $c == 3                     or die "107";
  $c = $a+2;                $c == 4                     or die "108";
  $c = $b-1;                $c == 2                     or die "109";
  $c = $b-2;                $c == 1                     or die "110";
  $c = $b-9;                $c == -6                    or die "111";
  $c = $a/2;                $c == $one                  or die "112";
  $c = $a/4;                $c == '1/2'                 or die "113";
  $c = $a*2/2;              $c == $two                  or die "114";
  $c = $a*2/4;              $c == $one                  or die "115";
  $c = $a**2;               $c == 4                     or die "116";
  $c = $a**10;              $c == 1024                  or die "117";
  $c = sqrt($a**2);         $c == $a                    or die "118";
  $d = n(-1);               $d == -1                    or die "119";
  $c = sqrt($d);            $c == '1*i'                 or die "120";
  $d = n(4);                $d == 4                     or die "121";
  $c = sqrt($d);            $c == 2                     or die "122";
  $c = n('x*y2')/n('a*b2'); $c == '1*$x/$a*$y**2/$b**2' or die "122";

  $a = n('x');              $a == '1*$x'                or die "21";
  $b = n('2*x**2');         $b == '2*$x**2'             or die "22";
  $c = $a+$a;               $c == '2*$x'                or die "23";
  $c = $a+$a+$a;            $c == '3*$x'                or die "24";
  $c = $a-$a;               $c == $zero                 or die "25";
  $c = $a-$a-$a;            $c == '-1*$x'               or die "26";
  $c = $a*$b;               $c == '2*$x**3'             or die "27";
  $c = $a*$b*$a*$b;         $c == '4*$x**6'             or die "28";
  $c = $b/$a;               $c == '2*$x'                or die "29";
  $c = $a**2/$b;

            $c == '1/2'                 or die "29";
  $c = sqrt($a**4/($b/2));  $c == $a                    or die "29";
           
  $a = sin($zero);          $a == -0                    or die "301";
  $a = sin($pi/6);          $a ==  $half                or die "302";
  $a = sin($pi/2);          $a == 1                     or die "303";
  $a = sin(5*$pi/6);        $a ==  $half                or die "304";
  $a = sin(120*$pi/120);    $a ==  $zero                or die "305";
  $a = sin(7*$pi/6);        $a == -$half                or die "306";
  $a = sin(3*$pi/2);        $a == -1                    or die "307";
  $a = sin(110*$pi/ 60);    $a == '-1/2'                or die "308";
  $a = sin(2*$pi);          $a ==  $zero                or die "309";
  $a = sin(-$zero);         $a ==  $zero                or die "311";
  $a = sin(-$pi/6);         $a == -$half                or die "312";
  $a = sin(-$pi/2);         $a == -$one                 or die "313";
  $a = sin(-5*$pi/6);       $a == -$half                or die "314";
  $a = sin(-120*$pi/120);   $a == -$zero                or die "315";
  $a = sin(-7*$pi/6);       $a ==  $half                or die "316";
  $a = sin(-3*$pi/2);       $a ==  $one                 or die "317";
  $a = sin(-110*$pi/ 60);   $a ==  $half                or die "318";
  $a = sin(-2*$pi);         $a ==  $zero                or die "319";
  $a = cos($zero);          $a ==  $one                 or die "321";
  $a = cos($pi/3);          $a ==  $half                or die "322";
  $a = cos($pi/2);          $a ==  $zero                or die "323";
  $a = cos(4*$pi/6);        $a == -$half                or die "324";
  $a = cos(120*$pi/120);    $a == -$one                 or die "325";
  $a = cos(8*$pi/6);        $a == -$half                or die "326";
  $a = cos(3*$pi/2);        $a ==  $zero                or die "327";
  $a = cos(100*$pi/ 60);    $a ==  $half                or die "328";
  $a = cos(2*$pi);          $a ==  $one                 or die "329";
  $a = cos(-$zero);         $a ==  $one                 or die "331";
  $a = cos(-$pi/3);         $a == +$half                or die "332";
  $a = cos(-$pi/2);         $a ==  $zero                or die "333";
  $a = cos(-4*$pi/6);       $a == -$half                or die "334";
  $a = cos(-120*$pi/120);   $a == -$one                 or die "335";
  $a = cos(-8*$pi/6);       $a == -$half                or die "336";
  $a = cos(-3*$pi/2);       $a ==  $zero                or die "337";
  $a = cos(-100*$pi/ 60);   $a ==  $half                or die "338";
  $a = cos(-2*$pi);         $a ==  $one                 or die "339";
  $a = exp($zero);          $a ==  $one                 or die "340";
  $a = exp($i*$pi/2);       $a ==  $i                   or die "341";
  $a = exp($i*$pi);         $a == -$one                 or die "342";
  $a = exp(3*$i*$pi/2);     $a == -$i                   or die "343";
  $a = exp(4*$i*$pi/2);     $a ==  $one                 or die "344";
 }

test unless caller;

#_______________________________________________________________________
# Package installed successfully
#_______________________________________________________________________

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
