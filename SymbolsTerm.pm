#!perl -w
#_ Term _________________________________________________________________
# Symbolic algebra: terms.
# Perl License.
# PhilipRBrenan@yahoo.com, 2004.
#________________________________________________________________________

#_ Term _________________________________________________________________
# Terms are built in place and then finalized when complete.
#________________________________________________________________________

package Math::Algebra::SymbolsTerm;
$VERSION = 1.16;

use Carp;
use Math::BigInt;  
#HashUtil use Hash::Util qw(lock_hash); 
use Scalar::Util qw(weaken);

#_ Term _________________________________________________________________
# Greatest Common Divisor.
#________________________________________________________________________

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

#_ Term _________________________________________________________________
# Least common multiple.  
#________________________________________________________________________

sub lcm($$)
 {my $x = abs($_[0]);
  my $y = abs($_[1]);
  return $x*$y if $x == 1 or $y == 1; 
  $x*$y / gcd($x, $y);
 }

#_ Term _________________________________________________________________
# Constructer
#________________________________________________________________________

sub new
 {bless {c=>1, d=>1, i=>0, v=>{}, sqrt=>undef, divide=>undef, exp=>undef, log=>undef};
 }

#_ Term _________________________________________________________________
# New from String
#________________________________________________________________________

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

#_ Term _________________________________________________________________
# Short name for new from String
#________________________________________________________________________

sub n($)
 {newFromString($_[0]);
 }

#_ Term _________________________________________________________________
# New from Strings
#________________________________________________________________________

sub newFromStrings(@)
 {return $zero->clone() unless scalar(@_);
  map {newFromString($_)} @_;
 }

#_ Term _________________________________________________________________
# Confirm type
#________________________________________________________________________

sub isTerm($) {1}; 

#_ Term _________________________________________________________________
# Integer check
#________________________________________________________________________

sub intCheck($$) 
 {my ($i, $m) = @_;
  return $i if $i == 1;
  $i =~ /^[\+\-]?\d+/ or die "Integer required for $m not $i";
  return Math::BigInt->new($i) if $i > 10_000_000;
  $i;
 }

#_ Term _________________________________________________________________
# Coefficient
#________________________________________________________________________

sub c($;$) 
 {my ($t) = @_;
  return $t->{c} unless @_ > 1;

  $t->{c} = ($_[1] == 1 ? $_[1] : intCheck($_[1], 'c'));
  $t;
 }

#_ Term _________________________________________________________________
# Divisor
#________________________________________________________________________

sub d($;$) 
 {my ($t) = @_;
  return $t->{d} unless @_ > 1;

  $t->{d} = ($_[1] == 1 ? $_[1] : intCheck($_[1], 'd'));
  $t;
 }

#_ Term _________________________________________________________________
# Multiply term by integer
#________________________________________________________________________

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

#_ Term _________________________________________________________________
# Divide term by integer
#________________________________________________________________________

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

#_ Term _________________________________________________________________
# Negate term
#________________________________________________________________________

sub negate($) 
 {my ($t) = @_;
  $t->{c} = -$t->{c};
  $t;
 }

#_ Term _________________________________________________________________
# Is Zero
#________________________________________________________________________

sub isZero($) 
 {my ($t) = @_;
  exists $t->{z} or die "Testing unfinalized term";
  $t->{id} == $zero->{id};
 }

sub notZero($) {return !isZero($_[0])} 

#_ Term _________________________________________________________________
# Is One
#________________________________________________________________________

sub isOne($) 
 {my ($t) = @_;
  exists $t->{z} or die "Testing unfinalized term";
  $t->{id} == $one->{id};
 }

sub notOne($) {return !isOne($_[0])} 

#_ Term _________________________________________________________________
# Is Minus One
#________________________________________________________________________

sub isMinusOne($) 
 {my ($t) = @_;
  exists $t->{z} or die "Testing unfinalized term";
  $t->{id} == $mOne->{id};
 }

sub notMinusOne($) {return !isMinusOne($_[0])} 

#_ Term _________________________________________________________________
# Get/Set i - sqrt(-1)
#________________________________________________________________________

sub i($;$) 
 {my ($t) = @_;

  return $t->{i} unless(@_) > 1;

  my $i = ($_[1] == 1 ? $_[1] : intCheck($_[1], 'i'));

  my $i4  = $i % 4;
  $t->{i} = $i % 2;
  $t->{c} = -$t->{c} if $i4 == 2 or $i4 == 3;
  $t;
 }

#_ Term _________________________________________________________________
# i by power: multiply a term by a power of i
#________________________________________________________________________

sub iby($$) 
 {my ($t, $p) = @_;

  $t->i($p+$t->{i});
  $t;
 }

#_ Term _________________________________________________________________
# Get/Set divide by
#________________________________________________________________________

sub Divide($;$) 
 {my ($t, $d) = @_;
  return $t->{divide} unless @_ > 1;
  $t->{divide} = $d;
  $t;
 }

#_ Term _________________________________________________________________
# Remove divide
#________________________________________________________________________

sub removeDivide($) 
 {my ($t) = @_;
  my $z = $t->clone;
  delete $z->{divide};
  $z->z;
 }

#_ Term _________________________________________________________________
# Get/Set sqrt
#________________________________________________________________________

sub Sqrt($;$) 
 {my ($t, $s) = @_;
  return $t->{sqrt} unless @_ > 1;
  $t->{sqrt} = $s;
  $t;
 }

#_ Term _________________________________________________________________
# Remove divide
#________________________________________________________________________

sub removeSqrt($) 
 {my ($t) = @_;
  my $z = $t->clone;
  delete $z->{sqrt};
  $z->z;
 }

#_ Term _________________________________________________________________
# Get/Set exp
#________________________________________________________________________

sub Exp($;$) 
 {my ($t, $e) = @_;
  return $t->{exp} unless @_ > 1;
  $t->{exp} = $e;
  $t;
 }

#_ Term _________________________________________________________________
# Get/Set log
#________________________________________________________________________

sub Log($$) 
 {my ($t, $l) = @_;
  return $t->{log} unless @_ > 1;
  $t->{log} = $l;
  $t;
 }

#_ Term _________________________________________________________________
# Get/Set variable power. 
#________________________________________________________________________

sub vp($$;$) 
 {my ($t, $v) = @_;
# $v =~ /^[a-z]+$/i or die "Bad variable name $v";

  return exists($t->{v}{$v}) ? $t->{v}{$v} : 0 if @_ == 2; 

  my $p = ($_[2] == 1 ? $_[2] : intCheck($_[2], 'vp'));
  $t->{v}{$v} = $p   if $p;
  delete $t->{v}{$v} unless $p;
  $t;
 }

#_ Term _________________________________________________________________
# Get all variables
#________________________________________________________________________

sub v($) 
 {my ($t) = @_;
  return keys %{$t->{v}};
 }

#_ Term _________________________________________________________________
# Clone
#________________________________________________________________________

sub clone($) 
 {my ($t) = @_;
  $t->{z} or die "Attempt to clone unfinalized  term";
  my $c   = bless {%$t};
  $c->{v} = {%{$t->{v}}};
  delete @$c{qw(id s z)};
# delete $c->{z};
# delete $c->{s};
# delete $c->{id};
  $c;
 }

#_ Term _________________________________________________________________
# Split
#________________________________________________________________________

sub split($) 
 {my ($t) = @_;
  my $c = $t->clone;
  my @c = @$c{qw(sqrt divide exp log)};
          @$c{qw(sqrt divide exp log)} = ((undef()) x 4);
 (t=>$c, s=>$c[0], d=>$c[1], e=>$c[2], l=>$c[3]);
 }

#_ Term _________________________________________________________________
# Sign the term. Used to optimize add().  Fix the problem of adding different logs
#________________________________________________________________________

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

#_ Term _________________________________________________________________
# Get the signature of a term
#________________________________________________________________________

sub getSignature($) 
 {my ($t) = @_;
  exists $t->{z} ? $t->{z} : die "Attempt to get signature of unfinalized term";
 }

#_ Term _________________________________________________________________
# Add two finalized terms, return result in new term or undef.
#________________________________________________________________________

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

#_ Term _________________________________________________________________
# Subtract two finalized terms, return result in new term or undef.
#________________________________________________________________________

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

#_ Term _________________________________________________________________
# Multiply two finalized terms, return the result in a new term or undef
#________________________________________________________________________

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

#_ Term _________________________________________________________________
# Divide two finalized terms, return the result in a new term or undef
#________________________________________________________________________

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

#_ Term _________________________________________________________________
# Invert a term
#________________________________________________________________________

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

#_ Term _________________________________________________________________
# Take power of term
#________________________________________________________________________

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

#_ Term _________________________________________________________________
# Sqrt a term
#________________________________________________________________________

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

#_ Term _________________________________________________________________
# Exponential of a term
#________________________________________________________________________

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

#_ Term _________________________________________________________________
# Sine of a term           
#________________________________________________________________________

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

#_ Term _________________________________________________________________
# Cosine of a term           
#________________________________________________________________________

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

#_ Term _________________________________________________________________
# Log of a term
#________________________________________________________________________

sub log2($) 
 {my ($a) = @_;

  $a->{z} or die "Attempt to use unfinalized term in log";

  return $zero if $a == $one;
  return undef;
 }

#_ Term _________________________________________________________________
# Get Id of a term
#________________________________________________________________________

sub id($) 
 {my ($t) = @_;
  $t->{id} or die "Term $t not yet finalized";
  $t->{id};
 }

#_ Term _________________________________________________________________
# Check term finalized
#________________________________________________________________________

sub zz($) 
 {my ($t) = @_;
  $t->{z} or die "Term $t not yet finalized";
  $t;
 }

#_ Term _________________________________________________________________
# Finalize creation of the term
#________________________________________________________________________

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

#_ Term _________________________________________________________________
# Print
#________________________________________________________________________

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

#_ Term _________________________________________________________________
# Useful constants
#________________________________________________________________________

$zero  = new()->c(0)->z;           sub zero () {$zero} 
$one   = new()->z;                 sub one  () {$one}
$two   = new()->c(2)->z;           sub two  () {$two}
$mOne  = new()->c(-1)->z;          sub mOne () {$mOne}
$i     = new()->i(1)->z;           sub pI   () {$pI}
$mI    = new()->c(-1)->i(1)->z;    sub mI   () {$mI}
$half  = new()->c( 1)->d(2)->z;    sub half () {$half}
$mHalf = new()->c(-1)->d(2)->z;    sub mHalf() {$mHalf}
$pi    = new()->vp('pi', 1)->z;    sub pi   () {$pi}

#_ Term _________________________________________________________________
# Import - parameters from caller - set up as requested.
#________________________________________________________________________

sub import
 {my %P = (program=>@_);
  my %p; $p{lc()} = $P{$_} for(keys(%P));

#_ Term _________________________________________________________________
# New symbols term constructor - export to calling package.
#________________________________________________________________________

  my $s = <<'END';
package XXXX;

BEGIN  {delete $XXXX::{NNNN}}

sub NNNN
 {return SSSS::newFromStrings(@_);
 }
END

#_ Term _________________________________________________________________
# Export to calling package.
#________________________________________________________________________

  my $name   = 'term';
     $name   = $p{term} if exists($p{term});
  my ($main) = caller();
  my $pack   = __PACKAGE__;   

  $s=~ s/XXXX/$main/g;
  $s=~ s/NNNN/$name/g;
  $s=~ s/SSSS/$pack/g;
  eval($s);

#_ Term _________________________________________________________________
# Check options supplied by user
#________________________________________________________________________

  delete @p{qw(program terms)};

  croak "Unknown option(s) for ". __PACKAGE__ .": ". join(' ', keys(%p))."\n\n". <<'END' if keys(%p);

Valid options are:

  terms=>'name' Desired name of the constructor routine for creating
                new terms.  The default is 'term'.
END
 }

#_ Term _________________________________________________________________
# Overload.
#________________________________________________________________________

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

#_ Term _________________________________________________________________
# Add operator.
#________________________________________________________________________

sub add3
 {my ($a, $b) = @_;
  $b = newFromString("$b") unless ref($b) eq __PACKAGE__;
  $a->{z} and $b->{z} or die "Add using unfinalized terms";
  $a->add($b);
 }

#_ Term _________________________________________________________________
# Negate operator.
#________________________________________________________________________

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

#_ Term _________________________________________________________________
# Multiply operator.
#________________________________________________________________________

sub multiply3
 {my ($a, $b) = @_;
  $b = newFromString("$b") unless ref($b) eq __PACKAGE__;
  $a->{z} and $b->{z} or die "Multiply using unfinalized terms";
  $a->multiply($b);
 }

#_ Term _________________________________________________________________
# Divide operator.
#________________________________________________________________________

sub divide3
 {my ($a, $b, $c) = @_;
  $b = newFromString("$b") unless ref($b) eq __PACKAGE__;
  $a->{z} and $b->{z} or die "Divide using unfinalized terms";
  return $b->divide2($a) if     $c;
  return $a->divide2($b) unless $c;
 }

#_ Term _________________________________________________________________
# Power operator.
#________________________________________________________________________

sub power3
 {my ($a, $b) = @_;
  $b = newFromString("$b") unless ref($b) eq __PACKAGE__;
  $a->{z} and $b->{z} or die "Power using unfinalized terms";
  $a->power($b);
 }

#_ Term _________________________________________________________________
# Equals operator.
#________________________________________________________________________

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

#_ Term _________________________________________________________________
# Print operator.
#________________________________________________________________________

sub print3
 {my ($a) = @_;
  $a->{z} or die "Print of unfinalized term";
  $a->print();
 }

#_ Term _________________________________________________________________
# Sqrt operator.
#________________________________________________________________________

sub sqrt3
 {my ($a) = @_;
  $a->{z} or die "Sqrt of unfinalized term";
  $a->sqrt2();
 }

#_ Term _________________________________________________________________
# Exp operator.
#________________________________________________________________________

sub exp3
 {my ($a) = @_;
  $a->{z} or die "Exp of unfinalized term";
  $a->exp2();
 }

#_ Term _________________________________________________________________
# Sine operator.
#________________________________________________________________________

sub sin3
 {my ($a) = @_;
  $a->{z} or die "Sin of unfinalized term";
  $a->sin2();
 }

#_ Term _________________________________________________________________
# Cosine operator.
#________________________________________________________________________

sub cos3
 {my ($a) = @_;
  $a->{z} or die "Cos of unfinalized term";
  $a->cos2();
 }

#_ Term _________________________________________________________________
# Log operator.
#________________________________________________________________________

sub log3
 {my ($a) = @_;
  $a->{z} or die "Log of unfinalized term";
  $a->log2();
 }

#_ Term _________________________________________________________________
# Tests
#________________________________________________________________________

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

#_ Term _________________________________________________________________
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

  2/3*x**2*y**-3*exp(i*pi)*sqrt(z**3) / x

but not:

  x + y

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



