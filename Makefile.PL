use ExtUtils::MakeMaker;

WriteMakefile
 (NAME		=> 'Math::Algebra::Symbols',
  VERSION	=> '1.16',	
  ABSTRACT=> 'Symbolic Algebra using Perl',
  AUTHOR 	=> '\"Philip R Brenan\"<philiprbrenan@yahoo.com>',
  PREREQ_PM => 
   {'Carp',     	 => '0',
    'Scalar::Util' => '0',
    'IO::Handle'	 => '0',
    'Math::BigInt' => '0'
   }
 );
