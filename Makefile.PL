use ExtUtils::MakeMaker;

WriteMakefile
 (NAME		=> 'Math::Algebra::Symbols',
  VERSION	=> '1.12',	
  ABSTRACT=> 'Symbolic Algebra using Perl',
  AUTHOR 	=> '\"Philip R Brenan\"<philiprbrenan@yahoo.com>',
  PREREQ_PM => 
   {'Hash::Util'	 => '0',
    'IO::Handle'	 => '0',
    'Math::BigInt' => '0'
   }
 );
