use ExtUtils::MakeMaker;

WriteMakefile
 (NAME		=> 'Math::Algebra::Symbols',
  VERSION	=> '1.21',	
  ABSTRACT=> 'Symbolic Algebra in Pure Perl',
  AUTHOR 	=> 'philiprbrenan@yahoo.com',
  PREREQ_PM => 
   {'Carp',     	 => '0',
    'Scalar::Util' => '0',
    'IO::Handle'	 => '0',
    'Math::BigInt' => '0'
   }
 );
