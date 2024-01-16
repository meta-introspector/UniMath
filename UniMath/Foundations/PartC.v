(**  Univalent Foundations. Vladimir Voevodsky. Feb. 2010 - Sep. 2011. Port to coq
     trunk (8.4-8.5) in March 2014. The third part of the original uu0 file,
     created on Dec. 3, 2014.

   Only one universe is used, and it is never used as a type.

   The only axiom we use is [ funextemptyAxiom ], which is the functional
   extensionality axiom for functions with values in the empty type.  Any
   results that don't depend on axioms should be in an earlier file.

*)


Require Export UniMath.Foundations.PartB.
Require Export UniMath.Foundations.UnivalenceAxiom.
