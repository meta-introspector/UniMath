open PartA
open Preamble

type __ = Obj.t

val isweqtoforallpathsAxiom :
  (__ -> __) -> (__ -> __) -> ((__ -> __) paths, (__, __) homot) isweq

val funcontrAxiom : (__ -> __ iscontr) -> (__ -> __) iscontr

val funcontr : (__ -> __ iscontr) -> (__ -> __) iscontr

val isweqtoforallpaths :
  (__ -> __) -> (__ -> __) -> ((__ -> __) paths, (__, __) homot) isweq
