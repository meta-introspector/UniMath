
if [ -f $1.sexp ]; then
    echo doing   $1.sexp
sercomp   --input=vernac --mode=sexp \
	  -R UniMath/Foundations/,UniMath.Foundations \
	  -R UniMath/Algebra/,UniMath.Algebra \
	  -R UniMath/CategoryTheory/,UniMath.CategoryTheory \
	  -R UniMath/Combinatorics/,UniMath.Combinatorics \
	  -R UniMath/Foundations/,UniMath.Foundations \
	  -R UniMath/MoreFoundations/,UniMath.MoreFoundations \
	  -R UniMath/NumberSystems/,UniMath.NumberSystems \
	  -R UniMath/OrderTheory/,UniMath.OrderTheory \
	  -R UniMath/PAdics/,UniMath.PAdics \
	  -R UniMath/SyntheticHomotopyTheory/,UniMath.SyntheticHomotopyTheory \
	  -R UniMath/Tactics/,UniMath.Tactics \
	  $1  > $1.sexp
else
    echo $1.sexp
fi
