import SingularMatrices.TwoByTwo
import SingularMatrices.ErrorSums
import SingularMatrices.ThreeByThree

/-!
# Which axioms do the main results use?

Each line below should print only `propext`, `Classical.choice` and `Quot.sound`, the
standard axioms of Lean and Mathlib. A `sorryAx` would mean an unfinished proof.
-/

#print axioms SingularMatrices.S2_formula
#print axioms SingularMatrices.main_bound
#print axioms SingularMatrices.S3_split
#print axioms SingularMatrices.A3count_eq_sum_g
