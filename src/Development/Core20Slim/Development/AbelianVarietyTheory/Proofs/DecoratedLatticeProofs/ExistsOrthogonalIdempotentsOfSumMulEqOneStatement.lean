module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsOrthogonalIdempotentsOfSumMulEqOne
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_orthogonal_idempotents_of_sum_mul_eq_one' : ∀ (F : Type) [Field F] [NumberField F] (ι : Type) [Fintype ι] (f s : ι → NumberField.AdeleRing (NumberField.RingOfIntegers F) F), ∑ i, s i * f i = 1 → ∃ e t : ι → NumberField.AdeleRing (NumberField.RingOfIntegers F) F, ∑ i, e i = 1 ∧ (∀ i j, i ≠ j → e i * e j = 0) ∧ ∀ i, t i * f i = e i := by
  first | exact @GlobalTheory.AdeleIdempotents.exists_orthogonal_idempotents_of_sum_mul_eq_one | exact GlobalTheory.AdeleIdempotents.exists_orthogonal_idempotents_of_sum_mul_eq_one | (intros; apply GlobalTheory.AdeleIdempotents.exists_orthogonal_idempotents_of_sum_mul_eq_one <;> assumption)
