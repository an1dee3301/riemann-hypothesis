module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsEqAdicCompletionIntegers
public import Init.Core
public import Init.Data.Nat.Basic
public import Init.Prelude
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Valuation.ValuationSubring

@[expose] public section

open IsDedekindDomain NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_binary_quadratic_eq_unit_of_disc_isUnit : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (t n u : v.adicCompletionIntegers F), IsUnit (t ^ 2 - 4 * n) → IsUnit u → ∃ r s : v.adicCompletionIntegers F, r ^ 2 + t * r * s + n * s ^ 2 = u := by
  first | exact @GlobalTheory.BinaryUnitForm.exists_eq_adicCompletionIntegers | exact GlobalTheory.BinaryUnitForm.exists_eq_adicCompletionIntegers | (intros; apply GlobalTheory.BinaryUnitForm.exists_eq_adicCompletionIntegers <;> assumption)
