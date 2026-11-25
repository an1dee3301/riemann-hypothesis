module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsFieldOrExistsSwappedIdempotentOfQuadraticEtale
public import Development.AbelianVarietyTheory.Definitions.Foundations.InFrameStabilizer
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Field.IsField
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs

@[expose] public section

open GlobalTheory.SgAlg Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isField_or_exists_swapped_idempotent_of_quadraticEtale : ∀ {E : Type} [CommRing E] (σ : E →+* E), IsQA σ → IsField E ∨ ∃ e : E, e * e = e ∧ e + σ e = 1 ∧ ∀ x : E, e * x ≠ 0 → ∃ y, e * x * y = e := by
  first | exact @GlobalTheory.SgAlg.isField_or_exists_idempotent_of_isQA | exact GlobalTheory.SgAlg.isField_or_exists_idempotent_of_isQA | (intros; apply GlobalTheory.SgAlg.isField_or_exists_idempotent_of_isQA <;> assumption)
