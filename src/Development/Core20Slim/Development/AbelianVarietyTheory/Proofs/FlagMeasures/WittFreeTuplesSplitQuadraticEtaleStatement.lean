module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.FlagMeasures.WittFreeTuplesSplitQuadraticEtale
public import Development.AbelianVarietyTheory.Definitions.Foundations.InFrameStabilizer
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs

@[expose] public section

open GlobalTheory.SgAlg Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.witt_free_tuples_split_quadratic_etale : ∀ {E : Type} [CommRing E] (σ : E →+* E), IsQA σ → (∃ e : E, e * e = e ∧ e + σ e = 1 ∧ ∀ x : E, e * x ≠ 0 → ∃ y, e * x * y = e) → ∀ {n a : ℕ} (J : Matrix (Fin n) (Fin n) E), IsHermU σ J → ∀ (X X' : Matrix (Fin n) (Fin a) E), Free X → Free X' → pairM σ J X X = pairM σ J X' X' → ∃ g, IsUn σ J g ∧ g * X = X' := by
  first | exact @GlobalTheory.SgAlg.WittSplit.witt_split | exact GlobalTheory.SgAlg.WittSplit.witt_split | (intros; apply GlobalTheory.SgAlg.WittSplit.witt_split <;> assumption)
