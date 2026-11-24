module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.FlagMeasures.HsLeWeightedSumBlockVariancesOfGap
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Formalism.FormalDegreeBessel.StatementDS
public import Formalism.RealPlaceAnalysis.Complexify
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Int.Lemmas
public import Init.Data.Int.Order
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Omega.Coeffs
public import Init.Omega.Constraint
public import Init.Omega.Int
public import Init.Omega.LinearCombo
public import Init.Prelude
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Fin.Basic
public import Mathlib.Order.Monotone.Defs

@[expose] public section

open Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hs_le_weighted_sum_blockVariances_of_gap : ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (h : ℝ) (Y : Matrix (Fin n) (Fin n) ℂ), StrictAnti lam → GapAtLeast ε lam h → inP ε Y → h * hs Y / 2 ≤ ∑ i : Fin (n - 1), (lam ⟨i.val, by omega⟩ - lam ⟨i.val + 1, by omega⟩ + 1) * ∑ a : Fin n, ∑ b : Fin n, if i.val + 1 ≤ a.val ∧ b.val < i.val + 1 then ‖Y a b‖ ^ 2 else 0 := by
  first | exact @GlobalTheory.GapSum.gap_mul_hs_le | exact GlobalTheory.GapSum.gap_mul_hs_le | (intros; apply GlobalTheory.GapSum.gap_mul_hs_le <;> assumption)
