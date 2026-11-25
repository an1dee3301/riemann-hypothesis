module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.FlagMeasures.AbsSumEigenvaluesNoncompactPartLe
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Formalism.RealPlaceAnalysis.Complexify
public import Init.Data.Cast
public import Init.Data.Nat.Basic
public import Init.Prelude
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Filter
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Hermitian

@[expose] public section

open Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abs_sum_eigenvalues_noncompactPart_le : ∀ (n : ℕ) (ε : Fin n → Bool) (Y : Matrix (Fin n) (Fin n) ℂ) (hY : Y.IsHermitian), inP ε Y → ∀ J : Finset (Fin n), |∑ j ∈ J, hY.eigenvalues j| ≤ Real.sqrt (2 * ((min (univ.filter fun a => ε a = true).card (univ.filter fun a => ε a = false).card : ℕ) : ℝ)) * Real.sqrt (hs Y) := by
  first | exact @GlobalTheory.EigenPartialSum.abs_sum_eigenvalues_le | exact GlobalTheory.EigenPartialSum.abs_sum_eigenvalues_le | (intros; apply GlobalTheory.EigenPartialSum.abs_sum_eigenvalues_le <;> assumption)
