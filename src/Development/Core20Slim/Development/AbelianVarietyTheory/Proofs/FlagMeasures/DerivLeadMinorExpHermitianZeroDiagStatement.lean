module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.FlagMeasures.DerivLeadMinorExpHermitianZeroDiag
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.deriv_leadMinor_exp_hermitian_zeroDiag : ∀ (n : ℕ) (Y : Matrix (Fin n) (Fin n) ℂ), Y.IsHermitian → (∀ a, Y a a = 0) → ∀ (l : ℕ) (hl : l ≤ n), deriv (fun t : ℝ => (leadMinor (NormedSpace.exp ((t : ℂ) • Y)) l hl).re) 0 = 0 ∧ deriv (deriv (fun t : ℝ => (leadMinor (NormedSpace.exp ((t : ℂ) • Y)) l hl).re)) 0 = ∑ a : Fin n, ∑ b : Fin n, if l ≤ a.val ∧ b.val < l then ‖Y a b‖ ^ 2 else 0 := by
  first | exact @GlobalTheory.MinorJet.deriv_leadMinor_exp | exact GlobalTheory.MinorJet.deriv_leadMinor_exp | (intros; apply GlobalTheory.MinorJet.deriv_leadMinor_exp <;> assumption)
