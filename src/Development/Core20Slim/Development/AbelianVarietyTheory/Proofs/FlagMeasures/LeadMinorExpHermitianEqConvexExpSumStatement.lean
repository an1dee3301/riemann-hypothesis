module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.FlagMeasures.LeadMinorExpHermitianEqConvexExpSum
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Powerset
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
theorem _root_.GlobalTheory.T.leadMinor_exp_hermitian_eq_convex_exp_sum : ∀ (n : ℕ) (Y : Matrix (Fin n) (Fin n) ℂ) (hY : Y.IsHermitian) (l : ℕ) (hl : l ≤ n), ∃ w : Finset (Fin n) → ℝ, (∀ J, 0 ≤ w J) ∧ (∀ J, w J ≠ 0 → J.card = l) ∧ ∑ J, w J = 1 ∧ ∀ t : ℝ, leadMinor (NormedSpace.exp ((t : ℂ) • Y)) l hl = ((∑ J, w J * Real.exp (t * ∑ j ∈ J, hY.eigenvalues j) : ℝ) : ℂ) := by
  first | exact @GlobalTheory.LeadMinorExp.leadMinor_exp_eq_sum | exact GlobalTheory.LeadMinorExp.leadMinor_exp_eq_sum | (intros; apply GlobalTheory.LeadMinorExp.leadMinor_exp_eq_sum <;> assumption)
