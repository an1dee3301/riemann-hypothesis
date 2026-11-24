module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.DenseRangeFiniteVectorsDiscreteSeries
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.SameBlockOfPosC
public import Formalism.LocalRingCardinality.DataTheta
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Nontrivial.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dense_range_finite_vectors_discrete_series : ∀ (p q : ℕ), 1 ≤ p + q → ∀ (T : GrpData p q) (D : DSRep T), Nontrivial D.HK.V → (∀ Y ∈ upq p q, ∀ y, ∃ C ρ : ℝ, 0 ≤ C ∧ 0 < ρ ∧ ∀ k : ℕ, ‖D.ι ((D.HK.act Y ^ k) y)‖ ≤ C * ρ ^ k * (k.factorial : ℝ)) → Dense (Set.range D.ι) := by
  first | exact @GlobalTheory.AnalyticDense.dense_range_of_factorial_bound | exact GlobalTheory.AnalyticDense.dense_range_of_factorial_bound | (intros; apply GlobalTheory.AnalyticDense.dense_range_of_factorial_bound <;> assumption)
