module

public import Mathlib
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalUniqueSquareRootNearOne
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Order.Filter.Defs
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open MeasureTheory
open scoped ENNReal NNReal Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_unique_square_root_near_one : ∀ (B V : Type) [Ring B] [TopologicalSpace B] [IsTopologicalRing B] [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (ψ : B ≃+ V), Continuous ψ → Continuous ψ.symm → ∃ (r : B → B) (U : Set B), U ∈ nhds (1 : B) ∧ Filter.Tendsto r (nhds 1) (nhds 1) ∧ (∀ᶠ h in nhds (1 : B), r h * r h = h) ∧ ∀ x ∈ U, ∀ y ∈ U, x * x = y * y → x = y := by
  first | exact @GlobalTheory.CompanionTheory.RingSqrt.exists_local_sqrt | exact GlobalTheory.CompanionTheory.RingSqrt.exists_local_sqrt | (intros; apply GlobalTheory.CompanionTheory.RingSqrt.exists_local_sqrt <;> assumption)
