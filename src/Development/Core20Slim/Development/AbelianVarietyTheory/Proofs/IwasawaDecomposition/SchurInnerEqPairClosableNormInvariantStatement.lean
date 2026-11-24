module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SchurInnerEqPairClosableNormInvariant
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfInnerSmooth
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HilbertSchurOfAdjointClosed
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GelfandInvariantCommRightTranslation
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Mathlib.Analysis.CStarAlgebra.Module.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Nat.Basic
public import Mathlib.Order.Filter.AtTopBot.Defs
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.Notation
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Cauchy
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR.Mult GlobalTheory.SmVec MeasureTheory Matrix Filter
open scoped TensorProduct ContDiff InnerProductSpace Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schur_inner_eq_pair_closable_normInvariant : ∀ (ι H E : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] (ρ : ι → (H →L[ℂ] H)) (D : Submodule ℂ H), (∀ i v, ‖ρ i v‖ = ‖v‖) → (∀ i, ∃ j, (∀ v, ρ j (ρ i v) = v) ∧ ∀ v, ρ i (ρ j v) = v) → (∀ S : Submodule ℂ H, IsClosed (S : Set H) → (∀ i, ∀ v ∈ S, ρ i v ∈ S) → S = ⊥ ∨ S = ⊤) → (∀ i, ∀ v ∈ D, ρ i v ∈ D) → ∀ A A' : H →ₗ[ℂ] E, (∀ i, ∀ w ∈ D, ‖A (ρ i w)‖ = ‖A w‖) → (∀ i, ∀ w ∈ D, ‖A' (ρ i w)‖ = ‖A' w‖) → (∀ i, ∀ w ∈ D, ⟪A (ρ i w), A' (ρ i w)⟫_ℂ = ⟪A w, A' w⟫_ℂ) → (∀ (u : ℕ → H) (f : E), (∀ i, u i ∈ D) → Tendsto u atTop (𝓝 0) → Tendsto (fun i => A (u i)) atTop (𝓝 f) → f = 0) → (∀ (u : ℕ → H) (f : E), (∀ i, u i ∈ D) → Tendsto u atTop (𝓝 0) → Tendsto (fun i => A' (u i)) atTop (𝓝 f) → f = 0) → ∃ c : ℂ, ∀ w ∈ D, ∀ w' ∈ D, ⟪A w, A' w'⟫_ℂ = c * ⟪w, w'⟫_ℂ := by
  first | exact @GlobalTheory.ClosableSchur.inner_eq_pair | exact GlobalTheory.ClosableSchur.inner_eq_pair | (intros; apply GlobalTheory.ClosableSchur.inner_eq_pair <;> assumption)
