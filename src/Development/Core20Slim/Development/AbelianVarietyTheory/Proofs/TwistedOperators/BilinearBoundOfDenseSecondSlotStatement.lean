module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.BilinearBoundOfDenseSecondSlot
public import Init.Core
public import Init.Data.Function
public import Init.Prelude
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Analysis.Normed.Module.Seminorm.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Topology.Algebra.IsUniformGroup.Defs
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.UniformSpace.Cauchy
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_seminorm_bound_of_dense_second_slot : ∀ {E : Type} [AddCommGroup E] [Module ℂ E] [UniformSpace E] [IsUniformAddGroup E] [CompleteSpace E] [T2Space E]
    {p : ℕ → Seminorm ℂ E}, WithSeminorms p →
    ∀ {X₁ X₂ : Type} [AddCommGroup X₁] [Module ℂ X₁] [AddCommGroup X₂] [Module ℂ X₂]
    (j₁ : X₁ →ₗ[ℂ] E) (j₂ : X₂ →ₗ[ℂ] E), Function.Injective j₁ → IsClosed (Set.range j₁) →
    ∀ (D₂ : Submodule ℂ X₂), (∀ x, j₂ x ∈ closure (j₂ '' (D₂ : Set X₂))) →
    ∀ (F : X₁ →ₗ[ℂ] X₂ →ₗ[ℂ] E),
    (∀ w i, ∃ q : Seminorm ℂ E, Continuous q ∧ ∀ b, p i (F w b) ≤ q (j₂ b)) →
    (∀ a ∈ D₂, ∀ i, ∃ q : Seminorm ℂ E, Continuous q ∧ ∀ w, p i (F w a) ≤ q (j₁ w)) →
    ∀ b i, ∃ q : Seminorm ℂ E, Continuous q ∧ ∀ w, p i (F w b) ≤ q (j₁ w) := by
  first | exact @GlobalTheory.bilinear_bound_of_dense_right | exact GlobalTheory.bilinear_bound_of_dense_right | (intros; apply GlobalTheory.bilinear_bound_of_dense_right <;> assumption)
