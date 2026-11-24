module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.FiniteIntertwining
public import Formalism.BranchSandwichDivisors.DivFromPassageAndNorm
public import Formalism.LocalToGlobal.Columns.PolyFn
public import Init.Classical
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.DirectSum.Basic
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.IsEmpty.Defs
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Defs
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.RepresentationTheory.Intertwining
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal

@[expose] public section

open MvPolynomial Formalism.BasicNotions Formalism.GradedWeylDivisibility GlobalTheory.Branching
open Formalism.MainNotions.PrimeDegreeVariant (embGL Interlace)
open scoped DirectSum

namespace GlobalTheory.IntertwinerSum

open Representation

variable {k G ι U W : Type} [Field k] [Group G] [Fintype ι] {V : ι → Type}
  [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)] [AddCommGroup U] [Module k U]
  [AddCommGroup W] [Module k W]

theorem finite_intertwiningMap [FiniteDimensional k U] [FiniteDimensional k W]
    (τ : Representation k G U) (σ : Representation k G W) :
    FiniteDimensional k (τ.IntertwiningMap σ) :=
  FiniteDimensional.of_injective
    ({ toFun := fun f => f.toLinearMap
       map_add' := fun _ _ => rfl
       map_smul' := fun _ _ => rfl } : τ.IntertwiningMap σ →ₗ[k] (U →ₗ[k] W))
    (IntertwiningMap.toLinearMap_injective τ σ)

theorem equivs_of_biproduct (ρ : ∀ i, Representation k G (V i)) (τ : Representation k G U)
    (σ : Representation k G W) (p : ∀ i, σ.IntertwiningMap (ρ i))
    (j : ∀ i, (ρ i).IntertwiningMap σ) (hsum : ∀ w, ∑ i, j i (p i w) = w)
    (hdiag : ∀ i x, p i (j i x) = x) (hoff : ∀ i i', i' ≠ i → ∀ x, p i (j i' x) = 0) :
    Nonempty (τ.IntertwiningMap σ ≃ₗ[k] ∀ i, τ.IntertwiningMap (ρ i)) ∧
      Nonempty (σ.IntertwiningMap τ ≃ₗ[k] ∀ i, (ρ i).IntertwiningMap τ) := by
  classical
  refine ⟨⟨{ toFun := fun f i => (p i).comp f
             map_add' := fun f g => ?_
             map_smul' := fun c f => ?_
             invFun := fun f => ∑ i, (j i).comp (f i)
             left_inv := fun f => ?_
             right_inv := fun f => ?_ }⟩,
          ⟨{ toFun := fun f i => f.comp (j i)
             map_add' := fun f g => rfl
             map_smul' := fun c f => rfl
             invFun := fun f => ∑ i, (f i).comp (p i)
             left_inv := fun f => ?_
             right_inv := fun f => ?_ }⟩⟩
  · funext i
    exact DFunLike.ext _ _ fun u => map_add (p i) (f u) (g u)
  · funext i
    exact DFunLike.ext _ _ fun u => map_smul (p i) c (f u)
  · refine DFunLike.ext _ _ fun u => ?_
    rw [IntertwiningMap.sum_apply]
    exact hsum (f u)
  · funext i
    refine DFunLike.ext _ _ fun u => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [IntertwiningMap.comp_apply, IntertwiningMap.sum_apply, map_sum]
    simp only [IntertwiningMap.comp_apply]
    rw [Finset.sum_eq_single i (fun i' _ h => hoff i i' h _) (by simp)]
    exact hdiag i _
  · refine DFunLike.ext _ _ fun w => ?_
    rw [IntertwiningMap.sum_apply]
    simp only [IntertwiningMap.comp_apply]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← map_sum, hsum]
  · funext i
    refine DFunLike.ext _ _ fun x => ?_
    rw [IntertwiningMap.comp_apply, IntertwiningMap.sum_apply]
    simp only [IntertwiningMap.comp_apply]
    rw [Finset.sum_eq_single i (fun i' _ h => by rw [hoff i' i h.symm, map_zero]) (by simp), hdiag]

theorem finrank_intertwiningMap_directSum :
    ∀ (k G ι U W : Type) [Field k] [Group G] [Fintype ι] (V : ι → Type) [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)] [∀ i, FiniteDimensional k (V i)] [AddCommGroup U] [Module k U] [FiniteDimensional k U] [AddCommGroup W] [Module k W] (ρ : ∀ i, Representation k G (V i)) (τ : Representation k G U) (σ : Representation k G W), Nonempty ((Representation.directSum ρ).Equiv σ) → Module.finrank k (τ.IntertwiningMap σ) = ∑ i, Module.finrank k (τ.IntertwiningMap (ρ i)) ∧ Module.finrank k (σ.IntertwiningMap τ) = ∑ i, Module.finrank k ((ρ i).IntertwiningMap τ) := by
  intro k G ι U W _ _ _ V _ _ _ _ _ _ _ _ ρ τ σ ⟨e⟩
  classical
  let p₀ : ∀ i, (Representation.directSum ρ).IntertwiningMap (ρ i) := fun i =>
    { toLinearMap := DirectSum.component k ι V i
      isIntertwining' := fun g => by
        refine LinearMap.ext fun x => ?_
        rfl }
  let j₀ : ∀ i, (ρ i).IntertwiningMap (Representation.directSum ρ) := fun i =>
    { toLinearMap := DirectSum.lof k ι V i
      isIntertwining' := fun g => by
        refine LinearMap.ext fun x => ?_
        simp [Representation.directSum] }
  have hse : ∀ x, e.symm.toIntertwiningMap (e.toIntertwiningMap x) = x :=
    fun x => e.toLinearEquiv.symm_apply_apply x
  have hes : ∀ x, e.toIntertwiningMap (e.symm.toIntertwiningMap x) = x :=
    fun x => e.toLinearEquiv.apply_symm_apply x
  obtain ⟨⟨a⟩, ⟨b⟩⟩ := equivs_of_biproduct ρ τ σ
    (fun i => (p₀ i).comp e.symm.toIntertwiningMap) (fun i => e.toIntertwiningMap.comp (j₀ i))
    (fun w => by
      simp only [IntertwiningMap.comp_apply]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← map_sum]
      have : ∀ x : ⨁ i, V i, ∑ i, j₀ i (p₀ i x) = x := fun x => DirectSum.sum_univ_of x
      rw [this, hes])
    (fun i x => by
      simp only [IntertwiningMap.comp_apply]
      rw [hse]
      exact DirectSum.component.lof_self k i x)
    (fun i i' h x => by
      simp only [IntertwiningMap.comp_apply]
      rw [hse]
      exact DirectSum.of_eq_of_ne i' i x h.symm)
  have := fun i => finite_intertwiningMap τ (ρ i)
  have := fun i => finite_intertwiningMap (ρ i) τ
  exact ⟨a.finrank_eq.trans (Module.finrank_pi_fintype k), b.finrank_eq.trans (Module.finrank_pi_fintype k)⟩

end GlobalTheory.IntertwinerSum
