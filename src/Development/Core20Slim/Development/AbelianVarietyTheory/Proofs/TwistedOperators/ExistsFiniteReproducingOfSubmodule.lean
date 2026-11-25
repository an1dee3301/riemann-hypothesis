module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsInterpolation
public import Init.Classical
public import Init.Core
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.BigOperators.GroupWithZero.Action
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.Module.BigOperators
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Finset.Lattice.Basic
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Pi
public import Mathlib.LinearAlgebra.Multilinear.Basic
public import Mathlib.Order.Defs.PartialOrder

@[expose] public section

namespace GlobalTheory

open Finset

theorem exists_finite_reproducing_of_submodule {X : Type} (V : Submodule ℂ (X → ℂ))
    (F : Finset ↥V) :
    ∃ (S : Finset X) (u : X → ↥V), ∀ f ∈ F, f = ∑ x ∈ S, (f : X → ℂ) x • u x := by
  first
  | exact @_root_.GlobalTheory.LagrangeInterpolationExistence.exists_interpolation
  | exact _root_.GlobalTheory.LagrangeInterpolationExistence.exists_interpolation
  | (apply _root_.GlobalTheory.LagrangeInterpolationExistence.exists_interpolation <;> assumption)
  | (intros; apply _root_.GlobalTheory.LagrangeInterpolationExistence.exists_interpolation <;> assumption)
  | (intros; apply @_root_.GlobalTheory.LagrangeInterpolationExistence.exists_interpolation <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.LagrangeInterpolationExistence.exists_interpolation ..)

theorem finsupp_sum_multilinear_eq_of_prod_eq {ι : Type} [Fintype ι] [DecidableEq ι]
    {X : ι → Type} (V : ∀ k, Submodule ℂ (X k → ℂ)) {R : Type} [AddCommGroup R] [Module ℂ R]
    (M : (∀ k, ↥(V k)) →ₘₗ[ℂ] R) {A : Type} (τ τ' : A →₀ ℂ)
    (φ φ' : A → ∀ k, ↥(V k))
    (h : ∀ z : ∀ k, X k, (τ.sum fun a c => c * ∏ k, (φ a k : X k → ℂ) (z k)) =
      τ'.sum fun a c => c * ∏ k, (φ' a k : X k → ℂ) (z k)) :
    (τ.sum fun a c => c • M (φ a)) = τ'.sum fun a c => c • M (φ' a) := by
  classical
  let T : Finset A := τ.support ∪ τ'.support
  let F : ∀ k, Finset ↥(V k) := fun k => T.image (fun a => φ a k) ∪ T.image (fun a => φ' a k)
  choose S u hSu using fun k => exists_finite_reproducing_of_submodule (V k) (F k)
  have key : ∀ w : ∀ k, ↥(V k), (∀ k, w k ∈ F k) →
      M w = ∑ z ∈ Fintype.piFinset S, (∏ k, (w k : X k → ℂ) (z k)) • M (fun k => u k (z k)) := by
    intro w hw
    have hw' : w = fun k => ∑ x ∈ S k, (w k : X k → ℂ) x • u k x :=
      funext fun k => hSu k (w k) (hw k)
    conv_lhs => rw [hw']
    rw [MultilinearMap.map_sum_finset]
    refine Finset.sum_congr rfl fun z _ => ?_
    simp only [MultilinearMap.map_smul_univ, RingHom.id_apply]
  have expand : ∀ (σ : A →₀ ℂ) (ψ : A → ∀ k, ↥(V k)), σ.support ⊆ T →
      (∀ a ∈ T, ∀ k, ψ a k ∈ F k) →
      (σ.sum fun a c => c • M (ψ a)) = ∑ z ∈ Fintype.piFinset S,
        (σ.sum fun a c => c * ∏ k, (ψ a k : X k → ℂ) (z k)) • M (fun k => u k (z k)) := by
    intro σ ψ hσ hψ
    unfold Finsupp.sum
    rw [Finset.sum_congr rfl fun a ha => congrArg (σ a • ·) (key (ψ a) (hψ a (hσ ha)))]
    simp only [Finset.smul_sum, smul_smul, Finset.sum_smul]
    exact Finset.sum_comm
  rw [expand τ φ Finset.subset_union_left
      (fun a ha k => Finset.mem_union_left _ (Finset.mem_image_of_mem _ ha)),
    expand τ' φ' Finset.subset_union_right
      (fun a ha k => Finset.mem_union_right _ (Finset.mem_image_of_mem _ ha))]
  exact Finset.sum_congr rfl fun z _ => by rw [h z]

end GlobalTheory
