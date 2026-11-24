module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NonemptyInvFunEquiv
public import Init.Classical
public import Init.Core
public import Init.Data.Function
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Projective
public import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Module.Submodule.Range
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Empty
public import Mathlib.Data.Finset.Insert
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.Multilinear.Basic
public import Mathlib.LinearAlgebra.PiTensorProduct.Basic
public import Mathlib.Logic.Function.Basic
public import Mathlib.Order.Notation

@[expose] public section

open MvPolynomial GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries GlobalTheory.OneFunctional Formalism.BasicNotions GlobalTheory.Branching
open scoped TensorProduct DirectSum

namespace GlobalTheory.TensorKernel

theorem piTensor_map_surjective_and_ker :
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (A B : ι → Type) [∀ τ, AddCommGroup (A τ)] [∀ τ, Module ℂ (A τ)] [∀ τ, AddCommGroup (B τ)] [∀ τ, Module ℂ (B τ)] (π : ∀ τ, A τ →ₗ[ℂ] B τ), (∀ τ, Function.Surjective (π τ)) → Function.Surjective (PiTensorProduct.map π) ∧ ∀ l : Module.Dual ℂ (⨂[ℂ] τ, A τ), (∀ (τ : ι) (x : ∀ σ, A σ), π τ (x τ) = 0 → l (PiTensorProduct.tprod ℂ x) = 0) → ∀ z, PiTensorProduct.map π z = 0 → l z = 0 := by
  intro ι _ _ A B _ _ _ _ π hπ

  have hsec : ∀ τ, ∃ g : B τ →ₗ[ℂ] A τ, π τ ∘ₗ g = LinearMap.id := fun τ =>
    (π τ).exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr (hπ τ))
  choose s hs using hsec
  have hπs : ∀ τ b, π τ (s τ b) = b := fun τ b => by
    simpa using LinearMap.congr_fun (hs τ) b

  have back : ∀ b, PiTensorProduct.map π (PiTensorProduct.map s b) = b := by
    intro b
    induction b using PiTensorProduct.induction_on with
    | smul_tprod r f => simp [PiTensorProduct.map_tprod, hπs]
    | add p q hp hq => rw [map_add (f := _), map_add (f := _), hp, hq]
  refine ⟨fun b => ⟨_, back b⟩, ?_⟩
  intro l hl

  have key : ∀ x : ∀ σ, A σ, l (PiTensorProduct.tprod ℂ x) =
      l (PiTensorProduct.tprod ℂ (fun σ => s σ (π σ (x σ)))) := by
    intro x
    have step : ∀ S : Finset ι, l (PiTensorProduct.tprod ℂ x) =
        l (PiTensorProduct.tprod ℂ (fun σ => if σ ∈ S then s σ (π σ (x σ)) else x σ)) := by
      intro S
      induction S using Finset.induction_on with
      | empty => simp
      | insert a S ha ih =>
        rw [ih]
        have h1 : (fun σ => if σ ∈ S then s σ (π σ (x σ)) else x σ) =
            Function.update (fun σ => if σ ∈ S then s σ (π σ (x σ)) else x σ) a (x a) := by
          funext σ
          by_cases h : σ = a
          · subst h; simp [ha]
          · rw [Function.update_of_ne h]
        have h2 : (fun σ => if σ ∈ insert a S then s σ (π σ (x σ)) else x σ) =
            Function.update (fun σ => if σ ∈ S then s σ (π σ (x σ)) else x σ) a
              (s a (π a (x a))) := by
          funext σ
          by_cases h : σ = a
          · subst h; simp
          · rw [Function.update_of_ne h]; simp [Finset.mem_insert, h]
        have h4 := hl a (Function.update (fun σ => if σ ∈ S then s σ (π σ (x σ)) else x σ) a
          (x a - s a (π a (x a)))) (by simp [hπs])
        rw [MultilinearMap.map_update_sub, map_sub, sub_eq_zero, ← h1] at h4
        rw [h2, h4]
    simpa using step Finset.univ
  have hall : ∀ z, l z = l (PiTensorProduct.map s (PiTensorProduct.map π z)) := by
    intro z
    induction z using PiTensorProduct.induction_on with
    | smul_tprod r f => simp [PiTensorProduct.map_tprod, key f]
    | add p q hp hq => rw [map_add (f := _), map_add (f := _), map_add (f := _), map_add (f := _), ← hp, ← hq]
  intro z hz
  rw [hall z, hz, map_zero, map_zero]

end GlobalTheory.TensorKernel
