module

public import Mathlib
public import Formalism.LocalToGlobal.Divisibility.CoefMod
public import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
public import Formalism.GradedWeylDivisibility.FinalD
public import Formalism.GradedWeylDivisibility.StatementD
public import Formalism.LocalRingCardinality.DataCoeff
public import Init.Classical
public import Init.Core
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Map
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MonoidAlgebra.Module
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Empty
public import Mathlib.Data.Finset.Insert
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Multilinear.Basic
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.Logic.Function.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic

@[expose] public section

set_option autoImplicit false
noncomputable section
open MvPolynomial Formalism.BasicNotions Formalism.L2.DIV
open scoped Matrix

namespace GlobalTheory

theorem multilinear_mem_span_of_mem_span {K ι M N : Type} [Field K] [Fintype ι]
    [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
    (m : (ι → M) →ₘₗ[K] N) (S : ι → Set M) (f : ι → M)
    (hf : ∀ τ, f τ ∈ Submodule.span K (S τ)) :
    m f ∈ Submodule.span K {P | ∃ g : ι → M, (∀ τ, g τ ∈ S τ) ∧ P = m g} := by
  classical
  have key : ∀ (s : Finset ι) (f : ι → M), (∀ τ, f τ ∈ Submodule.span K (S τ)) →
      (∀ τ, τ ∉ s → f τ ∈ S τ) →
      m f ∈ Submodule.span K {P | ∃ g : ι → M, (∀ τ, g τ ∈ S τ) ∧ P = m g} := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro f _ h
      exact Submodule.subset_span ⟨f, fun τ => h τ (Finset.notMem_empty τ), rfl⟩
    | insert a s ha ih =>
      intro f h1 h2
      have hle : Submodule.span K (S a) ≤
          (Submodule.span K {P | ∃ g : ι → M, (∀ τ, g τ ∈ S τ) ∧ P = m g}).comap
            (m.toLinearMap f a) := by
        rw [Submodule.span_le]
        intro x hx
        rw [SetLike.mem_coe, Submodule.mem_comap, MultilinearMap.toLinearMap_apply]
        apply ih
        · intro τ
          by_cases hτ : τ = a
          · subst hτ
            rw [Function.update_self]
            exact Submodule.subset_span hx
          · rw [Function.update_of_ne hτ]
            exact h1 τ
        · intro τ hτs
          by_cases hτ : τ = a
          · subst hτ
            rw [Function.update_self]
            exact hx
          · rw [Function.update_of_ne hτ]
            exact h2 τ (by simp [hτ, hτs])
      have h := hle (h1 a)
      rw [Submodule.mem_comap, MultilinearMap.toLinearMap_apply, Function.update_eq_self] at h
      exact h
  exact key Finset.univ f hf (fun τ h => absurd (Finset.mem_univ τ) h)

theorem coefSpace_le_span_pure_tensors (K : Type) [Field K] {ι : Type} [Fintype ι] {n : ℕ}
    (lam : ι → DomWeight n) (S : ι → Set (MvPolynomial (Fin n × Fin n) K))
    (hS : ∀ τ, nablaSq K n (lam τ) ≤ Submodule.span K (S τ)) :
    VV K lam ≤ Submodule.span K
      {P | ∃ f : ι → MvPolynomial (Fin n × Fin n) K, (∀ τ, f τ ∈ S τ) ∧ P = ten f} := by
  classical
  let m : (ι → MvPolynomial (Fin n × Fin n) K) →ₘₗ[K]
      (MvPolynomial (ι × Fin n × Fin n) K) :=
    (MultilinearMap.mkPiAlgebra K ι (MvPolynomial (ι × Fin n × Fin n) K)).compLinearMap
      (fun τ => (Formalism.GradedWeylDivisibility.blockEmb K τ).toLinearMap)
  have hm : ∀ f, m f = ten f := fun f => rfl
  unfold VV Formalism.GradedWeylDivisibility.tensorLat
  rw [Submodule.span_le]
  rintro P ⟨F, hF, rfl⟩
  exact multilinear_mem_span_of_mem_span m S F (fun τ => hS τ (hF τ))

end GlobalTheory
