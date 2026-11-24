module

public import Mathlib
public import Formalism.FockGram.StatementFock
public import Formalism.SmithDeterminants.StatementGram
public import Init.Classical
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Function
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.NonUnitalHom
public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MonoidAlgebra.Module
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Disjoint
public import Mathlib.Data.Finset.Empty
public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Finset.Insert
public import Mathlib.Data.Finset.Lattice.Basic
public import Mathlib.Data.Finsupp.Basic
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Disjoint
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

noncomputable section

namespace GlobalTheory.JointHarm

open MvPolynomial Matrix

section Minors

variable {R : Type*} [CommRing R]

variable {n l : ℕ}

end Minors

variable {n p q : ℕ}

section Killed

end Killed

section Fock

open Formalism.E

theorem fock_add_left {σ : Type} (P P' Q : MvPolynomial σ ℂ) :
    fock (P + P') Q = fock P Q + fock P' Q := by
  classical
  have key : ∀ (F : MvPolynomial σ ℂ) (s : Finset (σ →₀ ℕ)), F.support ⊆ s →
      fock F Q = ∑ m ∈ s, F.coeff m * star (Q.coeff m) * (Formalism.A.mfact m : ℂ) := by
    intro F s hs
    refine Finset.sum_subset hs fun m _ hm => ?_
    rw [notMem_support_iff.mp hm, zero_mul, zero_mul]
  rw [key _ _ support_add, key P _ Finset.subset_union_left, key P' _ Finset.subset_union_right,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_add]; ring

theorem fock_monomial_left {σ : Type} (α : σ →₀ ℕ) (c : ℂ) (Q : MvPolynomial σ ℂ) :
    fock (monomial α c) Q = c * star (Q.coeff α) * (Formalism.A.mfact α : ℂ) := by
  classical
  unfold fock
  rw [support_monomial]
  split_ifs with hc
  · simp [hc]
  · simp

variable {σ₁ σ₂ τ : Type} {f : σ₁ → τ} {g : σ₂ → τ}

theorem mapDomain_add_inj (hf : Function.Injective f) (hg : Function.Injective g)
    (hfg : ∀ x y, f x ≠ g y) {α α' : σ₁ →₀ ℕ} {β β' : σ₂ →₀ ℕ}
    (h : α.mapDomain f + β.mapDomain g = α'.mapDomain f + β'.mapDomain g) : α = α' ∧ β = β' := by
  constructor
  · ext x
    have := DFunLike.congr_fun h (f x)
    have hx : f x ∉ Set.range g := fun ⟨y, hy⟩ => hfg x y hy.symm
    simpa [Finsupp.mapDomain_apply_of_injective hf, Finsupp.mapDomain_notin_range _ _ hx] using this
  · ext y
    have := DFunLike.congr_fun h (g y)
    have hy : g y ∉ Set.range f := fun ⟨x, hx⟩ => hfg x y hx
    simpa [Finsupp.mapDomain_apply_of_injective hg, Finsupp.mapDomain_notin_range _ _ hy] using this

theorem coeff_rename_mul (hf : Function.Injective f) (hg : Function.Injective g)
    (hfg : ∀ x y, f x ≠ g y) (α : σ₁ →₀ ℕ) (β : σ₂ →₀ ℕ) (P : MvPolynomial σ₁ ℂ)
    (Q : MvPolynomial σ₂ ℂ) :
    AddMonoidAlgebra.coeff (rename f P * rename g Q) (α.mapDomain f + β.mapDomain g) = AddMonoidAlgebra.coeff P α * AddMonoidAlgebra.coeff Q β := by
  classical
  induction P using MvPolynomial.induction_on' with
  | add P P' h h' => simp only [map_add (f := _), add_mul, MvPolynomial.coeff_add, h, h']
  | monomial α' x =>
    induction Q using MvPolynomial.induction_on' with
    | add Q Q' h h' => simp only [map_add (f := _), mul_add, MvPolynomial.coeff_add, h, h']
    | monomial β' y =>
      rw [rename_monomial, rename_monomial, monomial_mul, coeff_monomial, coeff_monomial,
        coeff_monomial]
      by_cases h : α'.mapDomain f + β'.mapDomain g = α.mapDomain f + β.mapDomain g
      · obtain ⟨rfl, rfl⟩ := mapDomain_add_inj hf hg hfg h
        simp
      · rw [if_neg h]
        split_ifs with h1 h2
        · exact absurd (by rw [h1, h2]) h
        all_goals simp

theorem mfact_mapDomain_add (hf : Function.Injective f) (hg : Function.Injective g)
    (hfg : ∀ x y, f x ≠ g y) (α : σ₁ →₀ ℕ) (β : σ₂ →₀ ℕ) :
    Formalism.A.mfact (α.mapDomain f + β.mapDomain g) = Formalism.A.mfact α * Formalism.A.mfact β := by
  classical
  unfold Formalism.A.mfact
  rw [Finsupp.prod_add_index_of_disjoint, Finsupp.prod_mapDomain_index_inj hf,
    Finsupp.prod_mapDomain_index_inj hg]
  rw [Finsupp.mapDomain_support_of_injective hf, Finsupp.mapDomain_support_of_injective hg,
    Finset.disjoint_left]
  intro t h1 h2
  obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp h1
  obtain ⟨y, -, hy⟩ := Finset.mem_image.mp h2
  exact hfg x y hy.symm

theorem fock_rename_mul (hf : Function.Injective f) (hg : Function.Injective g)
    (hfg : ∀ x y, f x ≠ g y) (P P' : MvPolynomial σ₁ ℂ) (Q Q' : MvPolynomial σ₂ ℂ) :
    fock (rename f P * rename g Q) (rename f P' * rename g Q') = fock P P' * fock Q Q' := by
  induction P using MvPolynomial.induction_on' with
  | add P₁ P₂ h h' => simp only [map_add (f := _), add_mul, fock_add_left, h, h']
  | monomial α x =>
    induction Q using MvPolynomial.induction_on' with
    | add Q₁ Q₂ h h' => simp only [map_add (f := _), mul_add, fock_add_left, h, h']
    | monomial β y =>
      rw [rename_monomial, rename_monomial, monomial_mul, fock_monomial_left, fock_monomial_left,
        fock_monomial_left, coeff_rename_mul hf hg hfg, mfact_mapDomain_add hf hg hfg, star_mul']
      push_cast
      ring

end Fock

end GlobalTheory.JointHarm
