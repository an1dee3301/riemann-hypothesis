module

public import Mathlib
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsHermRingRat
public import Development.AbelianVarietyTheory.Definitions.Foundations.NonemptyAlgHomOfNotIsField
public import Batteries.Logic
public import Init.Classical
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Ext
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Submonoid.MulAction
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Notation.Prod
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Equiv
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Prod
public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Prod.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Defs
public import Mathlib.Order.Defs.Lattice
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.Tactic.FieldSimp.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

open NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.KFin
open Formalism.UG (cT)
open scoped TensorProduct NNReal

namespace GlobalTheory.CompanionTheory.KFin

theorem exists_larger_of_valuationSubring {k : Type} [Field k] (O : ValuationSubring k) (a b : k) :
    ∃ c : k, (c = a ∨ c = b) ∧ (∃ u ∈ O, a = c * u) ∧ (∃ u ∈ O, b = c * u) := by
  by_cases ha : a = 0
  · exact ⟨b, Or.inr rfl, ⟨0, O.zero_mem, by simp [ha]⟩, ⟨1, O.one_mem, by simp⟩⟩
  by_cases hb : b = 0
  · exact ⟨a, Or.inl rfl, ⟨1, O.one_mem, by simp⟩, ⟨0, O.zero_mem, by simp [hb]⟩⟩
  rcases O.mem_or_inv_mem (a / b) with h | h
  · exact ⟨b, Or.inr rfl, ⟨a / b, h, by field_simp⟩, ⟨1, O.one_mem, by simp⟩⟩
  · refine ⟨a, Or.inl rfl, ⟨1, O.one_mem, by simp⟩, ⟨(a / b)⁻¹, h, ?_⟩⟩
    field_simp

theorem fg_eq_prod_principal {k R : Type} [Field k] [CommRing R] (O : ValuationSubring k)
    (φ : R ≃+* k × k) (𝔬 : Subring R)
    (h𝔬 : ∀ r, r ∈ 𝔬 ↔ (φ r).1 ∈ O ∧ (φ r).2 ∈ O) (I : Submodule 𝔬 R) (hI : I.FG) :
    ∃ α β : k, ∀ r, r ∈ I ↔ (∃ x ∈ O, (φ r).1 = α * x) ∧ (∃ y ∈ O, (φ r).2 = β * y) := by
  induction I, hI using Submodule.fg_induction with
  | singleton r₀ =>
    refine ⟨(φ r₀).1, (φ r₀).2, fun r => ?_⟩
    rw [Submodule.mem_span_singleton]
    constructor
    · rintro ⟨t, rfl⟩
      have ht := (h𝔬 t).1 t.2
      have hs : φ (t • r₀) = φ (t : R) * φ r₀ := by
        rw [Subring.smul_def, smul_eq_mul, map_mul]
      refine ⟨⟨(φ (t : R)).1, ht.1, ?_⟩, ⟨(φ (t : R)).2, ht.2, ?_⟩⟩
      · rw [hs, Prod.fst_mul, mul_comm]
      · rw [hs, Prod.snd_mul, mul_comm]
    · rintro ⟨⟨x, hx, h1⟩, ⟨y, hy, h2⟩⟩
      have hmem : φ.symm (x, y) ∈ 𝔬 := by
        rw [h𝔬]
        simpa using ⟨hx, hy⟩
      refine ⟨⟨φ.symm (x, y), hmem⟩, ?_⟩
      apply φ.injective
      rw [Subring.smul_def, smul_eq_mul, map_mul, RingEquiv.apply_symm_apply]
      ext
      · simp [h1, mul_comm]
      · simp [h2, mul_comm]
  | sup I₁ I₂ _ _ ih₁ ih₂ =>
    obtain ⟨α₁, β₁, h₁⟩ := ih₁
    obtain ⟨α₂, β₂, h₂⟩ := ih₂
    obtain ⟨α, hα, ⟨u₁, hu₁, e₁⟩, ⟨u₂, hu₂, e₂⟩⟩ := exists_larger_of_valuationSubring O α₁ α₂
    obtain ⟨β, hβ, ⟨v₁, hv₁, f₁⟩, ⟨v₂, hv₂, f₂⟩⟩ := exists_larger_of_valuationSubring O β₁ β₂
    refine ⟨α, β, fun r => ?_⟩
    constructor
    · intro hr
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hr
      obtain ⟨⟨x₁, hx₁, p₁⟩, ⟨y₁, hy₁, q₁⟩⟩ := (h₁ a).1 ha
      obtain ⟨⟨x₂, hx₂, p₂⟩, ⟨y₂, hy₂, q₂⟩⟩ := (h₂ b).1 hb
      refine ⟨⟨u₁ * x₁ + u₂ * x₂, O.add_mem _ _ (O.mul_mem _ _ hu₁ hx₁) (O.mul_mem _ _ hu₂ hx₂), ?_⟩,
        ⟨v₁ * y₁ + v₂ * y₂, O.add_mem _ _ (O.mul_mem _ _ hv₁ hy₁) (O.mul_mem _ _ hv₂ hy₂), ?_⟩⟩
      · rw [map_add (f := _), Prod.fst_add, p₁, p₂, e₁, e₂]
        ring
      · rw [map_add (f := _), Prod.snd_add, q₁, q₂, f₁, f₂]
        ring
    · rintro ⟨⟨x, hx, p⟩, ⟨y, hy, q⟩⟩
      have hsplit : r = φ.symm ((φ r).1, 0) + φ.symm (0, (φ r).2) := by
        apply φ.injective
        rw [map_add (f := _), RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
        ext <;> simp
      rw [hsplit]
      refine Submodule.add_mem _ ?_ ?_
      · rcases hα with rfl | rfl
        · refine Submodule.mem_sup_left ((h₁ _).2 ?_)
          simp only [RingEquiv.apply_symm_apply]
          exact ⟨⟨x, hx, p⟩, ⟨0, O.zero_mem, by simp⟩⟩
        · refine Submodule.mem_sup_right ((h₂ _).2 ?_)
          simp only [RingEquiv.apply_symm_apply]
          exact ⟨⟨x, hx, p⟩, ⟨0, O.zero_mem, by simp⟩⟩
      · rcases hβ with rfl | rfl
        · refine Submodule.mem_sup_left ((h₁ _).2 ?_)
          simp only [RingEquiv.apply_symm_apply]
          exact ⟨⟨0, O.zero_mem, by simp⟩, ⟨y, hy, q⟩⟩
        · refine Submodule.mem_sup_right ((h₂ _).2 ?_)
          simp only [RingEquiv.apply_symm_apply]
          exact ⟨⟨0, O.zero_mem, by simp⟩, ⟨y, hy, q⟩⟩

end GlobalTheory.CompanionTheory.KFin
