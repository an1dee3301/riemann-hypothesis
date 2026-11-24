module

public import Mathlib
public import Development.Core20Slim.Development.AutomorphicArithmetic.ThetaCorrespondence.HoweDuality.FactorApply
public import Init.Classical
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.PropLemmas
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.IsApply
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Module.Submodule.Map
public import Mathlib.Algebra.Module.Submodule.Range
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.IsEmpty.Defs
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Empty
public import Mathlib.Data.Finset.Insert
public import Mathlib.Data.Finset.Lattice.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.Span.Basic
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.Order.BoundedOrder.Basic
public import Mathlib.Order.CompleteLattice.Basic
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Defs
public import Mathlib.Order.ConditionallyCompletePartialOrder.Defs
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Notation
public import Mathlib.Order.SetNotation

@[expose] public section

open scoped TensorProduct
open UpperTheory.Lit.HoweDuality

theorem UpperTheory.Lit.HoweDuality.nak :
    ∀ {M T R : Type} [AddCommGroup M] [Module ℂ M] [AddCommGroup T] [Module ℂ T] (j : R → M →ₗ[ℂ] T) (Op : Set (Module.End ℂ M)) (Rel K : Submodule ℂ M) (N : Submodule ℂ T), (⨆ r, LinearMap.range (j r)) = ⊤ → (∀ g ∈ Op, ∃ Φ : Module.End ℂ T, (∀ r x, Φ (j r x) = j r (g x)) ∧ ∀ t ∈ N, Φ t ∈ N) → (∀ r, ∀ x ∈ Rel, j r x ∈ N) → RadFin Op Rel K → N ⊔ (⨆ r, K.map (j r)) = ⊤ → N = ⊤ := by
  intro M T R _ _ _ _ j Op Rel K N hspan hOp hRel hRad hsup
  classical
  have h1 : ∀ e ∈ Algebra.adjoin ℂ Op,
      ∃ Φ : Module.End ℂ T, (∀ r x, Φ (j r x) = j r (e x)) ∧ ∀ t ∈ N, Φ t ∈ N := by
    intro e he
    induction he using Algebra.adjoin_induction with
    | mem g hg => exact hOp g hg
    | algebraMap c =>
      refine ⟨c • (1 : Module.End ℂ T), fun r x => ?_, fun t ht => ?_⟩
      · simp [Algebra.algebraMap_eq_smul_one]
      · simpa using N.smul_mem c ht
    | add a b _ _ ha hb =>
      obtain ⟨A, hA, hAN⟩ := ha
      obtain ⟨B, hB, hBN⟩ := hb
      refine ⟨A + B, fun r x => ?_, fun t ht => ?_⟩
      · simp [hA, hB]
      · simpa using N.add_mem (hAN t ht) (hBN t ht)
    | mul a b _ _ ha hb =>
      obtain ⟨A, hA, hAN⟩ := ha
      obtain ⟨B, hB, hBN⟩ := hb
      refine ⟨A * B, fun r x => ?_, fun t ht => ?_⟩
      · simp [hA, hB]
      · simpa using hAN _ (hBN t ht)
  have h2 : ∀ u ∈ (⨆ r, K.map (j r)), ∃ S : Finset M, (∀ k ∈ S, k ∈ K) ∧
      ∀ (e : Module.End ℂ M) (Φ : Module.End ℂ T), (∀ r x, Φ (j r x) = j r (e x)) →
        (∀ k ∈ S, e k ∈ Rel) → Φ u ∈ N := by
    intro u hu
    induction hu using Submodule.iSup_induction' with
    | mem r x hx =>
      obtain ⟨k, hk, rfl⟩ := hx
      refine ⟨{k}, by simpa using hk, fun e Φ hΦ hS => ?_⟩
      rw [hΦ]
      exact hRel r _ (hS k (Finset.mem_singleton_self k))
    | zero => exact ⟨∅, by simp, fun e Φ _ _ => by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨S, hS, hS'⟩ := hx
      obtain ⟨S2, hS2, hS2'⟩ := hy
      refine ⟨S ∪ S2, fun k hk => ?_, fun e Φ hΦ h => ?_⟩
      · rcases Finset.mem_union.1 hk with h | h
        · exact hS k h
        · exact hS2 k h
      · rw [map_add (f := _)]
        exact N.add_mem (hS' e Φ hΦ fun k hk => h k (Finset.mem_union_left _ hk))
          (hS2' e Φ hΦ fun k hk => h k (Finset.mem_union_right _ hk))
  obtain ⟨s, hGen, hs⟩ := hRad
  have h3 : ∀ r, j r s ∈ N := by
    intro r
    have hm : j r s ∈ N ⊔ (⨆ r, K.map (j r)) := by rw [hsup]; trivial
    obtain ⟨n, hn, u, hu, hnu⟩ := Submodule.mem_sup.1 hm
    obtain ⟨S, hSK, hS⟩ := h2 u hu
    obtain ⟨e, he, hes, heS⟩ := hs S hSK
    obtain ⟨Φ, hΦ, hΦN⟩ := h1 e he
    have : j r s = Φ n + Φ u := by rw [← map_add (f := _), hnu, hΦ, hes]
    rw [this]
    exact N.add_mem (hΦN n hn) (hS e Φ hΦ heS)
  have h4 : ∀ r, N.comap (j r) = ⊤ := by
    intro r
    refine hGen _ (fun x hx => hRel r x hx) (fun g hg x hx => ?_) (h3 r)
    obtain ⟨Φ, hΦ, hΦN⟩ := hOp g hg
    show j r (g x) ∈ N
    rw [← hΦ]
    exact hΦN _ hx
  rw [eq_top_iff, ← hspan]
  refine iSup_le fun r => ?_
  rintro _ ⟨x, rfl⟩
  have : x ∈ N.comap (j r) := by rw [h4 r]; trivial
  exact this
