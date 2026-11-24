module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsInfFamAndStdChar
public import Formalism.LocalRingCardinality.DataTheta
public import Init.Core
public import Init.Data.Bool
public import Init.Data.Int.Basic
public import Init.Data.List.Basic
public import Init.Data.List.BasicAux
public import Init.Data.List.Lemmas
public import Init.Data.Nat.Lemmas
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.GetElem
public import Init.Prelude
public import Init.PropLemmas
public import Init.SimpLemmas
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Dedup
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Filter
public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Finset.Lattice.Basic
public import Mathlib.Data.List.GetD
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Rat.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum

namespace GlobalTheory.Chain.ItPairCompare

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem mem_signed {l₁ l₂ : List ℚ} {c x : ℚ} {s : Bool} :
    (x, s) ∈ signed l₁ l₂ c ↔ (s = true ∧ x - c ∈ l₁) ∨ (s = false ∧ x - c ∈ l₂) := by
  simp only [signed, Finset.mem_union, List.mem_toFinset, List.mem_map, Prod.mk.injEq]
  constructor
  · rintro (⟨a, ha, rfl, rfl⟩ | ⟨a, ha, rfl, rfl⟩)
    · exact Or.inl ⟨rfl, by simpa using ha⟩
    · exact Or.inr ⟨rfl, by simpa using ha⟩
  · rintro (⟨rfl, h⟩ | ⟨rfl, h⟩)
    · exact Or.inl ⟨_, h, by ring, rfl⟩
    · exact Or.inr ⟨_, h, by ring, rfl⟩



theorem mem_iff_getD {l : List ℚ} {n : ℕ} (hn : n = l.length) {x : ℚ} : x ∈ l ↔ ∃ i : Fin n, l.getD i 0 = x := by
  subst hn
  rw [List.mem_iff_getElem]
  constructor
  · rintro ⟨i, hi, rfl⟩; exact ⟨⟨i, hi⟩, List.getD_eq_getElem _ _ hi⟩
  · rintro ⟨i, rfl⟩; exact ⟨i, i.2, (List.getD_eq_getElem _ _ i.2).symm⟩

theorem cross_iff {p q : ℕ} {l₁ l₂ : List ℚ} (hp : p = l₁.length) (hq : q = l₂.length) (P : ℚ → Prop) :
    (∀ a b : Formalism.BasicNotions.TH.Ix p q, ¬ sameBlock a b → P (ofBlocks l₁ l₂ a - ofBlocks l₁ l₂ b)) ↔
      ∀ x ∈ signed l₁ l₂ 0, ∀ y ∈ signed l₁ l₂ 0, x.2 ≠ y.2 → P (x.1 - y.1) := by
  constructor
  · rintro h ⟨x, s⟩ hx ⟨y, s'⟩ hy hs
    simp only [mem_signed, sub_zero] at hx hy
    rcases hx with ⟨rfl, hx⟩ | ⟨rfl, hx⟩ <;> rcases hy with ⟨rfl, hy⟩ | ⟨rfl, hy⟩
    · exact absurd rfl hs
    · obtain ⟨i, rfl⟩ := (mem_iff_getD hp).1 hx
      obtain ⟨j, rfl⟩ := (mem_iff_getD hq).1 hy
      exact h (.inl i) (.inr j) (fun h => h)
    · obtain ⟨i, rfl⟩ := (mem_iff_getD hq).1 hx
      obtain ⟨j, rfl⟩ := (mem_iff_getD hp).1 hy
      exact h (.inr i) (.inl j) (fun h => h)
    · exact absurd rfl hs
  · intro h a b hab
    have h1 : ∀ i : Fin p, (l₁.getD i 0, true) ∈ signed l₁ l₂ 0 := fun i =>
      mem_signed.2 (Or.inl ⟨rfl, by rw [sub_zero]; exact (mem_iff_getD hp).2 ⟨i, rfl⟩⟩)
    have h2 : ∀ i : Fin q, (l₂.getD i 0, false) ∈ signed l₁ l₂ 0 := fun i =>
      mem_signed.2 (Or.inr ⟨rfl, by rw [sub_zero]; exact (mem_iff_getD hq).2 ⟨i, rfl⟩⟩)
    rcases a with i | i <;> rcases b with j | j
    · exact absurd trivial hab
    · exact h _ (h1 i) _ (h2 j) (by simp)
    · exact h _ (h2 i) _ (h1 j) (by simp)
    · exact absurd trivial hab

theorem card_filter_true {l₁ l₂ : List ℚ} (h : l₁.Nodup) :
    ((signed l₁ l₂ 0).filter fun x => x.2 = true).card = l₁.length := by
  have : ((signed l₁ l₂ 0).filter fun x => x.2 = true) = l₁.toFinset.image fun x => (x, true) := by
    ext ⟨x, s⟩
    cases s <;> simp [mem_signed]
  rw [this, Finset.card_image_of_injective _ (fun a b h => (Prod.mk.inj h).1), List.toFinset_card_of_nodup h]

theorem card_filter_false {l₁ l₂ : List ℚ} (h : l₂.Nodup) :
    ((signed l₁ l₂ 0).filter fun x => x.2 = false).card = l₂.length := by
  have : ((signed l₁ l₂ 0).filter fun x => x.2 = false) = l₂.toFinset.image fun x => (x, false) := by
    ext ⟨x, s⟩
    cases s <;> simp [mem_signed]
  rw [this, Finset.card_image_of_injective _ (fun a b h => (Prod.mk.inj h).1), List.toFinset_card_of_nodup h]

theorem card_signed {l₁ l₂ : List ℚ} (h₁ : l₁.Nodup) (h₂ : l₂.Nodup) :
    (signed l₁ l₂ 0).card = l₁.length + l₂.length := by
  rw [← card_filter_true (l₂ := l₂) h₁, ← card_filter_false (l₁ := l₁) h₂,
    ← Finset.card_filter_add_card_filter_not (s := signed l₁ l₂ 0) (fun x => x.2 = true)]
  simp




section HC

variable {R : Ranks} (P : HCParam R)














end HC

variable {D : D7}









end GlobalTheory.Chain.ItPairCompare

end
