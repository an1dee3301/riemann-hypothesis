module

public import Mathlib
public import Init.Classical
public import Init.Core
public import Init.Data.Fin.Basic
public import Init.Data.Fin.Lemmas
public import Init.Data.Function
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Submonoid.BigOperators
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Subsemigroup.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Basic
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Equiv
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Module.Submodule.LinearMap
public import Mathlib.Algebra.Module.Submodule.Map
public import Mathlib.Algebra.Module.Submodule.Range
public import Mathlib.Algebra.Notation.Pi.Basic
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.IsEmpty.Defs
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Basic.Unique
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Set.CoeSort
public import Mathlib.Data.Set.Defs
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.LinearAlgebra.Span.Basic
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Fin.Basic
public import Mathlib.Order.Notation

@[expose] public section

open Submodule

namespace GlobalTheory.SubmodulePowSimple

variable {P : Type} [AddCommGroup P] [Module ℂ P] {ι : Type}

def equivValues (a : ι → Module.End ℂ P) (m : ℕ) (N : Submodule ℂ (Fin m → P)) :
    Set (Fin m → P) :=
  {v | ∃ S : P →ₗ[ℂ] (Fin m → P), (∀ i p, S (a i p) = fun j => a i (S p j)) ∧
    (∀ p, S p ∈ N) ∧ ∃ q, v = S q}

def snocZero (m : ℕ) : (Fin m → P) →ₗ[ℂ] (Fin (m+1) → P) where
  toFun z := Fin.snoc (α := fun _ => P) z 0
  map_add' x y := by
    funext j; refine Fin.lastCases ?_ (fun j => ?_) j <;> simp
  map_smul' c x := by
    funext j; refine Fin.lastCases ?_ (fun j => ?_) j <;> simp

lemma snocZero_diag {m : ℕ} (b : Module.End ℂ P) (z : Fin m → P) :
    snocZero m (fun j => b (z j)) = fun j => b (snocZero m z j) := by
  funext j; refine Fin.lastCases ?_ (fun j => ?_) j <;> simp [snocZero]

lemma single_diag {m : ℕ} (b : Module.End ℂ P) (p : P) :
    (Pi.single (Fin.last m) (b p) : Fin (m+1) → P) = fun j => b ((Pi.single (Fin.last m) p : Fin (m+1) → P) j) := by
  funext j
  by_cases h : j = Fin.last m
  · subst h; simp
  · simp [Pi.single_eq_of_ne h]

theorem mem_span_equivValues (a : ι → Module.End ℂ P)
    (hs : ∀ B : Submodule ℂ P, (∀ i, ∀ p ∈ B, a i p ∈ B) → B ≠ ⊥ → B = ⊤) :
    ∀ (m : ℕ) (N : Submodule ℂ (Fin m → P)), (∀ i, ∀ y ∈ N, (fun j => a i (y j)) ∈ N) →
    ∀ y ∈ N, y ∈ span ℂ (equivValues a m N) := by
  intro m
  induction m with
  | zero =>
    intro N _ y _
    rw [Subsingleton.elim y 0]; exact zero_mem _
  | succ m ih =>
    intro N hN y hy
    let B : Submodule ℂ P := N.comap (LinearMap.single ℂ (fun _ : Fin (m+1) => P) (Fin.last m))
    have hBmem : ∀ p, p ∈ B ↔ (Pi.single (Fin.last m) p : Fin (m+1) → P) ∈ N := fun p => by
      simp [B]
    have hBst : ∀ i, ∀ p ∈ B, a i p ∈ B := by
      intro i p hp
      rw [hBmem] at hp ⊢
      rw [single_diag]; exact hN i _ hp
    by_cases hB : B = ⊥
    · let I : (Fin (m+1) → P) →ₗ[ℂ] (Fin m → P) := LinearMap.funLeft ℂ P Fin.castSucc
      have hinj : ∀ x₁ ∈ N, ∀ x₂ ∈ N, I x₁ = I x₂ → x₁ = x₂ := by
        intro x₁ h₁ x₂ h₂ he
        have hd : x₁ - x₂ ∈ N := N.sub_mem h₁ h₂
        have hs' : x₁ - x₂ = Pi.single (Fin.last m) ((x₁ - x₂) (Fin.last m)) := by
          funext j; refine Fin.lastCases ?_ (fun j => ?_) j
          · simp
          · have h := congrFun he j
            change x₁ (Fin.castSucc j) = x₂ (Fin.castSucc j) at h
            rw [Pi.single_eq_of_ne (Fin.castSucc_lt_last j).ne]
            simp [h]
        have hB' : (x₁ - x₂) (Fin.last m) ∈ B := by
          rw [hBmem, ← hs']; exact hd
        rw [hB, Submodule.mem_bot] at hB'
        rw [hB', Pi.single_zero] at hs'
        exact sub_eq_zero.mp hs'
      let N0 := N.map I
      have hN0 : ∀ i, ∀ w ∈ N0, (fun j => a i (w j)) ∈ N0 := by
        intro i w hw
        obtain ⟨x, hx, rfl⟩ := hw
        exact ⟨_, hN i x hx, rfl⟩
      have lift : ∀ S : P →ₗ[ℂ] (Fin m → P), (∀ p, S p ∈ N0) →
          ∃ S' : P →ₗ[ℂ] (Fin (m+1) → P), (∀ p, S' p ∈ N) ∧ ∀ p, I (S' p) = S p := by
        intro S hS
        let J : N →ₗ[ℂ] (Fin m → P) := I ∘ₗ N.subtype
        have hJ : Function.Injective J := by
          intro u v huv; exact Subtype.ext (hinj u u.2 v v.2 huv)
        have hS' : ∀ p, S p ∈ LinearMap.range J := by
          intro p; obtain ⟨x, hx, hxe⟩ := hS p; exact ⟨⟨x, hx⟩, hxe⟩
        have key : ∀ v, J ((LinearEquiv.ofInjective J hJ).symm v) = v := fun v => by
          have h := congrArg Subtype.val ((LinearEquiv.ofInjective J hJ).apply_symm_apply v)
          rw [LinearEquiv.ofInjective_apply] at h
          exact h
        refine ⟨N.subtype ∘ₗ (LinearEquiv.ofInjective J hJ).symm.toLinearMap ∘ₗ
          S.codRestrict _ hS', fun p => Subtype.property _, fun p => ?_⟩
        exact key ⟨S p, hS' p⟩
      have h1 := ih N0 hN0 (I y) ⟨y, hy, rfl⟩
      obtain ⟨n, f, g, hfg⟩ := (Submodule.mem_span_set').mp h1
      have hg : ∀ k, ∃ S : P →ₗ[ℂ] (Fin m → P), (∀ i p, S (a i p) = fun j => a i (S p j)) ∧
          (∀ p, S p ∈ N0) ∧ ∃ q, (g k : Fin m → P) = S q := fun k => (g k).2
      choose S hSa hSN q hq using hg
      choose S' hS'N hS'I using fun k => lift (S k) (hSN k)
      have hS'a : ∀ k i p, S' k (a i p) = fun j => a i (S' k p j) := by
        intro k i p
        apply hinj _ (hS'N k _) _ (hN i _ (hS'N k p))
        rw [hS'I, hSa, ← hS'I k p]; rfl
      have hy_eq : y = ∑ k, f k • S' k (q k) := by
        apply hinj _ hy _ (sum_mem fun k _ => N.smul_mem _ (hS'N k _))
        set_option synthInstance.maxHeartbeats 100000 in
          rw [← hfg, map_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [map_smul, hS'I, hq]
      rw [hy_eq]
      exact sum_mem fun k _ => smul_mem _ _ (subset_span ⟨S' k, hS'a k, hS'N k, q k, rfl⟩)
    · have hBt := hs B hBst hB
      have hmem : ∀ p, (Pi.single (Fin.last m) p : Fin (m+1) → P) ∈ N := fun p => by
        rw [← hBmem, hBt]; exact Submodule.mem_top
      obtain ⟨y', hy'⟩ : ∃ y', y' = y - Pi.single (Fin.last m) (y (Fin.last m)) := ⟨_, rfl⟩
      have hy'N : y' ∈ N := hy' ▸ N.sub_mem hy (hmem _)
      have hy'last : y' (Fin.last m) = 0 := by simp [hy']
      let N' := N.comap (snocZero m)
      have hN' : ∀ i, ∀ z ∈ N', (fun j => a i (z j)) ∈ N' := by
        intro i z hz
        show snocZero m _ ∈ N
        rw [snocZero_diag]; exact hN i _ hz
      let z : Fin m → P := fun j => y' (Fin.castSucc j)
      have hz : snocZero m z = y' := by
        funext j; refine Fin.lastCases ?_ (fun j => ?_) j
        · simp [snocZero, hy'last]
        · simp [snocZero, z]
      have hzN' : z ∈ N' := show snocZero m z ∈ N from hz ▸ hy'N
      have h1 := ih N' hN' z hzN'
      have h2 : y' ∈ span ℂ (equivValues a (m+1) N) := by
        rw [← hz]
        have h := Submodule.mem_map_of_mem (f := snocZero m) h1
        rw [Submodule.map_span] at h
        refine Submodule.span_mono ?_ h
        rintro _ ⟨v, ⟨S, hSa, hSN, q, rfl⟩, rfl⟩
        refine ⟨snocZero m ∘ₗ S, ?_, fun p => hSN p, q, rfl⟩
        intro i p; simp only [LinearMap.comp_apply, hSa, snocZero_diag]
      have h3 : (Pi.single (Fin.last m) (y (Fin.last m)) : Fin (m+1) → P) ∈
          span ℂ (equivValues a (m+1) N) := by
        refine Submodule.subset_span
          ⟨LinearMap.single ℂ (fun _ : Fin (m+1) => P) (Fin.last m), ?_, ?_, y (Fin.last m), rfl⟩
        · intro i p; simp only [LinearMap.single_apply]; exact single_diag _ _
        · intro p; simpa using hmem p
      have : y = y' + Pi.single (Fin.last m) (y (Fin.last m)) := by simp [hy']
      rw [this]; exact add_mem h2 h3

end GlobalTheory.SubmodulePowSimple

namespace GlobalTheory

theorem submodule_pow_simple_eq_sum_equiv_values :
    ∀ {P : Type} [AddCommGroup P] [Module ℂ P] {ι : Type} (a : ι → Module.End ℂ P),
    (∀ B : Submodule ℂ P, (∀ i, ∀ p ∈ B, a i p ∈ B) → B ≠ ⊥ → B = ⊤) →
    ∀ (m : ℕ) (N : Submodule ℂ (Fin m → P)), (∀ i, ∀ y ∈ N, (fun j => a i (y j)) ∈ N) →
    ∀ y ∈ N, ∃ (n : ℕ) (Sm : Fin n → (P →ₗ[ℂ] (Fin m → P))) (q : Fin n → P),
      (∀ l i p, Sm l (a i p) = fun j => a i (Sm l p j)) ∧ (∀ l p, Sm l p ∈ N) ∧
        y = ∑ l, Sm l (q l) := by
  intro P _ _ ι a hs m N hN y hy
  obtain ⟨n, f, g, hfg⟩ :=
    (Submodule.mem_span_set').mp (SubmodulePowSimple.mem_span_equivValues a hs m N hN y hy)
  have hg : ∀ k, ∃ S : P →ₗ[ℂ] (Fin m → P), (∀ i p, S (a i p) = fun j => a i (S p j)) ∧
      (∀ p, S p ∈ N) ∧ ∃ q, (g k : Fin m → P) = S q := fun k => (g k).2
  choose S hSa hSN q hq using hg
  refine ⟨n, S, fun k => f k • q k, hSa, hSN, ?_⟩
  rw [← hfg]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hq, map_smul]

end GlobalTheory
