module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.CapelliIdentity.CapelliCentralStatement
public import Init.ByCases
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Fin.Basic
public import Init.Data.Fin.Lemmas
public import Init.Data.Function
public import Init.Data.Int.Basic
public import Init.Data.List.Basic
public import Init.Data.List.OfFn
public import Init.Data.Nat.Basic
public import Init.Data.NeZero
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.BigOperators.GroupWithZero.Action
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.IsEmpty.Defs
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Finset.BooleanAlgebra
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Empty
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Logic.Function.Basic
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result

@[expose] public section

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.Lap.Capelli

open ReciprocityTheory.ChartRestriction.DS

section SlopeTestRemainingChoices

variable {𝒰 : Type*} [Ring 𝒰]

theorem prod_ofFn_update_eq {p : ℕ} (f : Fin p → 𝒰) (j : Fin p) :
    ∃ A B : 𝒰, ∀ v, (List.ofFn (Function.update f j v)).prod = A * v * B := by
  induction p with
  | zero => exact j.elim0
  | succ p ih =>
    refine Fin.cases ?_ (fun j' => ?_) j
    · refine ⟨1, (List.ofFn fun i : Fin p => f i.succ).prod, fun v => ?_⟩
      simp [List.ofFn_succ, Function.update_apply, Fin.succ_ne_zero]
    · obtain ⟨A, B, h⟩ := ih (fun i => f i.succ) j'
      refine ⟨f 0 * A, B, fun v => ?_⟩
      have e1 : (fun i : Fin p => Function.update f j'.succ v i.succ) =
          Function.update (fun i => f i.succ) j' v := by
        funext i
        simp only [Function.update_apply, Fin.succ_inj]
      have e2 : Function.update f j'.succ v 0 = f 0 := by
        simp only [Function.update_apply, (Fin.succ_ne_zero j').symm, if_false]
      rw [List.ofFn_succ, List.prod_cons, e1, e2, h]
      simp only [mul_assoc]

theorem comm_prod_ofFn (y : 𝒰) {p : ℕ} (f : Fin p → 𝒰) :
    y * (List.ofFn f).prod - (List.ofFn f).prod * y =
      ∑ j, (List.ofFn (Function.update f j (y * f j - f j * y))).prod := by
  induction p with
  | zero => simp
  | succ p ih =>
    have h0 : (List.ofFn (Function.update f 0 (y * f 0 - f 0 * y))).prod =
        (y * f 0 - f 0 * y) * (List.ofFn fun i : Fin p => f i.succ).prod := by
      simp [List.ofFn_succ, Function.update_apply, Fin.succ_ne_zero]
    have hs : ∀ j' : Fin p,
        (List.ofFn (Function.update f j'.succ (y * f j'.succ - f j'.succ * y))).prod =
          f 0 * (List.ofFn (Function.update (fun i : Fin p => f i.succ) j'
            (y * f j'.succ - f j'.succ * y))).prod := by
      intro j'
      have e1 : (fun i : Fin p => Function.update f j'.succ (y * f j'.succ - f j'.succ * y) i.succ) =
          Function.update (fun i => f i.succ) j' (y * f j'.succ - f j'.succ * y) := by
        funext i
        simp only [Function.update_apply, Fin.succ_inj]
      have e2 : Function.update f j'.succ (y * f j'.succ - f j'.succ * y) 0 = f 0 := by
        simp only [Function.update_apply, (Fin.succ_ne_zero j').symm, if_false]
      rw [List.ofFn_succ, List.prod_cons, e1, e2]
    have hih := ih (fun i => f i.succ)
    rw [Fin.sum_univ_succ, h0, Finset.sum_congr rfl (fun j' _ => hs j'), ← Finset.mul_sum, ← hih,
      List.ofFn_succ, List.prod_cons]
    noncomm_ring

end SlopeTestRemainingChoices

variable {𝒰 : Type*} [Ring 𝒰] [Algebra ℂ 𝒰] {n : ℕ} (E : Fin n → Fin n → 𝒰)

theorem capEntry_comm (hE : GlRelR E) (a b c d : Fin n) (x : ℂ) :
    E a b * capEntry E x c d - capEntry E x c d * E a b =
      (if b = c then capEntry E x a d else 0) - (if d = a then capEntry E x c b else 0) := by
  have hz : ∀ s : 𝒰, (s = 0 ∨ ∃ z : ℂ, s = algebraMap ℂ 𝒰 z) → E a b * s - s * E a b = 0 := by
    rintro s (rfl | ⟨z, rfl⟩)
    · simp
    · rw [Algebra.commutes, sub_self]
  have key : E a b * capEntry E x c d - capEntry E x c d * E a b =
      (E a b * E c d - E c d * E a b) + (E a b * (if c = d then algebraMap ℂ 𝒰 x else 0) -
        (if c = d then algebraMap ℂ 𝒰 x else 0) * E a b) := by
    unfold capEntry
    noncomm_ring
  have hs : (if c = d then algebraMap ℂ 𝒰 x else 0) = 0 ∨
      ∃ z : ℂ, (if c = d then algebraMap ℂ 𝒰 x else 0) = algebraMap ℂ 𝒰 z := by
    split_ifs
    · exact Or.inr ⟨x, rfl⟩
    · exact Or.inl rfl
  rw [key, hz _ hs, add_zero, hE a b c d]
  unfold capEntry
  split_ifs <;> subst_vars <;> first | rfl | simp_all | abel

private theorem prod_ofFn_update_sub' {p : ℕ} (f : Fin p → 𝒰) (j : Fin p) (u v : 𝒰) :
    (List.ofFn (Function.update f j (u - v))).prod =
      (List.ofFn (Function.update f j u)).prod - (List.ofFn (Function.update f j v)).prod := by
  obtain ⟨A, B, h⟩ := prod_ofFn_update_eq f j
  rw [h, h, h]
  noncomm_ring

private theorem prod_ofFn_update_ite' {p : ℕ} (f : Fin p → 𝒰) (j : Fin p) (P : Prop) [Decidable P]
    (w : 𝒰) :
    (List.ofFn (Function.update f j (if P then w else 0))).prod =
      if P then (List.ofFn (Function.update f j w)).prod else 0 := by
  obtain ⟨A, B, h⟩ := prod_ofFn_update_eq f j
  split_ifs
  · rfl
  · rw [h, mul_zero, zero_mul]

private theorem sum_ite_sum_comm {α β : Type*} [Fintype α] [Fintype β] (P : α → Prop)
    [DecidablePred P] (g : α → β → 𝒰) :
    (∑ t, if P t then ∑ σ, g t σ else 0) = ∑ σ, ∑ t, if P t then g t σ else 0 := by
  symm
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun t _ => ?_
  split_ifs <;> simp

private theorem sum_comp_perm_eq_sum {p : ℕ} (σ : Equiv.Perm (Fin p)) (g : Fin p → 𝒰) :
    ∑ t, g t = ∑ j, g (σ j) :=
  (Equiv.sum_comp σ g).symm

theorem cminor_comm (hE : GlRelR E) (a b : Fin n) {p : ℕ} (R C : Fin p → Fin n) (x : ℂ) :
    E a b * cminor E R C x - cminor E R C x * E a b =
      (∑ t : Fin p, if R t = b then cminor E (Function.update R t a) C x else 0) -
        ∑ t : Fin p, if C t = a then cminor E R (Function.update C t b) x else 0 := by
  unfold cminor
  simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib, mul_smul_comm, smul_mul_assoc,
    ← smul_sub, comm_prod_ofFn, capEntry_comm E hE, prod_ofFn_update_sub', prod_ofFn_update_ite']
  simp only [Finset.smul_sum, smul_sub, Finset.sum_sub_distrib]
  congr 1
  · rw [sum_ite_sum_comm]
    refine Finset.sum_congr rfl fun σ _ => ?_
    conv_rhs => rw [sum_comp_perm_eq_sum σ]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases h : R (σ j) = b
    · rw [if_pos h.symm, if_pos h]
      congr 1
      congr 1
      congr 1
      funext k
      by_cases hk : k = j
      · subst hk
        simp
      · simp [Function.update_apply, hk, σ.injective.ne hk]
    · rw [if_neg (Ne.symm h), if_neg h, smul_zero]
  · rw [sum_ite_sum_comm]
    refine Finset.sum_congr rfl fun σ _ => ?_
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases h : C j = a
    · rw [if_pos h, if_pos h]
      congr 1
      congr 1
      congr 1
      funext k
      by_cases hk : k = j
      · subst hk
        simp
      · simp [Function.update_apply, hk]
    · rw [if_neg h, if_neg h, smul_zero]

end ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
