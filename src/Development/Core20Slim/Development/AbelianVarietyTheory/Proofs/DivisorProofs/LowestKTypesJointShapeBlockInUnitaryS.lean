module

public import Mathlib
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.Foundations.IsFockIPOfFockData
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowestKTypesJointShapeBlockUnitaryStatement
public import Formalism.LocalRingCardinality.DataTheta
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Function
public import Init.Data.Int.Basic
public import Init.Data.Int.Lemmas
public import Init.Data.Int.Order
public import Init.Data.List.Basic
public import Init.Data.List.Perm
public import Init.Data.Rat.Basic
public import Init.Data.Sum.Basic
public import Init.Data.Sum.Lemmas
public import Init.Data.Zero
public import Init.Omega.Coeffs
public import Init.Omega.Constraint
public import Init.Omega.Int
public import Init.Omega.LinearCombo
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Order.Ring.Unbundled.Rat
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Filter
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Rat.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Logic.Equiv.Sum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial

namespace GlobalTheory.TypesMirror

theorem sameBlock_swap {p q : ℕ} (a b : Ix p q) :
    sameBlock (p := q) (q := p) a.swap b.swap ↔ sameBlock a b := by
  cases a <;> cases b <;> simp [sameBlock]

theorem card_filter_swap {p q : ℕ} (P : Ix p q → Prop) (Q : Ix q p → Prop)
    [DecidablePred P] [DecidablePred Q] (h : ∀ b, P b ↔ Q b.swap) :
    (Finset.univ.filter P).card = (Finset.univ.filter Q).card := by
  refine Finset.card_equiv (Equiv.sumComm (Fin p) (Fin q)) ?_
  intro b
  simpa using h b

theorem blattner_swap {p q : ℕ} (lam : Ix q p → ℚ) (a : Ix p q) :
    blattner (fun b : Ix p q => lam b.swap) a = blattner lam a.swap := by
  unfold blattner rhoNC
  rw [card_filter_swap (fun b : Ix p q => ¬ sameBlock a b ∧ lam b.swap < lam a.swap)
      (fun b : Ix q p => ¬ sameBlock a.swap b ∧ lam b < lam a.swap)
      (fun b => by rw [sameBlock_swap]),
    card_filter_swap (fun b : Ix p q => ¬ sameBlock a b ∧ lam a.swap < lam b.swap)
      (fun b : Ix q p => ¬ sameBlock a.swap b ∧ lam a.swap < lam b)
      (fun b => by rw [sameBlock_swap]),
    card_filter_swap (fun b : Ix p q => sameBlock a b ∧ lam b.swap < lam a.swap)
      (fun b : Ix q p => sameBlock a.swap b ∧ lam b < lam a.swap)
      (fun b => by rw [sameBlock_swap]),
    card_filter_swap (fun b : Ix p q => sameBlock a b ∧ lam a.swap < lam b.swap)
      (fun b : Ix q p => sameBlock a.swap b ∧ lam a.swap < lam b)
      (fun b => by rw [sameBlock_swap])]

theorem shiftNu_swap {p q : ℕ} (r s : ℕ) (lam : Ix q p → ℚ) (a : Ix p q) :
    shiftNu (cPair r s) (blattner (fun b : Ix p q => lam b.swap)) a =
      shiftNu (cPair s r) (blattner lam) a.swap := by
  cases a <;> simp only [shiftNu, blattner_swap, Sum.swap_inl, Sum.swap_inr, cPair] <;> ring

theorem ofBlocks_swap {p q : ℕ} (l₁ l₂ : List ℚ) :
    (ofBlocks l₁ l₂ : Ix p q → ℚ) = fun b => (ofBlocks l₂ l₁ : Ix q p → ℚ) b.swap := by
  funext b; cases b <;> rfl

theorem isParam_swap {p q : ℕ} (lam : Ix q p → ℚ) (h : IsParam lam) :
    IsParam (fun b : Ix p q => lam b.swap) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨h1.comp (Equiv.sumComm (Fin p) (Fin q)).injective, ?_, fun a => h3 _, fun a b => h4 _ _⟩
  intro a b hab
  apply h2
  cases a <;> cases b <;> simpa [posC] using hab

theorem jointShape_swap {p q r s : ℕ} (lam : Ix q p → ℚ) (lam' : Ix s r → ℚ)
    (h : JointShape q p s r (blattner lam) (blattner lam')) :
    JointShape p q r s (blattner fun b => lam b.swap) (blattner fun b => lam' b.swap) := by
  obtain ⟨a, b, c, d, ha, hc, hb, hd, pa, pb, pc, pd, l1, l2, l3, l4, e1, e2⟩ := h
  refine ⟨c, d, a, b, hc, ha, hd, hb, pc, pd, pa, pb, l2, l1, l4, l3, ?_, ?_⟩
  · funext x
    rw [shiftNu_swap, e1, ofBlocks_swap]
    simp
  · funext x
    rw [shiftNu_swap, e2, ofBlocks_swap]
    simp

theorem hypA_swap {t : ℕ} {al be ga de : List ℚ} (h : HypA t al be ga de) :
    HypA t ga de al be := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
  have hp : (ga ++ de ++ al ++ be).Perm (al ++ be ++ ga ++ de) := by
    rw [List.append_assoc (ga ++ de), List.append_assoc (al ++ be)]
    exact List.perm_append_comm
  refine ⟨h1, by omega, h5, h6, h3, h4, hp.nodup_iff.mpr h7,
    fun e he => h8 e (List.perm_append_comm.mem_iff.mp he),
    fun e he => h9 e (List.perm_append_comm.mem_iff.mp he),
    fun e he => h10 e (hp.mem_iff.mp he), fun e he => h11 e (hp.mem_iff.mp he)⟩

theorem types_mirror : ∀ (t : ℕ) (al be ga de : List ℚ), HypA t al be ga de → JointShape _ _ _ _ (blattner (lamA al be ga de)) (blattner (lamM' t al be ga de)) ∧ IsParam (lamM' t al be ga de) ∧ (∀ a, (0 < lamA al be ga de a → 0 ≤ shiftNu (cPair (al.length + de.length) (ga.length + be.length + t)) (blattner (lamA al be ga de)) a) ∧ (lamA al be ga de a < 0 → shiftNu (cPair (al.length + de.length) (ga.length + be.length + t)) (blattner (lamA al be ga de)) a ≤ 0)) ∧ (∀ c, ((t : ℚ) / 2 < lamM' t al be ga de c → 0 ≤ shiftNu (cPair (al.length + be.length) (ga.length + de.length)) (blattner (lamM' t al be ga de)) c) ∧ (lamM' t al be ga de c ≤ (t : ℚ) / 2 → shiftNu (cPair (al.length + be.length) (ga.length + de.length)) (blattner (lamM' t al be ga de)) c ≤ 0)) := by
  intro t al be ga de h
  obtain ⟨k1, -, k3, k4, k5⟩ := GlobalTheory.T.lowest_kTypes_jointShape_block_unitary t ga de al be (hypA_swap h)
  have e1 : lamA al be ga de = fun b => lamA ga de al be b.swap := ofBlocks_swap _ _
  have e2 : lamM' t al be ga de = fun b => lamA' t ga de al be b.swap := ofBlocks_swap _ _
  rw [e1, e2]
  refine ⟨jointShape_swap _ _ k1, isParam_swap _ k3, fun a => ?_, fun c => ?_⟩
  · rw [shiftNu_swap]; exact k4 a.swap
  · rw [shiftNu_swap]; exact k5 c.swap

end GlobalTheory.TypesMirror
