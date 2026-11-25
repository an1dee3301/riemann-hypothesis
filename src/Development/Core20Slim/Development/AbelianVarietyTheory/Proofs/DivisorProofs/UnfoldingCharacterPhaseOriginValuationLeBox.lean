module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.AuxiliaryVectorUniformizerExponent
public import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Definitions.Foundations.SimpleSum
public import Init.Classical
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Fin.Basic
public import Init.Data.Int.Basic
public import Init.Data.Int.DivMod.Basic
public import Init.Data.Int.DivMod.Bootstrap
public import Init.Data.Int.Lemmas
public import Init.Data.Int.Order
public import Init.Data.List.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Nat.Lemmas
public import Init.Data.Zero
public import Init.Omega.Coeffs
public import Init.Omega.Constraint
public import Init.Omega.Int
public import Init.Omega.LinearCombo
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Even
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Nat.Even
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.GroupWithZero.Units.Lemmas
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Order.IsBotOne
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Algebra.Order.SuccPred
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Lattice
public import Mathlib.Order.SuccPred.Nat
public import Mathlib.RingTheory.Valuation.Basic
public import Mathlib.RingTheory.Valuation.ValuativeRel.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

open MeasureTheory ValuativeRel Matrix
open GlobalTheory.OriginBox GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx

namespace GlobalTheory.OriginBox

section Entries
variable {k : Type} [Field k] {n n' : Type} {c : ℕ}

theorem stepPt_var (x₀ : Matrix n n' k) (e : StepVar n c n' → k) {r : n ⊕ Fin c} {s : n' ⊕ Fin (c + 1)}
    (h : Free (c / 2 + 1) (r, s) ∨ Kept (r, s)) (hb : basePt c x₀ r s = 0) : stepPt x₀ e r s = e ⟨(r, s), h⟩ := by
  simp only [stepPt, Matrix.add_apply, Matrix.of_apply, hb, zero_add, dif_pos h]

theorem basePt_inr_succ (x₀ : Matrix n n' k) (i : Fin c) : basePt c x₀ (.inr i) (.inr i.succ) = 0 := by
  simp [basePt]

theorem basePt_inl_inr (x₀ : Matrix n n' k) (r : n) (i : Fin (c + 1)) : basePt c x₀ (.inl r) (.inr i) = 0 := by
  simp [basePt]

theorem basePt_inr_inl (x₀ : Matrix n n' k) (l : Fin c) (s : n') : basePt c x₀ (.inr l) (.inl s) = 0 := by
  simp [basePt]

end Entries

section Main
variable {k : Type} [Field k] [ValuativeRel k]

theorem phase_origin_le (G : Grid k) (ϖ : kˣ) (a a' : ℤ) (e : Vars G) (he : e ∈ box G ϖ a a') :
    valuation k (phase (0 : ColArgs G) e) ≤ valuation k ((ϖ ^ (a + a') : kˣ) : k) := by
  have hbox : ∀ j v {A : ℤ}, boxExp G a a' j v = A → valuation k (e j v) ≤ valuation k ((ϖ ^ A : kˣ) : k) :=
    fun j v A hA => hA ▸ he j (Set.mem_univ j) v (Set.mem_univ v)
  have hmul : ∀ {x y : k} {A B : ℤ}, valuation k x ≤ valuation k ((ϖ ^ A : kˣ) : k) →
      valuation k y ≤ valuation k ((ϖ ^ B : kˣ) : k) → A + B = a + a' →
      valuation k (x * y) ≤ valuation k ((ϖ ^ (a + a') : kˣ) : k) := by
    intro x y A B hx hy hAB
    rw [← hAB, _root_.zpow_add, Units.val_mul, map_mul, map_mul]
    exact mul_le_mul' hx hy
  unfold phase
  refine Valuation.map_sum_le _ fun j _ => Valuation.map_add_le _ ?_ ?_
  · unfold ch
    refine Valuation.map_sum_le _ fun i _ => ?_
    rw [stepPt_var _ _ (Or.inl (by simp [Free])) (basePt_inr_succ _ i)]
    refine hbox _ _ ?_
    simp only [boxExp, auxiliaryVectorUniformizerExponent, Fin.val_succ]
    push_cast
    ring
  · split_ifs with hc
    · refine Valuation.map_sum_le _ fun r _ => ?_
      unfold rowVar
      split_ifs with h
      · rw [Finset.sum_mul]
        refine Valuation.map_sum_le _ fun l _ => ?_
        split_ifs with hl
        · have hc' : Odd (G.m - 2 - (j + 1)) := by
            obtain ⟨q, hq⟩ := hc
            exact ⟨q - 1, by omega⟩
          unfold colVar
          rw [stepPt_var (c := G.m - 2 - (j + 1)) (r := .inr l) (s := .inl r) _ _ (Or.inr ⟨hc', hl⟩) (basePt_inr_inl _ l r),
            stepPt_var (c := G.m - 2 - j) (r := .inl r) (s := .inr ⟨(G.m - 2 - j) / 2, by omega⟩) _ _ (Or.inr ⟨hc, rfl⟩) (basePt_inl_inr _ r _)]
          refine hmul (hbox _ _ rfl) (hbox _ _ rfl) ?_
          obtain ⟨q, hq⟩ := hc
          have h1 : (G.m - 2 - (j + 1) : ℕ) = q + q - 1 := by omega
          have h2 : (l : ℕ) + 1 = q := by omega
          have h3 : (G.m - 2 - j) / 2 = q := by omega
          have h4 : (((q + q - 1 : ℕ)) : ℤ) = 2 * (q : ℤ) - 1 := by omega
          have h5 : ((l : ℕ) : ℤ) = (q : ℤ) - 1 := by omega
          simp only [boxExp, auxiliaryVectorUniformizerExponent]
          rw [h5, h3, hq, h1, h4]
          push_cast
          ring
        · simp
      · simp
    · simp

end Main
end GlobalTheory.OriginBox
