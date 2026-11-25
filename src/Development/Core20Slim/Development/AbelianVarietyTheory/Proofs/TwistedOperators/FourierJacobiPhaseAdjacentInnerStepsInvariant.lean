module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ValuationGdetKapAt
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteUnfSupportOfNeOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Definitions.Foundations.SimpleSum
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Fin.Lemmas
public import Init.Data.Int.Basic
public import Init.Data.Int.Lemmas
public import Init.Data.Int.Order
public import Init.Data.Nat.Basic
public import Init.Data.Nat.Lemmas
public import Init.Data.Zero
public import Init.Omega.Coeffs
public import Init.Omega.Constraint
public import Init.Omega.Int
public import Init.Omega.LinearCombo
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Even
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Nat.Even
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.RingTheory.Valuation.ValuativeRel.Basic
public import Mathlib.Tactic.LinearCombination.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Defs.Basic

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv
open GlobalTheory.FunObj.FiniteSupport

namespace GlobalTheory.TopLevelInv

theorem phase_eq_of_two_steps : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] {Γ : Grid k} (j : ℕ) (hA : j + 2 < Γ.m) (x x' : ColArgs Γ) (e e' : Vars Γ),
    (∀ i, i ≠ j → i ≠ j + 1 → x' i = x i) → (∀ i : Fin (Γ.m - 1), i.val ≠ j → i.val ≠ j + 1 → e' i = e i) →
    ch (stepPt (x' j) (e' ⟨j, by omega⟩)) + ch (stepPt (x' (j + 1)) (e' ⟨j + 1, by omega⟩)) +
        (if Even (Γ.m - 2 - j) then ∑ r, rowVar x' e' (j + 1) r * colVar x' e' ⟨j, by omega⟩ r else 0) =
      ch (stepPt (x j) (e ⟨j, by omega⟩)) + ch (stepPt (x (j + 1)) (e ⟨j + 1, by omega⟩)) +
        (if Even (Γ.m - 2 - j) then ∑ r, rowVar x e (j + 1) r * colVar x e ⟨j, by omega⟩ r else 0) →
    (Odd (Γ.m - 2 - j) → ∀ s : Fin (topRank Γ j), rowVar x' e' j s = rowVar x e j s) →
    (Odd (Γ.m - 2 - j) → ∀ r : Fin (topRank Γ (j + 1 + 1)), colVar x' e' ⟨j + 1, by omega⟩ r = colVar x e ⟨j + 1, by omega⟩ r) →
    phase x e = phase x' e' := by
  intro k _ _ _ _ _ _ Γ j hA x x' e e' hx he h0 hrow hcol
  have hch : ∀ i : Fin (Γ.m - 1), i.val ≠ j → i.val ≠ j + 1 →
      ch (stepPt (x' i) (e' i)) = ch (stepPt (x i) (e i)) := by
    intro i h1 h2; rw [hx i h1 h2, he i h1 h2]
  have hcv : ∀ i : Fin (Γ.m - 1), i.val ≠ j → i.val ≠ j + 1 → ∀ r, colVar x' e' i r = colVar x e i r := by
    intro i h1 h2 r; simp only [colVar]; rw [hx i h1 h2, he i h1 h2]
  have hrv : ∀ n : ℕ, n ≠ j → n ≠ j + 1 → ∀ s, rowVar x' e' n s = rowVar x e n s := by
    intro n h1 h2 s; unfold rowVar
    split_ifs with h
    · rw [hx n h1 h2, he ⟨n, h⟩ h1 h2]
    · rw [hx n h1 h2]
  have hodd : Even (Γ.m - 2 - (j + 1)) ↔ Odd (Γ.m - 2 - j) := by
    rw [show Γ.m - 2 - j = (Γ.m - 2 - (j + 1)) + 1 by omega, Nat.odd_add_one, Nat.not_odd_iff_even]
  have hP1 : (if Even (Γ.m - 2 - (j + 1)) then ∑ r, rowVar x' e' (j + 1 + 1) r * colVar x' e' ⟨j + 1, by omega⟩ r else 0)
      = (if Even (Γ.m - 2 - (j + 1)) then ∑ r, rowVar x e (j + 1 + 1) r * colVar x e ⟨j + 1, by omega⟩ r else 0) := by
    split_ifs with hE
    · refine Finset.sum_congr rfl fun r _ => ?_
      rw [hrv (j + 1 + 1) (by omega) (by omega), hcol (hodd.1 hE) r]
    · rfl
  unfold phase
  rw [← sub_eq_zero, ← Finset.sum_sub_distrib,
    Fintype.sum_eq_add (⟨j, by omega⟩ : Fin (Γ.m - 1)) ⟨j + 1, by omega⟩ (by simp [Fin.ext_iff]) ?_]
  · have hch1 := h0
    simp only [Fin.val_mk] at hP1 ⊢
    rw [hP1]
    linear_combination -h0
  · rintro ⟨i, hi⟩ ⟨h1, h2⟩
    simp only [ne_eq, Fin.ext_iff, Fin.val_mk] at h1 h2
    rw [sub_eq_zero, hch ⟨i, hi⟩ h1 h2]
    congr 1
    by_cases hij : i + 1 = j
    · subst hij
      split_ifs with hE
      · refine Finset.sum_congr rfl fun r _ => ?_
        rw [hcv ⟨i, hi⟩ h1 h2, hrow ?_ r]
        rw [show Γ.m - 2 - i = (Γ.m - 2 - (i + 1)) + 1 by omega, Nat.even_add_one, Nat.not_even_iff_odd] at hE
        exact hE
      · rfl
    · split_ifs
      · refine Finset.sum_congr rfl fun r _ => ?_
        rw [hcv ⟨i, hi⟩ h1 h2 r, hrv (i + 1) hij (by omega) r]
      · rfl

end GlobalTheory.TopLevelInv
