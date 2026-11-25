module

public import Mathlib
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalRingCardinality.DataTheta
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Int.Lemmas
public import Init.Data.Int.Order
public import Init.Data.List.Basic
public import Init.Data.List.BasicAux
public import Init.Data.List.Lemmas
public import Init.Data.List.Range
public import Init.Data.Nat.Basic
public import Init.Data.Nat.Lemmas
public import Init.Data.Rat.Basic
public import Init.Data.Rat.Lemmas
public import Init.Data.Zero
public import Init.GetElem
public import Init.Omega.Coeffs
public import Init.Omega.Constraint
public import Init.Omega.Int
public import Init.Omega.LinearCombo
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.List.Defs
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Order.IsBotOne
public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Empty
public import Mathlib.Data.Finset.Range
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.List.Monad
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Rat.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible

namespace GlobalTheory.CasimirNumber

def sqSum (l : List ℚ) : ℚ := (l.map fun x => x ^ 2).sum

theorem sqSum_append (l₁ l₂ : List ℚ) : sqSum (l₁ ++ l₂) = sqSum l₁ + sqSum l₂ := by
  unfold sqSum
  rw [List.map_append, List.sum_append]

theorem sum_range_getD_sq (l : List ℚ) :
    ∑ i ∈ Finset.range l.length, (l.getD i 0) ^ 2 = sqSum l := by
  induction l with
  | nil => simp [sqSum]
  | cons a l ih =>
    rw [List.length_cons, Finset.sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    rw [ih]
    unfold sqSum
    simp only [List.map_cons, List.sum_cons]
    ring

theorem sum_fin_getD_sq (l : List ℚ) (p : ℕ) (h : l.length = p) :
    ∑ i : Fin p, (l.getD i 0) ^ 2 = sqSum l := by
  subst h
  rw [Fin.sum_univ_eq_sum_range (fun i => (l.getD i 0) ^ 2)]
  exact sum_range_getD_sq l

theorem normSq_ofBlocks {p q : ℕ} (l₁ l₂ : List ℚ) (h₁ : l₁.length = p) (h₂ : l₂.length = q) :
    normSq (ofBlocks (p := p) (q := q) l₁ l₂) = sqSum l₁ + sqSum l₂ := by
  unfold normSq ofBlocks
  rw [Fintype.sum_sum_type]
  simp only
  rw [sum_fin_getD_sq l₁ p h₁, sum_fin_getD_sq l₂ q h₂]

theorem sum_range_sub_sq (c : ℚ) (n : ℕ) :
    ∑ i ∈ Finset.range n, (c - (i : ℚ)) ^ 2 =
      n * c ^ 2 - c * (n * (n - 1)) + (n - 1) * n * (2 * n - 1) / 6 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

theorem rhoSq_eq (n : ℕ) : rhoSq n = (n : ℚ) * ((n : ℚ) ^ 2 - 1) / 12 := by
  unfold rhoSq
  rw [sum_range_sub_sq]
  ring

theorem length_block (t : ℕ) : (Formalism.BasicNotions.TH.block t).length = t := by
  unfold Formalism.BasicNotions.TH.block
  simp

theorem sqSum_map_range (f : ℕ → ℚ) (n : ℕ) :
    sqSum ((List.range n).map f) = ∑ i ∈ Finset.range n, f i ^ 2 := by
  induction n with
  | zero => simp [sqSum]
  | succ n ih =>
    rw [List.range_succ, List.map_append, sqSum_append, ih, Finset.sum_range_succ]
    simp [sqSum]

theorem sqSum_block (t : ℕ) : sqSum (Formalism.BasicNotions.TH.block t) = rhoSq t := by
  have hb : Formalism.BasicNotions.TH.block t = (List.range t).map (fun m : ℕ => ((t : ℚ) - 1) / 2 - m) := by
    have hf : ∀ l : List ℕ, List.flatMap (fun a : ℕ => [(Nat.cast a : ℚ)]) l = List.map (fun a : ℕ => (Nat.cast a : ℚ)) l := by
      intro l
      induction l with
      | nil => rfl
      | cons a l ih => simp [List.flatMap_cons, ih]
    unfold Formalism.BasicNotions.TH.block
    simp only [List.bind_eq_flatMap, List.pure_def]
    rw [hf, List.map_map]
    rfl
  rw [hb, sqSum_map_range]
  unfold rhoSq
  rfl

theorem normSq_lamA (al be ga de : List ℚ) :
    normSq (lamA al be ga de) = sqSum al + sqSum be + sqSum ga + sqSum de := by
  unfold lamA
  rw [normSq_ofBlocks _ _ (by simp) (by simp), sqSum_append, sqSum_append]
  ring

theorem normSq_lamA' (t : ℕ) (al be ga de : List ℚ) :
    normSq (lamA' t al be ga de) = sqSum al + sqSum be + sqSum ga + sqSum de + rhoSq t := by
  unfold lamA'
  rw [normSq_ofBlocks _ _ (by simp [length_block] <;> omega) (by simp <;> omega)]
  simp only [sqSum_append, sqSum_block]
  ring

theorem normSq_lamM' (t : ℕ) (al be ga de : List ℚ) :
    normSq (lamM' t al be ga de) = sqSum al + sqSum be + sqSum ga + sqSum de + rhoSq t := by
  unfold lamM'
  rw [normSq_ofBlocks _ _ (by simp <;> omega) (by simp [length_block] <;> omega)]
  simp only [sqSum_append, sqSum_block]
  ring

theorem casimir_number_identity : ∀ (t : ℕ) (al be ga de : List ℚ), HypA t al be ga de → normSq (lamA' t al be ga de) - rhoSq (al.length + be.length + ga.length + de.length + t) = normSq (lamA al be ga de) - rhoSq (al.length + be.length + ga.length + de.length) - ((al.length + be.length + ga.length + de.length : ℕ) : ℚ) * ((al.length + be.length + ga.length + de.length + t : ℕ) : ℚ) * (t : ℚ) / 4 ∧ normSq (lamM' t al be ga de) = normSq (lamA' t al be ga de) := by
  intro t al be ga de _
  refine ⟨?_, by rw [normSq_lamM', normSq_lamA']⟩
  rw [normSq_lamA', normSq_lamA, rhoSq_eq, rhoSq_eq, rhoSq_eq]
  push_cast
  ring

end GlobalTheory.CasimirNumber
