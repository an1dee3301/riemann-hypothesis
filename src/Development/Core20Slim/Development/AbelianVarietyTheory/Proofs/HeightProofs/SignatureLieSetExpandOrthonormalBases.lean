module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.HeightProofs.InnerDRepSq
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.HeightProofs.OrthonormalBasesMemUnitaryLieAlgebra
public import Batteries.Classes.Order
public import Batteries.Data.List.Basic
public import Batteries.Data.List.Lemmas
public import Batteries.Logic
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.HeightProofs.InvSqrtTwo
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Init.ByCases
public import Init.Classical
public import Init.Core
public import Init.Data.BEq
public import Init.Data.Bool
public import Init.Data.Cast
public import Init.Data.Fin.Lemmas
public import Init.Data.Int.Basic
public import Init.Data.List.Basic
public import Init.Data.List.FinRange
public import Init.Data.List.Lemmas
public import Init.Data.Nat.Basic
public import Init.Data.Ord.Basic
public import Init.Data.Order.Lemmas
public import Init.Data.Order.Ord
public import Init.Data.RArray
public import Init.Data.Zero
public import Init.Grind.Lemmas
public import Init.Grind.Norm
public import Init.Grind.Order
public import Init.Grind.Ring.CommSolver
public import Init.Grind.Ring.Field
public import Init.Prelude
public import Init.PropLemmas
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.Field.Basic
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Opposite
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Opposite
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Opposites
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Ring.CharZero
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.IsEmpty.Defs
public import Mathlib.Basic.Logic.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Bool.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Int.Cast.Lemmas
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Basis
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.NNRat.Defs
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Cast.Order.Ring
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Rat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Fin.Basic
public import Mathlib.Order.Lattice
public import Mathlib.Order.RelClasses
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.FieldSimp.Lemmas
public import Mathlib.Tactic.Linarith.Lemmas
public import Mathlib.Tactic.LinearCombination.Lemmas
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum GlobalTheory.TypeSum.CasBasis GlobalTheory.LowTypeDetermined

noncomputable section
namespace GlobalTheory.TypeSum.CasBasis.Expand
variable {n : ℕ}

theorem sum_get {α M : Type*} [AddCommMonoid M] (l : List α) (f : α → M) :
    ∑ i : Fin l.length, f (l.get i) = (l.map f).sum := by
  rw [Fin.sum_univ_def]
  conv_rhs => rw [← List.map_get_finRange l]
  rw [List.map_map]
  rfl

theorem trace_mul_unitE (U : Mx n) (a b : Fin n) : trace (U * unitE a b) = U b a := by
  simpa [unitE] using (Matrix.trace_mul_single U a b 1)

theorem sum_flatMap {α M : Type*} [AddCommMonoid M] (l : List α) (f : α → List M) :
    (l.flatMap f).sum = (l.map fun a => (f a).sum).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.flatMap_cons, List.sum_append, ih]

theorem filter_split {α M : Type*} [AddCommMonoid M] (l : List α) (c d : α → Bool) (F : α → M) :
    ((l.filter fun p => c p && (d p == true)).map F).sum + ((l.filter fun p => c p && (d p == false)).map F).sum =
      (l.map fun p => if c p then F p else 0).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.filter_cons, List.map_cons, List.sum_cons]
    cases hc : c a <;> cases hd : d a <;> simp [← ih] <;> abel

theorem sum_map_neg' {α M : Type*} [AddCommGroup M] (l : List α) (f : α → M) :
    (l.map fun x => -f x).sum = -(l.map f).sum := by
  induction l with
  | nil => simp
  | cons a l ih => rw [List.map_cons, List.sum_cons, ih, List.map_cons, List.sum_cons, neg_add]

theorem sum_product_list {M : Type*} [AddCommMonoid M] (G : Fin n × Fin n → M) :
    ((List.product (List.finRange n) (List.finRange n)).map G).sum = ∑ a, ∑ b, G (a, b) := by
  simp [List.product, List.map_flatMap, sum_flatMap, List.map_map, Fin.sum_univ_def, Function.comp_def]

variable {ε : Fin n → Bool}

theorem diag_re {U : Mx n} (hU : U ∈ lieSet ε) (a : Fin n) : (U a a).re = 0 := by
  have h := (mem_lieSet_iff_entry.mp hU) a a
  rcases ha : ε a <;> simp [ha] at h <;> have h2 := congrArg Complex.re h <;> simp at h2 <;> linarith

theorem entry_same {U : Mx n} (hU : U ∈ lieSet ε) {a b : Fin n} (h : ε a = ε b) : U b a = -star (U a b) := by
  have h1 := (mem_lieSet_iff_entry.mp hU) a b
  rw [h] at h1
  have : (starRingEnd ℂ) (U b a) = -U a b := by
    rcases hb : ε b <;> simp [hb] at h1 <;> first | linear_combination h1 | linear_combination -h1
  have h3 := congrArg (starRingEnd ℂ) this
  simp at h3
  simpa [Complex.star_def] using h3

theorem entry_opp {U : Mx n} (hU : U ∈ lieSet ε) {a b : Fin n} (h : ε a ≠ ε b) : U b a = star (U a b) := by
  have h1 := (mem_lieSet_iff_entry.mp hU) a b
  have : star (U b a) = U a b := by
    rcases ha : ε a <;> rcases hb : ε b <;> simp_all <;> first | linear_combination h1 | linear_combination -h1
  have h3 := congrArg star this
  simpa using h3

abbrev tm (U X : Mx n) : Mx n := (trace (U * X)).re • X

theorem tm_diag {U : Mx n} (hU : U ∈ lieSet ε) (a : Fin n) :
    tm U (Complex.I • unitE a a) = -(U a a • unitE a a) := by
  have h := diag_re hU a
  simp only [tm, Matrix.mul_smul, trace_smul, trace_mul_unitE, ← Complex.coe_smul, smul_smul, ← neg_smul]
  congr 1
  apply Complex.ext <;> simp [h]

theorem tm_same {U : Mx n} (hU : U ∈ lieSet ε) {a b : Fin n} (h : ε a = ε b) :
    tm U (invSqrtTwo • (unitE a b - unitE b a)) + tm U ((invSqrtTwo * Complex.I) • (unitE a b + unitE b a)) =
      -(U a b • unitE a b + U b a • unitE b a) := by
  have hba := entry_same hU h
  simp only [tm, Matrix.mul_smul, Matrix.mul_sub, Matrix.mul_add, trace_smul, trace_sub, trace_add, trace_mul_unitE,
    ← Complex.coe_smul, hba]
  match_scalars <;> simp only [smul_eq_mul] <;> apply Complex.ext <;>
    simp [invSqrtTwo, Complex.mul_re, Complex.mul_im, Complex.inv_re, Complex.inv_im] <;> field_simp
  all_goals (try rw [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]) <;> ring

theorem tm_opp {U : Mx n} (hU : U ∈ lieSet ε) {a b : Fin n} (h : ε a ≠ ε b) :
    tm U (invSqrtTwo • (unitE a b + unitE b a)) + tm U ((invSqrtTwo * Complex.I) • (unitE a b - unitE b a)) =
      U a b • unitE a b + U b a • unitE b a := by
  have hba := entry_opp hU h
  simp only [tm, Matrix.mul_smul, Matrix.mul_sub, Matrix.mul_add, trace_smul, trace_sub, trace_add, trace_mul_unitE,
    ← Complex.coe_smul, hba]
  match_scalars <;> simp only [smul_eq_mul] <;> apply Complex.ext <;>
    simp [invSqrtTwo, Complex.mul_re, Complex.mul_im, Complex.inv_re, Complex.inv_im] <;> field_simp
  all_goals (try rw [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]) <;> ring

abbrev pairTerm (U : Mx n) (p : Fin n × Fin n) : Mx n := U p.1 p.2 • unitE p.1 p.2 + U p.2 p.1 • unitE p.2 p.1

theorem decomp (U : Mx n) :
    U = ∑ a, U a a • unitE a a + ∑ a, ∑ b, if a < b then pairTerm U (a, b) else 0 := by
  ext r t
  simp only [Matrix.add_apply, Matrix.sum_apply, apply_ite (fun M : Mx n => M r t), pairTerm, Matrix.smul_apply,
    single_apply, smul_eq_mul, Matrix.zero_apply]
  simp [ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq']
  rcases lt_trichotomy r t with h | rfl | h
  · rw [Finset.sum_eq_single r (fun x _ hx => Finset.sum_eq_zero fun y _ => by split_ifs <;> grind) (by simp),
      Finset.sum_eq_single t (fun y _ hy => by split_ifs <;> grind) (by simp)]
    simp [h, h.ne, not_lt.mpr h.le]
  · simp only [lt_self_iff_false, if_true]
    rw [Finset.sum_eq_zero fun x _ => Finset.sum_eq_zero fun y _ => by split_ifs <;> grind]
    simp
  · rw [Finset.sum_eq_single t (fun x _ hx => Finset.sum_eq_zero fun y _ => by split_ifs <;> grind) (by simp),
      Finset.sum_eq_single r (fun y _ hy => by split_ifs <;> grind) (by simp)]
    simp [h, h.ne, h.ne', not_lt.mpr h.le]

theorem pairs_split (U : Mx n) :
    ((pairs ε true).map (pairTerm U)).sum + ((pairs ε false).map (pairTerm U)).sum =
      ∑ a, ∑ b, if a < b then pairTerm U (a, b) else 0 :=
  (filter_split _ (fun p : Fin n × Fin n => decide (p.1 < p.2)) (fun p : Fin n × Fin n => ε p.1 == ε p.2)
    (pairTerm U)).trans (by rw [sum_product_list]; simp)

theorem sum_k {U : Mx n} (hU : U ∈ lieSet ε) :
    ∑ i, tm U (kB ε i) = -(∑ a, U a a • unitE a a + ((pairs ε true).map (pairTerm U)).sum) := by
  rw [show (∑ i, tm U (kB ε i)) = ((kList ε).map (tm U)).sum from sum_get _ _]
  simp only [kList, List.map_append, List.sum_append, List.map_map, List.map_flatMap, sum_flatMap, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil, add_zero, Function.comp_def, tm_diag hU]
  rw [List.map_congr_left (g := fun p => -pairTerm U p) (fun p hp => by
    have hs : ε p.1 = ε p.2 := by
      simp [pairs] at hp
      exact hp.2.2
    exact tm_same hU hs), Fin.sum_univ_def, sum_map_neg', sum_map_neg', neg_add]

theorem sum_p {U : Mx n} (hU : U ∈ lieSet ε) :
    ∑ b, tm U (pB ε b) = ((pairs ε false).map (pairTerm U)).sum := by
  rw [show (∑ b, tm U (pB ε b)) = ((pList ε).map (tm U)).sum from sum_get _ _]
  simp only [pList, List.map_flatMap, sum_flatMap, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  rw [List.map_congr_left (g := pairTerm U) (fun p hp => by
    have hs : ε p.1 ≠ ε p.2 := by
      simp [pairs] at hp
      exact hp.2.2
    exact tm_opp hU hs)]

end GlobalTheory.TypeSum.CasBasis.Expand

namespace GlobalTheory.TypeSum.CasBasis


open Expand in
theorem lieSet_expand_bases : ∀ (n : ℕ) (ε : Fin n → Bool), ∀ U ∈ lieSet ε,
    U = ∑ b, (trace (U * pB ε b)).re • pB ε b - ∑ i, (trace (U * kB ε i)).re • kB ε i := by
  intro n ε U hU
  have h1 := sum_p hU
  have h2 := sum_k hU
  simp only [tm] at h1 h2
  rw [h1, h2, sub_neg_eq_add]
  conv_lhs => rw [decomp U]
  rw [← pairs_split (ε := ε)]
  abel

end GlobalTheory.TypeSum.CasBasis
