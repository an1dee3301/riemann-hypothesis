module

public import Mathlib
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.CycSec
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.NullSec
public import Init.Core
public import Init.Data.Bool
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Int.Lemmas
public import Init.Data.Int.Order
public import Init.Data.List.Basic
public import Init.Data.List.Lemmas
public import Init.Data.Nat.Basic
public import Init.Data.Order.Lemmas
public import Init.Data.Zero
public import Init.Omega.Coeffs
public import Init.Omega.Constraint
public import Init.Omega.Int
public import Init.Omega.LinearCombo
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.IsApply
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Subsemigroup.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Submodule.Basic
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MonoidAlgebra.Module
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Notation.Pi.Basic
public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Logic.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Filter
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.Logic.Function.Defs
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.RelClasses
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

noncomputable section

open MeasureTheory Matrix Set Filter Topology MvPolynomial
open scoped NNReal

namespace PositivityTheory.Rg.Sw.AbsSt.CycP

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt

variable {m n : ℕ}

def gen (ε : Fin m → Bool) (k : Bool × Fin n × Fin n) : PX m n := Qb ε k.1 k.2.1 k.2.2

def Mon (ε : Fin m → Bool) (d : ℕ) : Submodule ℂ (PX m n) :=
  Submodule.span ℂ {M | ∃ l : List (Bool × Fin n × Fin n), l.length ≤ d ∧ M = (l.map (gen ε)).prod}

theorem mon_mono (ε : Fin m → Bool) {d d' : ℕ} (h : d ≤ d') : Mon (n := n) ε d ≤ Mon ε d' :=
  Submodule.span_mono fun _ ⟨l, hl, e⟩ => ⟨l, hl.trans h, e⟩

theorem gen_mul_mon (ε : Fin m → Bool) (d : ℕ) (k : Bool × Fin n × Fin n) {M : PX m n} (hM : M ∈ Mon ε d) :
    gen ε k * M ∈ Mon ε (d + 1) := by
  induction hM using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨l, hl, rfl⟩ := hx
    exact Submodule.subset_span ⟨k :: l, by simp; omega, by simp⟩
  | zero => simp
  | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
  | smul a x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ hx

theorem mon_mul (ε : Fin m → Bool) {d d' : ℕ} {a b : PX m n} (ha : a ∈ Mon ε d) (hb : b ∈ Mon ε d') :
    a * b ∈ Mon ε (d + d') := by
  induction ha using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨l, hl, rfl⟩ := hx
    induction hb using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨l', hl', rfl⟩ := hy
      exact Submodule.subset_span ⟨l ++ l', by simp; omega, by simp⟩
    | zero => simp
    | add u v _ _ hu hv => rw [mul_add]; exact add_mem hu hv
    | smul c u _ hu => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ hu
  | zero => simp
  | add u v _ _ hu hv => rw [add_mul]; exact add_mem hu hv
  | smul c u _ hu => rw [smul_mul_assoc]; exact Submodule.smul_mem _ _ hu

theorem adjoin_le (ε : Fin m → Bool) {R : PX m n}
    (hR : R ∈ Algebra.adjoin ℂ (Set.range fun k : Bool × Fin n × Fin n => (Qb ε k.1 k.2.1 k.2.2 : PX m n))) :
    ∃ d, R ∈ Mon ε d := by
  induction hR using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨k, rfl⟩ := hx
    exact ⟨1, Submodule.subset_span ⟨[k], by simp, by simp [gen]⟩⟩
  | algebraMap r =>
    refine ⟨0, ?_⟩
    rw [Algebra.algebraMap_eq_smul_one]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨[], by simp, by simp⟩)
  | add x y _ _ hx hy =>
    obtain ⟨d, hd⟩ := hx
    obtain ⟨d', hd'⟩ := hy
    exact ⟨max d d', add_mem (mon_mono ε (le_max_left _ _) hd) (mon_mono ε (le_max_right _ _) hd')⟩
  | mul x y _ _ hx hy =>
    obtain ⟨d, hd⟩ := hx
    obtain ⟨d', hd'⟩ := hy
    exact ⟨d + d', mon_mul ε hd hd'⟩


def eulD (H : Matrix (Fin n) (Fin n) ℂ) : Derivation ℂ (PX m n) (PX m n) :=
  ∑ a : Fin m, ∑ j : Fin n, ((∑ i, X (a, i, false) * C (H i j)) • pderiv (a, j, false) +
    (∑ i, X (a, i, true) * C (star (H i j))) • pderiv (a, j, true))

theorem eulH_eq (H : Matrix (Fin n) (Fin n) ℂ) (R : PX m n) : eulH H R = eulD H R := by
  simp [eulH, eulD, smul_eq_mul]

theorem eulD_X_false (H : Matrix (Fin n) (Fin n) ℂ) (a : Fin m) (j : Fin n) :
    eulD H (X (a, j, false) : PX m n) = ∑ i, X (a, i, false) * C (H i j) := by
  simp [eulD, pderiv_X, Pi.single_apply, ite_and, Finset.sum_ite_eq]

theorem eulD_X_true (H : Matrix (Fin n) (Fin n) ℂ) (a : Fin m) (j : Fin n) :
    eulD H (X (a, j, true) : PX m n) = ∑ i, X (a, i, true) * C (star (H i j)) := by
  simp [eulD, pderiv_X, Pi.single_apply, ite_and, Finset.sum_ite_eq]

theorem eulH_gen (ε : Fin m → Bool) (H : Matrix (Fin n) (Fin n) ℂ) (k : Bool × Fin n × Fin n) :
    eulH H (gen ε k) ∈ Mon ε 1 := by
  have : eulH H (gen ε k) = ∑ l, C (H l k.2.2) * gen ε (k.1, k.2.1, l) + ∑ l, C (star (H l k.2.1)) * gen ε (k.1, l, k.2.2) := by
    obtain ⟨b, i, j⟩ := k
    rw [eulH_eq]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [gen, Qb, map_sum, Derivation.leibniz, smul_eq_mul, eulD_X_false, eulD_X_true, Finset.mul_sum]
    rw [Finset.sum_add_distrib]
    congr 1
    · rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun a _ => by ring
    · rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun a _ => by ring
  rw [this]
  refine add_mem (Submodule.sum_mem _ fun l _ => ?_) (Submodule.sum_mem _ fun l _ => ?_)
  · rw [← smul_eq_C_mul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨[(k.1, k.2.1, l)], by simp, by simp⟩)
  · rw [← smul_eq_C_mul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨[(k.1, l, k.2.2)], by simp, by simp⟩)

theorem eulH_mon (ε : Fin m → Bool) (H : Matrix (Fin n) (Fin n) ℂ) (d : ℕ) {M : PX m n} (hM : M ∈ Mon ε d) :
    eulH H M ∈ Mon ε d := by
  rw [eulH_eq]
  induction hM using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨l, hl, rfl⟩ := hx
    induction l generalizing d with
    | nil => simp
    | cons k l ih =>
      simp only [List.map_cons, List.prod_cons, Derivation.leibniz, smul_eq_mul]
      simp only [List.length_cons] at hl
      have hd : l.length + 1 ≤ d := hl
      refine add_mem ?_ ?_
      · exact mon_mono ε hd (gen_mul_mon ε l.length k (ih l.length le_rfl))
      · have h1 := eulH_gen ε H k
        rw [eulH_eq] at h1
        have h2 : (l.map (gen ε)).prod ∈ Mon ε l.length := Submodule.subset_span ⟨l, le_rfl, rfl⟩
        rw [mul_comm ((l.map (gen ε)).prod)]
        exact mon_mono ε (by omega) (mon_mul ε h1 h2)
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul a x _ hx => rw [(eulD H).map_smul]; exact Submodule.smul_mem _ _ hx

end PositivityTheory.Rg.Sw.AbsSt.CycP
