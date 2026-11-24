module

public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.GlobalTwisting.GoodTopBot
public import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.WeylDualWeylLatticesAgreeOfLowestAlcove
public import Init.ByCases
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.NeZero
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result

@[expose] public section

namespace GlobalTheory.CommutatorPowerEntry

open Finset

theorem comm_pow_entry (A : Type) [Ring A] (N : ℕ) (E : Matrix (Fin N) (Fin N) A)
    (h : GlobalTheory.Alc.GlRel E) (k : ℕ) :
    ∀ (a b c d : Fin N), E a b * (E ^ k) c d - (E ^ k) c d * E a b =
      (if b = c then (E ^ k) a d else (0 : A)) - if d = a then (E ^ k) c b else (0 : A) := by
  induction k with
  | zero =>
    intro a b c d
    simp only [pow_zero, Matrix.one_apply]
    by_cases hcd : c = d <;> by_cases hbc : b = c <;> by_cases hda : d = a <;>
      simp_all [eq_comm]
  | succ k ih =>
    intro a b c d
    have h' : ∀ c d : Fin N, E a b * E c d - E c d * E a b =
        (if b = c then E a d else 0) - (if d = a then E c b else 0) := h a b
    have key : ∀ x y : A, E a b * (x * y) - (x * y) * E a b =
        (E a b * x - x * E a b) * y + x * (E a b * y - y * E a b) := by
      intro x y; noncomm_ring
    simp only [pow_succ, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib, key, ih, h']
    simp only [sub_mul, mul_sub, ite_mul, mul_ite, zero_mul, mul_zero, Finset.sum_add_distrib,
      Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    by_cases hbc : b = c <;> by_cases hda : d = a <;> simp only [hbc, hda, if_true, if_false,
      Finset.sum_const_zero] <;> abel

theorem comm_trace_pow (A : Type) [Ring A] (N : ℕ) (E : Matrix (Fin N) (Fin N) A)
    (h : GlobalTheory.Alc.GlRel E) (k : ℕ) (a b : Fin N) :
    E a b * Matrix.trace (E ^ k) = Matrix.trace (E ^ k) * E a b := by
  rw [← sub_eq_zero]
  simp only [Matrix.trace, Matrix.diag, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib,
    comm_pow_entry A N E h k]
  simp [Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq']

theorem main : ∀ (A : Type) [inst : Ring A] (N : ℕ) (E : Matrix (Fin N) (Fin N) A), GlobalTheory.Alc.GlRel E → ∀ (k : ℕ), (∀ (a b c d : Fin N), E a b * (E ^ k) c d - (E ^ k) c d * E a b = (if b = c then (E ^ k) a d else (0 : A)) - if d = a then (E ^ k) c b else (0 : A)) ∧ ∀ (a b : Fin N), E a b * Matrix.trace (E ^ k) = Matrix.trace (E ^ k) * E a b := by
  intro A _ N E h k
  exact ⟨comm_pow_entry A N E h k, comm_trace_pow A N E h k⟩

end GlobalTheory.CommutatorPowerEntry
