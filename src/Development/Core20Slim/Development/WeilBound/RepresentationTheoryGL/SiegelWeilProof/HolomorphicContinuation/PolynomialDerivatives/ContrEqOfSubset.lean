module

public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.GaussianMomentRecurrence
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.NullSec
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.FockMono
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.IntegrableMonomial
public import Init.Core
public import Init.Data.Bool
public import Init.Data.Cast
public import Init.Data.Nat.Basic
public import Init.Data.Nat.Lemmas
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MonoidAlgebra.Module
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Algebra.Order.Sub.Basic
public import Mathlib.Algebra.Order.Sub.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Erase
public import Mathlib.Data.Finset.Insert
public import Mathlib.Data.Finset.Lattice.Basic
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Finsupp.Order
public import Mathlib.Data.Finsupp.Single
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Prod.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

noncomputable section

open MvPolynomial

namespace PositivityTheory.Rg.Sw.LC

open PositivityTheory.Rg.Sw

variable {m n : ℕ}

def hC (c : ℝ) (p q : ℕ) : ℂ := if p = q then (p.factorial : ℂ) * (2 * c : ℂ) ^ p else 0

def wC (c : ℝ) (s : Fin m × Fin n × Bool →₀ ℕ) : ℂ := ∏ a, ∏ i, hC c (s (a, i, false)) (s (a, i, true))

theorem hC_comm (c : ℝ) (p q : ℕ) : hC c p q = hC c q p := by
  unfold hC; by_cases h : p = q
  · subst h; rfl
  · rw [if_neg h, if_neg (Ne.symm h)]

theorem hC_rel (c : ℝ) (p q : ℕ) : hC c (p + 1) q = (2 * c : ℂ) * (q : ℂ) * hC c p (q - 1) := by
  rcases q with _ | q
  · simp [hC]
  · simp only [hC, Nat.add_sub_cancel, Nat.add_right_cancel_iff]
    split_ifs with h
    · subst h; rw [Nat.factorial_succ]; push_cast; ring
    · simp

theorem contr_eq (c : ℝ) (p : PX m n) : contr c p = ∑ s ∈ p.support, p.coeff s * wC c s := by
  unfold contr wC
  refine Finset.sum_congr rfl fun s _ => ?_
  have : (∏ a, ∏ i, hC c (s (a, i, false)) (s (a, i, true))) =
      if ∀ a i, s (a, i, false) = s (a, i, true) then
        ∏ a, ∏ i, (((s (a, i, false)).factorial : ℂ) * (2 * c : ℂ) ^ (s (a, i, false))) else 0 := by
    simp only [hC, Finset.prod_ite_zero, Finset.mem_univ, true_implies]
  rw [this]
  split_ifs <;> simp

theorem contr_eq_of_subset (c : ℝ) (p : PX m n) (S : Finset (Fin m × Fin n × Bool →₀ ℕ)) (hS : p.support ⊆ S) :
    contr c p = ∑ s ∈ S, p.coeff s * wC c s := by
  rw [contr_eq]
  refine Finset.sum_subset hS fun s _ hs => ?_
  rw [notMem_support_iff.1 hs, zero_mul]

theorem contr_add (c : ℝ) (p q : PX m n) : contr c (p + q) = contr c p + contr c q := by
  classical
  rw [contr_eq_of_subset c (p + q) (p.support ∪ q.support) support_add,
    contr_eq_of_subset c p (p.support ∪ q.support) Finset.subset_union_left,
    contr_eq_of_subset c q (p.support ∪ q.support) Finset.subset_union_right, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [MvPolynomial.coeff_add, add_mul]

theorem contr_monomial (c : ℝ) (s : Fin m × Fin n × Bool →₀ ℕ) (r : ℂ) : contr c (monomial s r) = r * wC c s := by
  classical
  rw [contr_eq_of_subset c _ {s} support_monomial_subset, Finset.sum_singleton, coeff_monomial, if_pos rfl]

theorem contr_C (c : ℝ) (r : ℂ) : contr c (C r : PX m n) = r := by
  rw [← monomial_zero', contr_monomial]
  simp [wC, hC]

theorem wC_split (c : ℝ) (s : Fin m × Fin n × Bool →₀ ℕ) (a : Fin m) (i : Fin n) :
    wC c s = hC c (s (a, i, false)) (s (a, i, true)) *
      ∏ x ∈ Finset.univ.erase (a, i), hC c (s (x.1, x.2, false)) (s (x.1, x.2, true)) := by
  unfold wC
  rw [← Fintype.prod_prod_type' (f := fun a i => hC c (s (a, i, false)) (s (a, i, true)))]
  exact (Finset.mul_prod_erase _ (fun x : Fin m × Fin n => hC c (s (x.1, x.2, false)) (s (x.1, x.2, true)))
    (Finset.mem_univ (a, i))).symm

theorem wC_rel (c : ℝ) (u : Fin m × Fin n × Bool →₀ ℕ) (k : Fin m × Fin n × Bool) :
    wC c (Finsupp.single k 1 + u) = (2 * c : ℂ) * (u (flip k) : ℂ) * wC c (u - Finsupp.single (flip k) 1) := by
  obtain ⟨a, i, b⟩ := k
  rw [wC_split c _ a i, wC_split c _ a i]
  have hrest : ∏ x ∈ Finset.univ.erase (a, i), hC c ((Finsupp.single (a, i, b) 1 + u : Fin m × Fin n × Bool →₀ ℕ) (x.1, x.2, false))
        ((Finsupp.single (a, i, b) 1 + u : Fin m × Fin n × Bool →₀ ℕ) (x.1, x.2, true)) =
      ∏ x ∈ Finset.univ.erase (a, i), hC c ((u - Finsupp.single (flip (a, i, b)) 1 : Fin m × Fin n × Bool →₀ ℕ) (x.1, x.2, false))
        ((u - Finsupp.single (flip (a, i, b)) 1 : Fin m × Fin n × Bool →₀ ℕ) (x.1, x.2, true)) := by
    refine Finset.prod_congr rfl fun x hx => ?_
    have hx' := (Finset.mem_erase.1 hx).1
    have key : ∀ b', (Finsupp.single (a, i, b) 1 + u : Fin m × Fin n × Bool →₀ ℕ) (x.1, x.2, b') = (u - Finsupp.single (flip (a, i, b)) 1 : Fin m × Fin n × Bool →₀ ℕ) (x.1, x.2, b') := by
      intro b'
      have h1 : (a, i, b) ≠ (x.1, x.2, b') := fun h => hx' (by
        have := congrArg (fun y : Fin m × Fin n × Bool => (y.1, y.2.1)) h; simp at this; exact this.symm)
      have h2 : flip (a, i, b) ≠ (x.1, x.2, b') := fun h => hx' (by
        have := congrArg (fun y : Fin m × Fin n × Bool => (y.1, y.2.1)) h; simp [flip] at this; exact this.symm)
      simp only [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.coe_add, Pi.add_apply, Finsupp.single_apply,
        if_neg h1, if_neg h2, tsub_zero, zero_add]
    rw [key false, key true]
  rw [hrest, ← mul_assoc]
  congr 1
  have e1 : (a, i, true) ≠ (a, i, false) := by simp
  cases b
  · simp only [flip, Bool.not_false, Finsupp.coe_tsub, Pi.sub_apply, Finsupp.coe_add, Pi.add_apply,
      Finsupp.single_apply, if_pos, if_neg e1, if_neg e1.symm, tsub_zero, zero_add]
    rw [add_comm]
    exact hC_rel c _ _
  · simp only [flip, Bool.not_true, Finsupp.coe_tsub, Pi.sub_apply, Finsupp.coe_add, Pi.add_apply,
      Finsupp.single_apply, if_pos, if_neg e1, if_neg e1.symm, tsub_zero, zero_add]
    rw [hC_comm c (u (a, i, false)), hC_comm c (u (a, i, false) - 1), add_comm]
    exact hC_rel c _ _

theorem contr_X_mul (c : ℝ) (k : Fin m × Fin n × Bool) (p : PX m n) :
    contr c (X k * p) = (2 * c : ℂ) * contr c (pderiv (flip k) p) := by
  induction p using MvPolynomial.induction_on' with
  | monomial u r =>
    have hX : (X k : PX m n) * monomial u r = monomial (Finsupp.single k 1 + u) r := by
      rw [X, monomial_mul, one_mul]
    rw [hX, pderiv_monomial, contr_monomial, contr_monomial, wC_rel]
    ring
  | add P Q hP hQ => rw [mul_add, contr_add, hP, hQ, map_add (f := _), contr_add, mul_add]

end PositivityTheory.Rg.Sw.LC
