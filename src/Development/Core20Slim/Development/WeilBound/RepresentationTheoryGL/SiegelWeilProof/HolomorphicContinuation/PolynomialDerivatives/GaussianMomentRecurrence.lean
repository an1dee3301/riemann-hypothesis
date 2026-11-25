module

public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.IntegrableMonomial
public import Batteries.Logic
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.NullSec
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.FockMono
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.OneMom
public import Init.Core
public import Init.Data.Bool
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Nat.Lemmas
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MonoidAlgebra.Module
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Derivation
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Notation.Bracket
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Notation.Pi.Basic
public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Algebra.Order.Sub.Basic
public import Mathlib.Algebra.Order.Sub.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Erase
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
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.Order.Basic
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.Derivation.Lie
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.Tactic.FieldSimp.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

noncomputable section

open MvPolynomial MeasureTheory

namespace PositivityTheory.Rg.Sw.LC

open PositivityTheory.Rg.Sw

variable {m n : ℕ}

theorem gaussian_moment_symm (c : ℝ) (p q : ℕ) : g1 c p q = g1 c q p := by
  unfold g1; by_cases h : p = q
  · subst h; rfl
  · rw [if_neg h, if_neg (Ne.symm h)]

theorem gaussian_moment_recurrence (c : ℝ) (hc : 0 < c) (p q : ℕ) : (p : ℂ) * g1 c (p - 1) q = (c : ℂ) * g1 c p (q + 1) := by
  rcases p with _ | p
  · simp [g1]
  · simp only [Nat.add_sub_cancel, g1, Nat.add_right_cancel_iff]
    split_ifs with h
    · subst h
      have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
      push_cast
      rw [Nat.factorial_succ]
      push_cast
      field_simp
      ring
    · simp

theorem phi_split (c : ℝ) (s : Fin m × Fin n × Bool →₀ ℕ) (a : Fin m) (i : Fin n) :
    phi c s = g1 c (s (a, i, false)) (s (a, i, true)) *
      ∏ x ∈ Finset.univ.erase (a, i), g1 c (s (x.1, x.2, false)) (s (x.1, x.2, true)) := by
  unfold phi
  rw [← Fintype.prod_prod_type' (f := fun a i => g1 c (s (a, i, false)) (s (a, i, true)))]
  exact (Finset.mul_prod_erase _ (fun x : Fin m × Fin n => g1 c (s (x.1, x.2, false)) (s (x.1, x.2, true)))
    (Finset.mem_univ (a, i))).symm

theorem rest_congr (c : ℝ) (s s' : Fin m × Fin n × Bool →₀ ℕ) (a : Fin m) (i : Fin n)
    (h : ∀ x : Fin m × Fin n, x ≠ (a, i) → ∀ b, s (x.1, x.2, b) = s' (x.1, x.2, b)) :
    ∏ x ∈ Finset.univ.erase (a, i), g1 c (s (x.1, x.2, false)) (s (x.1, x.2, true)) =
      ∏ x ∈ Finset.univ.erase (a, i), g1 c (s' (x.1, x.2, false)) (s' (x.1, x.2, true)) := by
  refine Finset.prod_congr rfl fun x hx => ?_
  have hx' := (Finset.mem_erase.1 hx).1
  rw [h x hx' false, h x hx' true]

theorem phi_rel (c : ℝ) (hc : 0 < c) (u : Fin m × Fin n × Bool →₀ ℕ) (k : Fin m × Fin n × Bool) :
    (u k : ℂ) * phi c (u - Finsupp.single k 1) = (c : ℂ) * phi c (Finsupp.single (flip k) 1 + u) := by
  obtain ⟨a, i, b⟩ := k
  rw [phi_split c _ a i, phi_split c _ a i,
    rest_congr c (u - Finsupp.single (a, i, b) 1) (Finsupp.single (flip (a, i, b)) 1 + u) a i (fun x hx b' => by
      have h1 : (x.1, x.2, b') ≠ (a, i, b) := fun h => hx (by
        have := congrArg (fun y : Fin m × Fin n × Bool => (y.1, y.2.1)) h; simpa using this)
      have h2 : (x.1, x.2, b') ≠ flip (a, i, b) := fun h => hx (by
        have := congrArg (fun y : Fin m × Fin n × Bool => (y.1, y.2.1)) h; simpa [flip] using this)
      simp only [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.coe_add, Pi.add_apply, Finsupp.single_apply,
        if_neg (Ne.symm h1), if_neg (Ne.symm h2), tsub_zero, zero_add])]
  rw [← mul_assoc, ← mul_assoc]
  congr 1
  cases b
  · have e1 : (a, i, true) ≠ (a, i, false) := by simp
    simp only [flip, Bool.not_false, Finsupp.coe_tsub, Pi.sub_apply, Finsupp.coe_add, Pi.add_apply,
      Finsupp.single_apply, if_pos, if_neg e1, if_neg e1.symm, tsub_zero, zero_add]
    rw [add_comm]
    exact gaussian_moment_recurrence c hc _ _
  · have e1 : (a, i, true) ≠ (a, i, false) := by simp
    simp only [flip, Bool.not_true, Finsupp.coe_tsub, Pi.sub_apply, Finsupp.coe_add, Pi.add_apply,
      Finsupp.single_apply, if_pos, if_neg e1, if_neg e1.symm, tsub_zero, zero_add]
    rw [gaussian_moment_symm c _ (u (a, i, true) - 1), gaussian_moment_symm c (1 + u (a, i, false)), add_comm]
    exact gaussian_moment_recurrence c hc _ _

variable (hM : OneMom)


include hM in
theorem mom_pderiv (c : ℝ) (hc : 0 < c) (k : Fin m × Fin n × Bool) (Q : PX m n) :
    mom c (pderiv k Q) = (c : ℂ) * mom c (X (flip k) * Q) := by
  induction Q using MvPolynomial.induction_on' with
  | monomial u r =>
    have hX : (X (flip k) : PX m n) * monomial u r = monomial (Finsupp.single (flip k) 1 + u) r := by
      rw [X, monomial_mul, one_mul]
    rw [pderiv_monomial, hX, mom_monomial hM c hc, mom_monomial hM c hc, mul_assoc, phi_rel c hc u k]
    ring
  | add P Q hP hQ => rw [map_add (f := _), mom_add hM c hc, hP, hQ, mul_add, mom_add hM c hc, mul_add]

theorem pderiv_comm (k j : Fin m × Fin n × Bool) (Q : PX m n) :
    pderiv k (pderiv j Q) = pderiv j (pderiv k Q) := by
  have : ⁅(pderiv k : Derivation ℂ (PX m n) (PX m n)), (pderiv j : Derivation ℂ (PX m n) (PX m n))⁆ = 0 := by
    apply MvPolynomial.derivation_ext
    intro l
    rw [Derivation.commutator_apply, Derivation.zero_apply]
    classical
    rw [pderiv_X, pderiv_X]
    simp only [Pi.single_apply]
    split_ifs <;> simp
  have h := congrArg (fun D : Derivation ℂ (PX m n) (PX m n) => D Q) this
  simp only [Derivation.commutator_apply, Derivation.zero_apply] at h
  exact sub_eq_zero.1 h

theorem cr_apply (c : ℝ) (k : Fin m × Fin n × Bool) (Q : PX m n) :
    cr c k Q = -pderiv k Q + (2 * c : ℂ) • (X (flip k) * Q) := by
  obtain ⟨a, i, b⟩ := k
  cases b <;> simp [cr, flip]

theorem pderiv_cr (c : ℝ) (k j : Fin m × Fin n × Bool) (Q : PX m n) :
    pderiv k (cr c j Q) = cr c j (pderiv k Q) + (if k = flip j then (2 * c : ℂ) else 0) • Q := by
  classical
  rw [cr_apply, cr_apply, map_add (f := _), map_neg, Derivation.map_smul, pderiv_mul, pderiv_X, pderiv_comm k j]
  by_cases h : k = flip j
  · subst h; simp [Pi.single_apply]; ring
  · simp [Pi.single_apply, h, Ne.symm h]

end PositivityTheory.Rg.Sw.LC
