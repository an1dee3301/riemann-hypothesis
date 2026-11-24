module

public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.ContractionFirstOperatorAdjoint
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.NullSec
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.CoreSt
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.FockMono
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.PartialDerivZeroSecondFamily
public import Init.ByCases
public import Init.Core
public import Init.Data.Bool
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Nat.Lemmas
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.GroupWithZero.Action
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.BigOperators
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MonoidAlgebra.Module
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Algebra.Order.Monoid.Canonical.Defs
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Sub.Unbundled.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finsupp.Basic
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Finsupp.Order
public import Mathlib.Data.Finsupp.Single
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Logic.Function.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Preorder.Finsupp
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

noncomputable section

open MvPolynomial Finsupp

namespace PositivityTheory.Rg.Sw.LC

namespace CoreC

open PositivityTheory.Rg.Sw G

variable {m n : ℕ}

theorem dop_split (ε : Fin m → Bool) (c : ℝ) (a b : Fin m) {f g : PX m n} (hf : f ∈ F1 ε) (hg : g ∈ F2 ε) :
    Dop ε c a b (f * g) = D1 ε c a b f * g + f * D2 ε c a b g := by
  have hL : ∀ k, pderiv k (f * g) = f * pderiv k g + g * pderiv k f := fun k => by
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
  have hL2 : ∀ k (p q : PX m n), pderiv k (p * q) = p * pderiv k q + q * pderiv k p := fun k p q => by
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
  unfold Dop D1 D2
  by_cases hab : ε a = ε b
  · rw [if_pos hab, if_pos hab, if_pos hab]
    cases ha : ε a
    · have hb : ε b = false := by rw [← hab, ha]
      simp only [Bool.false_eq_true, if_false]
      simp only [Finset.sum_mul, Finset.mul_sum, neg_mul, mul_neg, ← Finset.sum_neg_distrib,
        ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hL, hL, partial_deriv_zero_second_family ε (k := (a, i, true)) (by simp [inF1, ha]) hg,
        partial_deriv_zero_first_family ε (k := (b, i, false)) (by simp [inF1, hb]) hf]
      ring
    · have hb : ε b = true := by rw [← hab, ha]
      simp only [if_true]
      simp only [Finset.sum_mul, Finset.mul_sum, neg_mul, mul_neg, ← Finset.sum_neg_distrib,
        ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hL, hL, partial_deriv_zero_first_family ε (k := (a, i, true)) (by simp [inF1, ha]) hf,
        partial_deriv_zero_second_family ε (k := (b, i, false)) (by simp [inF1, hb]) hg]
      ring
  · rw [if_neg hab, if_neg hab, if_neg hab]
    cases ha : ε a
    · have hb : ε b = true := by cases h' : ε b <;> simp_all
      simp only [Bool.false_eq_true, if_false]
      simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm, Finset.smul_sum, neg_mul, mul_neg,
        neg_smul, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hL, map_add (f := _), hL2 _ f, hL2 _ g, partial_deriv_zero_second_family ε (k := (a, i, true)) (by simp [inF1, ha]) hg,
        partial_deriv_zero_second_family ε (k := (b, i, false)) (by simp [inF1, hb]) hg]
      simp only [mul_zero, zero_add, add_zero, zero_mul, map_zero, smul_eq_C_mul]
      ring
    · have hb : ε b = false := by cases h' : ε b <;> simp_all
      simp only [if_true]
      simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm, Finset.smul_sum, neg_mul, mul_neg,
        neg_smul, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hL, partial_deriv_zero_first_family ε (k := (a, i, true)) (by simp [inF1, ha]) hf, mul_zero, add_zero, hL2 _ f,
        partial_deriv_zero_first_family ε (k := (b, i, false)) (by simp [inF1, hb]) hf, mul_zero, add_zero]
      simp only [smul_eq_C_mul]
      ring

theorem X_pderiv_mono (k : Fin m × Fin n × Bool) (v : Fin m × Fin n × Bool →₀ ℕ) :
    (X k * pderiv k (monomial v (1 : ℂ)) : PX m n) = ((v k : ℕ) : ℂ) • monomial v 1 := by
  rw [pderiv_monomial, X, monomial_mul, one_mul, one_mul]
  by_cases h0 : v k = 0
  · simp [h0]
  · rw [add_tsub_cancel_of_le (Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr h0)), smul_monomial, smul_eq_mul,
      mul_one]

theorem centre (ε : Fin m → Bool) (c : ℝ) (Λ : PX m n →ₗ[ℂ] ℂ) (hΛ : ∀ a b p, Λ (Dop ε c a b p) = 0)
    {s u : Fin m × Fin n × Bool →₀ ℕ} (hs : ∀ k ∈ s.support, inF1 ε k) (hu : ∀ k ∈ u.support, ¬ inF1 ε k)
    (hr : rdeg ε s ≠ rdeg ε (u.mapDomain pE)) : Λ (monomial s 1 * monomial u 1) = 0 := by
  have hs0 : ∀ k, ¬ inF1 ε k → s k = 0 := fun k hk => by
    by_contra h; exact hk (hs k (Finsupp.mem_support_iff.mpr h))
  have hu0 : ∀ k, inF1 ε k → u k = 0 := fun k hk => by
    by_contra h; exact hu k (Finsupp.mem_support_iff.mpr h) hk
  obtain ⟨a, ha⟩ := Function.ne_iff.mp hr
  rw [monomial_mul, one_mul]
  have hD : Dop ε c a a (monomial (s + u) (1 : ℂ)) =
      ((∑ i, ((s + u) (a, i, true) : ℂ)) - ∑ i, ((s + u) (a, i, false) : ℂ)) • monomial (s + u) 1 := by
    unfold Dop
    rw [if_pos rfl]
    simp only [X_pderiv_mono, ← Finset.sum_sub_distrib, Finset.sum_smul, sub_smul]
  have h0 := hΛ a a (monomial (s + u) 1)
  rw [hD, map_smul, smul_eq_mul] at h0
  refine (mul_eq_zero.mp h0).resolve_left ?_
  have hm (k : Fin m × Fin n × Bool) : (u.mapDomain pE) k = u (pE.symm k) :=
    Finsupp.mapDomain_equiv_apply u k
  simp only [rdeg] at ha
  simp only [hm] at ha
  simp only [pE_symm, pE_apply, Bool.not_not] at ha
  rw [← ne_eq, sub_ne_zero]
  simp only [Finsupp.add_apply, Nat.cast_add, Finset.sum_add_distrib]
  cases hεa : ε a
  · have e1 : ∀ i, u (a, i, true) = 0 := fun i => hu0 _ (by simp [inF1, hεa])
    have e2 : ∀ i, s (a, i, false) = 0 := fun i => hs0 _ (by simp [inF1, hεa])
    simp only [e1, e2, Nat.cast_zero, Finset.sum_const_zero, add_zero, zero_add]
    rw [hεa] at ha
    simp only [Bool.not_false] at ha
    intro h; apply ha; exact_mod_cast h
  · have e1 : ∀ i, u (a, i, false) = 0 := fun i => hu0 _ (by simp [inF1, hεa])
    have e2 : ∀ i, s (a, i, true) = 0 := fun i => hs0 _ (by simp [inF1, hεa])
    simp only [e1, e2, Nat.cast_zero, Finset.sum_const_zero, add_zero, zero_add]
    rw [hεa] at ha
    simp only [Bool.not_true] at ha
    intro h; apply ha; exact_mod_cast h.symm

end CoreC

end PositivityTheory.Rg.Sw.LC
