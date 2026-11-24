module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.GlobalTwisting.GoodTopBot
public import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.WeylDualWeylLatticesAgreeOfLowestAlcove
public import Formalism.GradedWeylDivisibility.StatementA
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.NonUnitalHom
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.IsApply
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Submodule.LinearMap
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MonoidAlgebra.Module
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Derivation
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Notation.Pi.Basic
public import Mathlib.Algebra.Order.Antidiag.Prod
public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.IsEmpty.Defs
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Finset.Insert
public import Mathlib.Data.Finset.NatAntidiagonal
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.Logic.Embedding.Basic
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BasicNotions GlobalTheory.Alc

noncomputable section

namespace GlobalTheory.Alc

theorem rowE_apply (R : Type) [CommRing R] (r n : ℕ) (a b : Fin r) (P : MvPolynomial (Fin r × Fin n) R) :
    rowE R r n a b P = ∑ s : Fin n, X (a, s) * pderiv (b, s) P := by
  simp [rowE, LinearMap.sum_apply]

theorem rowE_X (R : Type) [CommRing R] (r n : ℕ) (a b c : Fin r) (t : Fin n) :
    rowE R r n a b (X (c, t)) = if b = c then X (a, t) else 0 := by
  rw [rowE_apply]
  split_ifs with h
  · subst h
    rw [Finset.sum_eq_single t]
    · simp
    · intro s _ hs
      rw [pderiv_X_of_ne (by simp [Ne.symm hs])]; simp
    · simp
  · refine Finset.sum_eq_zero fun s _ => ?_
    rw [pderiv_X_of_ne (by simp [Ne.symm h])]; simp

theorem rowE_mul (R : Type) [CommRing R] (r n : ℕ) (a b : Fin r) (P Q : MvPolynomial (Fin r × Fin n) R) :
    rowE R r n a b (P * Q) = rowE R r n a b P * Q + P * rowE R r n a b Q := by
  simp only [rowE_apply, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp only [Derivation.leibniz, smul_eq_mul]; ring

theorem rowE_C (R : Type) [CommRing R] (r n : ℕ) (a b : Fin r) (x : R) :
    rowE R r n a b (C x) = 0 := by
  simp [rowE_apply]

theorem glRel_rowE (R : Type) [CommRing R] (r n : ℕ) : GlRel (rowE R r n) := by
  intro a b c d
  refine LinearMap.ext fun P => ?_
  induction P using MvPolynomial.induction_on with
  | C x => split_ifs <;> simp [rowE_C]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p v hp =>
    obtain ⟨e, t⟩ := v
    have hX : (rowE R r n a b * rowE R r n c d - rowE R r n c d * rowE R r n a b) (X (e, t)) =
        ((if b = c then rowE R r n a d else 0) - (if d = a then rowE R r n c b else 0)) (X (e, t)) := by
      simp only [LinearMap.sub_apply, Module.End.mul_apply, rowE_X]
      split_ifs <;> simp_all [rowE_X]
    have hL : ∀ P Q, (rowE R r n a b * rowE R r n c d - rowE R r n c d * rowE R r n a b) (P * Q) =
        (rowE R r n a b * rowE R r n c d - rowE R r n c d * rowE R r n a b) P * Q +
          P * (rowE R r n a b * rowE R r n c d - rowE R r n c d * rowE R r n a b) Q := by
      intro P Q
      simp only [LinearMap.sub_apply, Module.End.mul_apply, rowE_mul, map_add (f := _)]; ring
    have hR : ∀ P Q, ((if b = c then rowE R r n a d else 0) - (if d = a then rowE R r n c b else 0)) (P * Q) =
        ((if b = c then rowE R r n a d else 0) - (if d = a then rowE R r n c b else 0)) P * Q +
          P * ((if b = c then rowE R r n a d else 0) - (if d = a then rowE R r n c b else 0)) Q := by
      intro P Q
      split_ifs <;> simp [rowE_mul] <;> ring
    rw [hL, hR, hp, hX]

theorem rowE_eq_rowDiv (R : Type) [CommRing R] (r n : ℕ) (a b : Fin r) (P : MvPolynomial (Fin r × Fin n) R) :
    rowE R r n a b P = rowDiv R a b 1 P ∧ rowDiv R a b 0 P = P := by
  induction P using MvPolynomial.induction_on with
  | C x => simp [rowE_C, rowDiv, rowGen, Polynomial.algebraMap_apply, Polynomial.coeff_C]
  | add p q hp hq =>
    simp only [rowDiv, map_add (f := _), Polynomial.coeff_add] at *
    exact ⟨by rw [hp.1, hq.1], by rw [hp.2, hq.2]⟩
  | mul_X p v hp =>
    obtain ⟨e, t⟩ := v
    simp only [rowDiv, map_mul] at *
    have h0 : (rowGen R a b (X (e, t) : MvPolynomial (Fin r × Fin n) R)).coeff 0 = X (e, t) := by
      simp only [rowGen, aeval_X]; split_ifs <;> simp
    have h1 : (rowGen R a b (X (e, t) : MvPolynomial (Fin r × Fin n) R)).coeff 1 =
        if b = e then X (a, t) else 0 := by
      simp only [rowGen, aeval_X]
      by_cases h : e = b
      · simp [h, Polynomial.coeff_C]
      · simp [h, Ne.symm h, Polynomial.coeff_C]
    refine ⟨?_, by rw [Polynomial.mul_coeff_zero, hp.2, h0]⟩
    rw [rowE_mul, rowE_X, Polynomial.coeff_mul, Finset.Nat.antidiagonal_succ]
    simp [hp.1, hp.2, h0, h1, add_comm]

theorem map_rowE {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (r n : ℕ) (a b : Fin r)
    (f : MvPolynomial (Fin r × Fin n) R) :
    map φ (rowE R r n a b f) = rowE S r n a b (map φ f) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [rowE_apply, map_sum, map_mul, map_X, pderiv_map]

theorem map_rowE_pow {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (r n k : ℕ) (a b : Fin r)
    (f : MvPolynomial (Fin r × Fin n) R) :
    map φ ((rowE R r n ^ k) a b f) = (rowE S r n ^ k) a b (map φ f) := by
  induction k generalizing a b f with
  | zero =>
    simp only [pow_zero, Matrix.one_apply]
    split_ifs <;> simp
  | succ k ih =>
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [pow_succ, Matrix.mul_apply, LinearMap.sum_apply, Module.End.mul_apply, map_sum, ih, map_rowE]

theorem map_gel {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (r n k : ℕ)
    (f : MvPolynomial (Fin r × Fin n) R) :
    map φ (gel R r n k f) = gel S r n k (map φ f) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [gel, Matrix.trace, Matrix.diag, LinearMap.sum_apply, map_sum, map_rowE_pow]

theorem rowOperators_main : ∀ (R : Type) [CommRing R] (r n : ℕ), GlRel (rowE R r n) ∧
    (∀ a b f, rowE R r n a b f = rowDiv R a b 1 f) ∧
    ∀ (S : Type) [CommRing S] (φ : R →+* S) (k : ℕ) (f : MvPolynomial (Fin r × Fin n) R),
      map φ (gel R r n k f) = gel S r n k (map φ f) := by
  intro R _ r n
  exact ⟨glRel_rowE R r n, fun a b f => (rowE_eq_rowDiv R r n a b f).1,
    fun S _ φ k f => map_gel φ r n k f⟩

end GlobalTheory.Alc
