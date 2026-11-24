module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.Foundations.GelfA
public import Formalism.RealPlaceAnalysis.StatementB
public import Formalism.GradedWeylDivisibility.StatementA
public import Init.ByCases
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Ext
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.NonUnitalHom
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.BigOperators.Ring.Finset
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
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Notation.Pi.Basic
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.Tactic.LinearCombination.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

noncomputable section

namespace GlobalTheory.Mem.GelfCheck

open MvPolynomial GlobalTheory.Mem.Gelf

open MvPolynomial in
theorem _root_.GlobalTheory.Mem.GelfCheck.rowE_apply (R : Type) [CommRing R] (r n : ℕ) (a b : Fin r)
    (P : MvPolynomial (Fin r × Fin n) R) :
    _root_.GlobalTheory.Mem.Gelf.rowE R r n a b P = ∑ s : Fin n, X (a, s) * pderiv (b, s) P := by
  simp [_root_.GlobalTheory.Mem.Gelf.rowE, LinearMap.sum_apply]

open MvPolynomial in
theorem _root_.GlobalTheory.Mem.GelfCheck.rowE_X (R : Type) [CommRing R] (r n : ℕ) (a b c : Fin r) (t : Fin n) :
    _root_.GlobalTheory.Mem.Gelf.rowE R r n a b (X (c, t)) = if b = c then X (a, t) else 0 := by
  rw [_root_.GlobalTheory.Mem.GelfCheck.rowE_apply]
  simp only [pderiv_X, Pi.single_apply, Prod.ext_iff]
  split_ifs with hbc
  · subst hbc
    simp [Finset.sum_ite_eq']
  · have hcb : ¬c = b := fun h => hbc h.symm
    simp [hcb]

open MvPolynomial in
theorem _root_.GlobalTheory.Mem.GelfCheck.rowE_mul (R : Type) [CommRing R] (r n : ℕ) (a b : Fin r)
    (P Q : MvPolynomial (Fin r × Fin n) R) :
    _root_.GlobalTheory.Mem.Gelf.rowE R r n a b (P * Q) =
      _root_.GlobalTheory.Mem.Gelf.rowE R r n a b P * Q + P * _root_.GlobalTheory.Mem.Gelf.rowE R r n a b Q := by
  simp only [_root_.GlobalTheory.Mem.GelfCheck.rowE_apply, Derivation.leibniz, smul_eq_mul, Finset.sum_mul,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  ring

open MvPolynomial in
theorem _root_.GlobalTheory.Mem.GelfCheck.rowE_C (R : Type) [CommRing R] (r n : ℕ) (a b : Fin r) (x : R) :
    _root_.GlobalTheory.Mem.Gelf.rowE R r n a b (C x) = 0 := by
  simp [_root_.GlobalTheory.Mem.GelfCheck.rowE_apply]

open MvPolynomial in
theorem _root_.GlobalTheory.Mem.GelfCheck.glRel_rowE (R : Type) [CommRing R] (r n : ℕ) :
    _root_.GlobalTheory.Mem.Gelf.GlRel (_root_.GlobalTheory.Mem.Gelf.rowE R r n) := by
  intro a b c d
  set E := _root_.GlobalTheory.Mem.Gelf.rowE R r n with hE
  apply LinearMap.ext
  intro P
  induction P using MvPolynomial.induction_on with
  | C x =>
    simp only [LinearMap.sub_apply, Module.End.mul_apply, hE, _root_.GlobalTheory.Mem.GelfCheck.rowE_C,
      map_zero, sub_zero]
    split_ifs <;> simp [_root_.GlobalTheory.Mem.GelfCheck.rowE_C]
  | add p q hp hq =>
    simp only [LinearMap.sub_apply, Module.End.mul_apply, map_add (f := _)] at hp hq ⊢
    rw [hp, hq]
  | mul_X p v hp =>
    obtain ⟨e, t⟩ := v
    simp only [LinearMap.sub_apply, Module.End.mul_apply] at hp ⊢
    simp only [hE, _root_.GlobalTheory.Mem.GelfCheck.rowE_mul, map_add (f := _), _root_.GlobalTheory.Mem.GelfCheck.rowE_X,
      apply_ite, map_zero] at hp ⊢
    split_ifs at hp ⊢ <;> subst_vars <;>
      simp_all [_root_.GlobalTheory.Mem.GelfCheck.rowE_mul, _root_.GlobalTheory.Mem.GelfCheck.rowE_X] <;>
      linear_combination hp * X _

open MvPolynomial in
private theorem gradedWeyl_gen_coeff_one_and_coeff_zero (R : Type) [CommRing R] (r n : ℕ) (a b : Fin r)
    (P : MvPolynomial (Fin r × Fin n) R) :
    (_root_.Formalism.GradedWeylDivisibility.rowGen R a b P).coeff 1 = ∑ s : Fin n, X (a, s) * pderiv (b, s) P ∧
      (_root_.Formalism.GradedWeylDivisibility.rowGen R a b P).coeff 0 = P := by
  induction P using MvPolynomial.induction_on with
  | C x =>
    simp [_root_.Formalism.GradedWeylDivisibility.rowGen, Polynomial.coeff_C]
  | add p q hp hq =>
    simp only [map_add (f := _), Polynomial.coeff_add, hp.1, hp.2, hq.1, hq.2, Finset.sum_add_distrib,
      mul_add, and_self]
  | mul_X p v hp =>
    obtain ⟨hp1, hp0⟩ := hp
    have hX : _root_.Formalism.GradedWeylDivisibility.rowGen R a b (X v) = Polynomial.C (X v) +
        if v.1 = b then Polynomial.X * Polynomial.C (X (a, v.2)) else 0 := by
      simp [_root_.Formalism.GradedWeylDivisibility.rowGen]
    rw [map_mul, hX]
    obtain ⟨i, t⟩ := v
    simp only [Derivation.leibniz, pderiv_X, smul_eq_mul, mul_add, Finset.sum_add_distrib]
    split_ifs with hib
    · subst hib
      have h1 : (1 : ℕ) = 0 + 1 := rfl
      rw [← mul_assoc]
      simp only [Polynomial.coeff_add, Polynomial.coeff_mul_C]
      rw [h1, Polynomial.coeff_mul_X, ← h1]
      simp only [Polynomial.coeff_mul_X_zero, zero_mul, add_zero, hp0, hp1]
      refine ⟨?_, trivial⟩
      simp only [Pi.single_apply, Prod.mk.injEq, true_and, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_mul]
      rw [add_comm]
      congr 1
      · ring
      · exact Finset.sum_congr rfl fun _ _ => by ring
    · simp [Pi.single_apply, Prod.ext_iff, hib, Polynomial.coeff_mul_C, hp0, hp1, Finset.sum_mul]
      exact Finset.sum_congr rfl fun _ _ => by ring

open MvPolynomial in
theorem _root_.GlobalTheory.Mem.GelfCheck.rowE_eq_rowDiv (R : Type) [CommRing R] (r n : ℕ) (a b : Fin r)
    (P : MvPolynomial (Fin r × Fin n) R) :
    _root_.GlobalTheory.Mem.Gelf.rowE R r n a b P = _root_.Formalism.GradedWeylDivisibility.rowDiv R a b 1 P ∧ _root_.Formalism.GradedWeylDivisibility.rowDiv R a b 0 P = P := by
  obtain ⟨h1, h0⟩ := gradedWeyl_gen_coeff_one_and_coeff_zero R r n a b P
  rw [_root_.GlobalTheory.Mem.GelfCheck.rowE_apply]
  exact ⟨by unfold _root_.Formalism.GradedWeylDivisibility.rowDiv; exact h1.symm, by unfold _root_.Formalism.GradedWeylDivisibility.rowDiv; exact h0⟩


section
variable {A : Type} [Ring A] {N : ℕ} {E : Matrix (Fin N) (Fin N) A}


end

section
variable {R : Type} [CommRing R] {V : Type} [AddCommGroup V] [Module R V] {N : ℕ}
  {E : Matrix (Fin N) (Fin N) (Module.End R V)} {μ : Fin N → R} {v : V}

open MvPolynomial in
variable {R : Type} [CommRing R] {V : Type} [AddCommGroup V] [Module R V] {N : ℕ}
  {E : Matrix (Fin N) (Fin N) (Module.End R V)} {μ : Fin N → R} {v : V} in

end

end GlobalTheory.Mem.GelfCheck
