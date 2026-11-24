module

public import Development.Core20Slim.Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SchurOrthogonality.InstMeasurableSpaceMat
public import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LFocksLemmas
public import Formalism.GradedWeylDivisibility.StatementA
public import Formalism.LocalRingCardinality.DataCoeff
public import Formalism.RealPlaceAnalysis.FockPairGl
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Basic
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
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Lattice.Basic
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

noncomputable section

namespace PI.WSF

open Formalism.BasicNotions MvPolynomial

theorem cf_eq_sum_of_subset {σ : Type} (f g : MvPolynomial σ ℂ) (S : Finset (σ →₀ ℕ))
    (hS : f.support ⊆ S) :
    Formalism.REAL.fockF f g =
      ∑ m ∈ S, f.coeff m * star (g.coeff m) * ((∏ k ∈ m.support, (m k).factorial : ℕ) : ℂ) := by
  unfold Formalism.REAL.fockF
  refine Finset.sum_subset hS fun m _ hm => ?_
  rw [MvPolynomial.notMem_support_iff.mp hm, zero_mul, zero_mul]

theorem cf_add_left {σ : Type} [DecidableEq σ] (f f' g : MvPolynomial σ ℂ) :
    Formalism.REAL.fockF (f + f') g = Formalism.REAL.fockF f g + Formalism.REAL.fockF f' g := by
  classical
  rw [cf_eq_sum_of_subset (f + f') g (f.support ∪ f'.support) MvPolynomial.support_add,
    cf_eq_sum_of_subset f g (f.support ∪ f'.support) Finset.subset_union_left,
    cf_eq_sum_of_subset f' g (f.support ∪ f'.support) Finset.subset_union_right, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_add]
  ring

theorem cf_smul_left {σ : Type} (c : ℂ) (f g : MvPolynomial σ ℂ) :
    Formalism.REAL.fockF (c • f) g = c * Formalism.REAL.fockF f g := by
  rw [MvPolynomial.smul_eq_C_mul, Formalism.GradedWeylDivisibility.LFocks_C_mul_left]

theorem cf_F {N : ℕ} (lam : DomWeight N) :
    (Formalism.REAL.fockF (extremal ℂ N lam) (extremal ℂ N lam)).im = 0 ∧
      0 < (Formalism.REAL.fockF (extremal ℂ N lam) (extremal ℂ N lam)).re := by
  have hne : extremal ℂ N lam ≠ 0 := Formalism.GradedWeylDivisibility.hwNe ℂ N N le_rfl lam.natW
  obtain ⟨h1, h2⟩ := Formalism.GradedWeylDivisibility.fockPos _ _ hne
  exact ⟨h2, h1⟩

theorem cf_F_ne {N : ℕ} (lam : DomWeight N) :
    Formalism.REAL.fockF (extremal ℂ N lam) (extremal ℂ N lam) ≠ 0 := by
  intro h0
  have h1 := (cf_F lam).2
  rw [h0, Complex.zero_re] at h1
  exact lt_irrefl _ h1

def Blin {N : ℕ} (lam : DomWeight N) (q : MvPolynomial (Fin N × Fin N) ℂ) :
    MvPolynomial (Fin N × Fin N) ℂ →ₗ[ℂ] ℂ where
  toFun p := normFock lam p q
  map_add' p p' := by
    simp only [normFock]
    rw [cf_add_left, add_div]
  map_smul' c p := by
    simp only [normFock, RingHom.id_apply, smul_eq_mul]
    rw [cf_smul_left, mul_div_assoc]

theorem cf_Blin_apply {N : ℕ} (lam : DomWeight N) (p q : MvPolynomial (Fin N × Fin N) ℂ) :
    Blin lam q p = normFock lam p q := rfl

theorem cf_herm {N : ℕ} (lam : DomWeight N) (p q : MvPolynomial (Fin N × Fin N) ℂ) :
    normFock lam q p = star (normFock lam p q) := by
  unfold normFock
  rw [Formalism.GradedWeylDivisibility.fockHerm, star_div₀]
  congr 1
  have h := (cf_F lam).1
  apply Complex.ext
  · simp
  · simp [h]

theorem normFock_self_ne_zero {N : ℕ} (lam : DomWeight N) (p : MvPolynomial (Fin N × Fin N) ℂ) (hp : p ≠ 0) :
    normFock lam p p ≠ 0 := by
  unfold normFock
  refine div_ne_zero ?_ (cf_F_ne lam)
  intro h0
  have h1 := (Formalism.GradedWeylDivisibility.fockPos _ p hp).1
  rw [h0, Complex.zero_re] at h1
  exact lt_irrefl _ h1

theorem cf_adj {N : ℕ} (lam : DomWeight N) (g : Matrix (Fin N) (Fin N) ℂ)
    (p q : MvPolynomial (Fin N × Fin N) ℂ) :
    normFock lam (Formalism.GradedWeylDivisibility.rowAct ℂ g p) q = normFock lam p (Formalism.GradedWeylDivisibility.rowAct ℂ g.conjTranspose q) := by
  unfold normFock
  rw [Formalism.GradedWeylDivisibility.fockRowAdj]

theorem cf_ee {N : ℕ} (lam : DomWeight N) : normFock lam (extremal ℂ N lam) (extremal ℂ N lam) = 1 := by
  unfold normFock
  exact div_self (cf_F_ne lam)

end PI.WSF
