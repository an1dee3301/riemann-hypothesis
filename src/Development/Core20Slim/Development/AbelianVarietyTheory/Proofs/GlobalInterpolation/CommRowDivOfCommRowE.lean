module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.GlobalTwisting.GoodTopBot
public import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.WeylDualWeylLatticesAgreeOfLowestAlcove
public import Development.Core20Slim.Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.CapelliOps
public import Formalism.GradedWeylDivisibility.StatementA
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Nat.Basic
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Rat
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
public import Mathlib.Algebra.Module.Torsion.Free
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MonoidAlgebra.Module
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Algebra.Order.Ring.Rat
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Ring.Unbundled.Rat
public import Mathlib.Algebra.Order.Star.Rat
public import Mathlib.Algebra.Order.ZeroLEOne
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Algebra.Star.Rat
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Cast.Order.Basic
public import Mathlib.Data.Rat.Defs
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.RingTheory.TotallySplit
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.Positivity.Core

@[expose] public section

open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BasicNotions GlobalTheory.Alc

namespace GlobalTheory.Alc

theorem pol_eq_rowE_apply (R : Type) [CommRing R] (r n : ℕ) (a b : Fin r) (g : MvPolynomial (Fin r × Fin n) R) :
    PI.WGL.pol R a b g = rowE R r n a b g := by
  rw [PI.WGL.pol_apply]
  simp [rowE, LinearMap.sum_apply]

theorem rowDiv_succ_smul {r n : ℕ} (a b : Fin r) (k : ℕ) (g : MvPolynomial (Fin r × Fin n) ℚ) :
    ((k : ℚ) + 1) • rowDiv ℚ a b (k + 1) g =
      rowDiv ℚ a b k (rowE ℚ r n a b g) - (if a = b then (k : ℚ) • rowDiv ℚ a b k g else 0) := by
  have h := PI.WGL.rowDiv_succ ℚ a b k g
  rw [pol_eq_rowE_apply] at h
  rw [← h]
  split_ifs <;> simp [Algebra.smul_def, mul_comm]

theorem comm_rowDiv_of_comm_rowE : ∀ (r n : ℕ) (T : Module.End ℚ (MvPolynomial (Fin r × Fin n) ℚ)),
    (∀ a b, T * rowE ℚ r n a b = rowE ℚ r n a b * T) →
      ∀ a b k f, T (rowDiv ℚ a b k f) = rowDiv ℚ a b k (T f) := by
  intro r n T hT a b k
  have hE : ∀ g, T (rowE ℚ r n a b g) = rowE ℚ r n a b (T g) := fun g => by
    have := LinearMap.congr_fun (hT a b) g
    simpa only [Module.End.mul_apply] using this
  induction k with
  | zero => intro f; rw [PI.WGL.rowDiv_zero, PI.WGL.rowDiv_zero]
  | succ k ih =>
    intro f
    have hne : ((k : ℚ) + 1) ≠ 0 := by positivity
    apply smul_right_injective _ hne
    simp only
    rw [← map_smul, rowDiv_succ_smul, rowDiv_succ_smul, map_sub, ih, hE]
    split_ifs
    · rw [map_smul, ih]
    · rw [map_zero]

end GlobalTheory.Alc
