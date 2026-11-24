module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NonemptyInvFunEquiv
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.MinorOrderedEntries
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.FiniteIntertwining
public import Formalism.GradedWeylDivisibility.StatementA
public import Formalism.LocalRingCardinality.DataCoeff
public import Init.Core
public import Init.Data.Fin.Basic
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Hom.Instances
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Equiv
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MonoidAlgebra.Module
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.IsEmpty.Defs
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.Order.Basic
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

open MvPolynomial GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries GlobalTheory.OneFunctional Formalism.BasicNotions GlobalTheory.Branching
open scoped TensorProduct DirectSum

namespace GlobalTheory.OneFunctional

private lemma detShift_eq_add_of_weight_shift (n : ℕ) (c : ℤ) (lam lam' : DomWeight n) (h : ∀ i, lam'.w i = lam.w i + c)
    (hn : 0 < n) : lam'.detShift = lam.detShift + c := by
  simp only [DomWeight.detShift, dif_pos hn, h]

private lemma natW_eq_of_weight_shift (n : ℕ) (c : ℤ) (lam lam' : DomWeight n) (h : ∀ i, lam'.w i = lam.w i + c) :
    lam'.natW = lam.natW := by
  funext i
  simp only [DomWeight.natW, detShift_eq_add_of_weight_shift n c lam lam' h (Fin.pos i), h]
  congr 1
  ring

private lemma nablaSq_eq_of_weight_shift (n : ℕ) (c : ℤ) (lam lam' : DomWeight n) (h : ∀ i, lam'.w i = lam.w i + c) :
    nablaSq ℂ n lam' = nablaSq ℂ n lam := by
  simp only [nablaSq, natW_eq_of_weight_shift n c lam lam' h]

private lemma detPow_detShift_of_weight_shift (n : ℕ) (c : ℤ) (lam lam' : DomWeight n) (h : ∀ i, lam'.w i = lam.w i + c) (g : U n) :
    detPow ℂ n (unitaryIncl n g) lam'.detShift =
      ((detU n g ^ c : ℂˣ) : ℂ) * detPow ℂ n (unitaryIncl n g) lam.detShift := by
  have hdet : Matrix.GeneralLinearGroup.det (unitaryIncl n g) = detU n g := by
    ext
    simp [detU, unitaryIncl_coe]
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    have h1 : detU 0 g = 1 := by
      ext
      simp [detU]
    simp [h1, DomWeight.detShift, detPow]
  · simp only [detPow, detShift_eq_add_of_weight_shift n c lam lam' h hn, hdet, zpow_add, Units.val_mul]
    ring

theorem iso_twist_det_irr_shift (n : ℕ) (c : ℤ) (lam lam' : DomWeight n) (h : ∀ i, lam'.w i = lam.w i + c) :
    Iso (twist (detU n ^ c) (irr n lam)) (irr n lam') := by
  refine ⟨LinearEquiv.ofEq _ _ (nablaSq_eq_of_weight_shift n c lam lam' h).symm, fun g x => ?_⟩
  apply Subtype.ext
  change ((detU n ^ c) g : ℂ) • (sqRep ℂ n lam (unitaryIncl n g) x : MvPolynomial (Fin n × Fin n) ℂ) =
    (sqRep ℂ n lam' (unitaryIncl n g) (LinearEquiv.ofEq _ _ (nablaSq_eq_of_weight_shift n c lam lam' h).symm x) :
      MvPolynomial (Fin n × Fin n) ℂ)
  have hz : (detU n ^ c) g = detU n g ^ c := rfl
  rw [sqRep_coe, sqRep_coe, hz]
  simp only [sqAct, LinearEquiv.coe_ofEq_apply, detPow_detShift_of_weight_shift n c lam lam' h g, mul_smul]

end GlobalTheory.OneFunctional
