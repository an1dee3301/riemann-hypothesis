module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolEval
public import Init.Core
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.NonUnitalHom
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.BooleanAlgebra
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Insert
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Fintype.Defs
public import Mathlib.LinearAlgebra.Multilinear.Basic
public import Mathlib.LinearAlgebra.PiTensorProduct.Basic
public import Mathlib.Logic.Function.Basic
public import Mathlib.Order.BooleanAlgebra.Defs
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic

@[expose] public section

open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift

namespace GlobalTheory.CCRFock

theorem polMap_tprod_eq_prod_rename_mulX (W Λ : Type) [Fintype W] [DecidableEq W] (q : W → MvPolynomial Λ ℂ) :
    GlobalTheory.CCRFock.polMap W Λ (PiTensorProduct.tprod ℂ q) =
      ∏ v, MvPolynomial.rename (Prod.mk v) (q v) := by
  simp [GlobalTheory.CCRFock.polMap]

theorem polMap_comp_atPl_mulLeft_X : ∀ (W Λ : Type) [Fintype W] [DecidableEq W] (w : W) (l : Λ),
    GlobalTheory.CCRFock.polMap W Λ ∘ₗ GlobalTheory.RealLift.atPl (V := fun _ : W => MvPolynomial Λ ℂ) w
                 (LinearMap.mulLeft ℂ (MvPolynomial.X l)) =
      LinearMap.mulLeft ℂ (MvPolynomial.X (w, l)) ∘ₗ GlobalTheory.CCRFock.polMap W Λ := by
  intro W Λ _ _ w l
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro p
  have h : GlobalTheory.RealLift.atPl (V := fun _ : W => MvPolynomial Λ ℂ) w
        (LinearMap.mulLeft ℂ (MvPolynomial.X l)) (PiTensorProduct.tprod ℂ p) =
      PiTensorProduct.tprod ℂ (Function.update p w (MvPolynomial.X l * p w)) := by
    unfold GlobalTheory.RealLift.atPl
    rw [PiTensorProduct.map_tprod]
    congr 1
    funext v
    by_cases hv : v = w
    · subst hv; simp
    · simp [Function.update_of_ne hv]
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, h, polMap_tprod_eq_prod_rename_mulX,
    LinearMap.mulLeft_apply]
  rw [Fintype.prod_eq_mul_prod_compl w, Fintype.prod_eq_mul_prod_compl w
    (fun v => MvPolynomial.rename (Prod.mk v) (p v)), ← mul_assoc]
  congr 1
  · simp
  · refine Finset.prod_congr rfl fun v hv => ?_
    have hv' : v ≠ w := by simpa using hv
    rw [Function.update_of_ne hv']

end GlobalTheory.CCRFock
