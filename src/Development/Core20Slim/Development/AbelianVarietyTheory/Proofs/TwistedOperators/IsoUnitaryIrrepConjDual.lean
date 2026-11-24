module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NonemptyInvFunEquiv
public import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LFocksLemmas
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.FiniteIntertwining
public import Formalism.GradedWeylDivisibility.StatementA
public import Formalism.LocalRingCardinality.DataCoeff
public import Formalism.RealPlaceAnalysis.FockPairGl
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ProdFactorialSupportSubSingle
public import Init.Core
public import Init.Data.Function
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.NonUnitalHom
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Hom.Basic
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Semigroup
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
public import Mathlib.Algebra.Module.Submodule.LinearMap
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.MvPolynomial.Monad
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Algebra.Star.Unitary
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.Order.Basic
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.RingTheory.Bialgebra.Basic
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic

@[expose] public section

noncomputable section

open MvPolynomial GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries GlobalTheory.OneFunctional Formalism.BasicNotions GlobalTheory.Branching Formalism.GradedWeylDivisibility Formalism.REAL
open scoped TensorProduct DirectSum Matrix

namespace GlobalTheory.ConjDual

theorem map_rowAct {r n : ℕ} (φ : ℂ →+* ℂ) (A : Matrix (Fin r) (Fin r) ℂ) (f : MvPolynomial (Fin r × Fin n) ℂ) :
    map φ (rowAct ℂ A f) = rowAct ℂ (A.map φ) (map φ f) := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [rowAct]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p v hp =>
    simp only [map_mul, hp, map_X]
    congr 1
    simp [rowAct]

def bil (σ : Type) : MvPolynomial σ ℂ →ₗ[ℂ] MvPolynomial σ ℂ →ₗ[ℂ] ℂ :=
  LinearMap.mk₂ ℂ (fun f f' => fockF f (map (starRingEnd ℂ) f'))
    (fun _ _ _ => fischerInner_add_left _ _ _)
    (fun c f f' => by rw [smul_eq_C_mul, LFocks_C_mul_left, smul_eq_mul])
    (fun f a b => by rw [map_add (f := _), fischerInner_add_right])
    (fun c f f' => by
      rw [smul_eq_C_mul, map_mul, map_C, LFocks_C_mul_right, smul_eq_mul]
      simp)

theorem bil_apply {σ : Type} (f f' : MvPolynomial σ ℂ) : bil σ f f' = fockF f (map (starRingEnd ℂ) f') := rfl

theorem bil_rowAct {r n : ℕ} (A : Matrix (Fin r) (Fin r) ℂ) (f f' : MvPolynomial (Fin r × Fin n) ℂ) :
    bil _ (rowAct ℂ A f) f' = bil _ f (rowAct ℂ Aᵀ f') := by
  rw [bil_apply, bil_apply, fockRowAdj, map_rowAct]
  rfl

theorem bil_conj {σ : Type} (f : MvPolynomial σ ℂ) : bil σ f (map (starRingEnd ℂ) f) = fockF f f := by
  rw [bil_apply, map_map]
  have : (starRingEnd ℂ).comp (starRingEnd ℂ) = RingHom.id ℂ := by ext; simp
  rw [this, map_id]

def toDual (n : ℕ) (lam : DomWeight n) : nablaSq ℂ n lam →ₗ[ℂ] Module.Dual ℂ (nablaSq ℂ n lam) :=
  (bil _).compl₁₂ (nablaSq ℂ n lam).subtype (nablaSq ℂ n lam).subtype

theorem toDual_injective (n : ℕ) (lam : DomWeight n) : Function.Injective (toDual n lam) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro f hf
  by_contra h0
  have h1 : f.1 ≠ 0 := fun h => h0 (Subtype.ext h)
  have h2 := LinearMap.congr_fun hf ⟨map (starRingEnd ℂ) f.1, dualWeylMap ℂ ℂ _ n n _ _ f.2⟩
  have h3 : fockF f.1 f.1 = 0 := (bil_conj f.1).symm.trans h2
  have h := fockPos _ f.1 h1
  rw [h3] at h
  simp at h

theorem detPow_conjU (n : ℕ) (g : U n) (c : ℤ) :
    detPow ℂ n (unitaryIncl n (conjU n g)) c = detPow ℂ n (unitaryIncl n g⁻¹) c := by
  unfold detPow
  congr 2
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply, unitaryIncl_coe,
    unitaryIncl_coe, conjU_coe, Matrix.det_transpose]
  rfl

theorem iso_conj_dual : ∀ (n : ℕ) (lam : DomWeight n),
    Iso ((irr n lam).comp (conjU n) : Representation ℂ (U n) (nablaSq ℂ n lam)) (irr n lam).dual := by
  intro n lam
  refine ⟨(toDual n lam).linearEquivOfInjective (toDual_injective n lam) Subspace.dual_finrank_eq.symm,
    fun g x => ?_⟩
  ext y
  change bil _ (sqAct ℂ n lam (unitaryIncl n (conjU n g)) x.1) y.1 =
    bil _ x.1 (sqAct ℂ n lam (unitaryIncl n g⁻¹) y.1)
  unfold sqAct
  rw [map_smul, map_smul, LinearMap.smul_apply, detPow_conjU, bil_rowAct, Matrix.transpose_transpose]
  rfl

end GlobalTheory.ConjDual
