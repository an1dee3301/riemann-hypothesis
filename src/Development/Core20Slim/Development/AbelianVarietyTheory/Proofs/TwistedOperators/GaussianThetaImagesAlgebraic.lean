module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRtensOp
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaTransformGaussianVacuumIsFiniteDatumStatement
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HermitianOrthogonalExtensionData
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlkGLMem
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsReading
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.List.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.LinearMap
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MonoidAlgebra.Module
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.Group.Multiset
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Finsupp.Multiset
public import Mathlib.Data.Finsupp.SMul
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Multiset.Basic
public import Mathlib.Data.Multiset.Defs
public import Mathlib.Data.Multiset.ZeroCons
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import Mathlib.LinearAlgebra.SesquilinearForm.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.ThetaGaussAlg

variable {D : D7}

theorem fockF_one (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (ε : Bool) {M X : HSp D} (A : Fr M) (B : Fr X)
    (f : WO M X → ℂ) : fockF ψ θ ε A B f 1 = f := by
  simp only [fockF, pureTensorO, pureTensorL]
  have h1 : (1 : MvPolynomial (FVar D X.rank M.rank) ℂ) = MvPolynomial.basisMonomials (FVar D X.rank M.rank) ℂ 0 := by
    rw [MvPolynomial.coe_basisMonomials]
    rfl
  rw [h1, Module.Basis.constr_basis]
  simp [opPow]

theorem det_gram_ne_zero (V : HSp D) : V.gram.det ≠ 0 := by
  intro hdet
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet

  have hb : ∀ i, V.hT (V.frame i) (∑ j, v j • V.frame j) = 0 := by
    intro i
    have hi : V.hT (V.frame i) (∑ j, v j • V.frame j) = (V.gram *ᵥ v) i := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_smul, smul_eq_mul, Matrix.mulVec, dotProduct, Formalism.BasicNotions.HSpace.gram]
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    rw [hi, hv]
    rfl
  have hy : (∑ j, v j • V.frame j) = 0 := by
    refine V.nondeg.2 _ fun x => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← V.frame.sum_repr x, map_sum V.hT, LinearMap.sum_apply]
    exact Finset.sum_eq_zero fun i _ => by rw [map_smulₛₗ, LinearMap.smul_apply, hb, smul_zero]
  exact hv0 (funext (Fintype.linearIndependent_iff.mp V.frame.linearIndependent v hy))

theorem incM_gram_inv (S : HSp D) :
    GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM S.gram * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM S.gram⁻¹ = 1 ∧
      GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM S.gram⁻¹ * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM S.gram = 1 := by
  have hu : IsUnit S.gram.det := isUnit_iff_ne_zero.mpr (det_gram_ne_zero S)
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM]
  constructor
  · rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ hu, Matrix.map_one _ (map_zero _) (map_one _)]
  · rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ hu, Matrix.map_one _ (map_zero _) (map_one _)]

def crd (S X : HSp D) {k : ℕ} (e : Fin k ≃ Fin X.rank) : Matrix (Fin S.rank) (Fin k) (AE D) ≃+ WO S X where
  toFun u := (HMul.hMul (uᵀ.submatrix e.symm id) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM S.gram) : Matrix (Fin X.rank) (Fin S.rank) (AE D))
  invFun x := GlobalTheory.TripleRead.ptO S.gram e x
  left_inv u := by
    simp only [GlobalTheory.TripleRead.ptO]
    rw [Matrix.mul_assoc, (incM_gram_inv S).1, Matrix.mul_one]
    ext i j
    simp
  right_inv x := by
    have : (GlobalTheory.TripleRead.ptO S.gram e x)ᵀ.submatrix e.symm id =
        (HMul.hMul x (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM S.gram⁻¹) : Matrix (Fin X.rank) (Fin S.rank) (AE D)) := by
      ext i j
      simp [GlobalTheory.TripleRead.ptO]
    simp only [this]
    rw [Matrix.mul_assoc, (incM_gram_inv S).2, Matrix.mul_one]
  map_add' u v := by
    rw [← Matrix.add_mul]
    rfl

end GlobalTheory.ThetaGaussAlg

end
