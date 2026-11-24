module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixSDblDecZero
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsGLSubmatrix
public import Development.AbelianVarietyTheory.Definitions.Foundations.MemSiegelOfIffRightAct
public import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompProjAnisotropicAnisotropicEmbedding
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Fin.Basic
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Basic
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP
open GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw

namespace GlobalTheory.Core.Rk.SWLaw

theorem aP_levi_mul_nC : ∀ (D : D7) (A : HSp D) (p : siegel A) (a : GL (Fin A.rank) (AE D)) (c : skewA D A.rank), (p : GA D (dblSp A)) = (dblDec A).levi a * (dblDec A).nC c → aP A p = Matrix.GeneralLinearGroup.det a := by
  intro D A p a c hp
  have hM : Formalism.L2.Theta.mt (dblSp A) (p : GA D (dblSp A)) ⬝ (dblDec A).jX = (dblDec A).jX ⬝ a.1 := by
    rw [hp, GlobalTheory.MixModel.mt_mul, Matrix.mul_assoc, HypDec.nC_jX, HypDec.levi_jX]
  apply Units.ext
  rw [GlobalTheory.Doubling.val_aOf]
  show (GlobalTheory.Doubling.leviMat finSumFinEquiv (Formalism.L2.Theta.mt (dblSp A) (p : GA D (dblSp A)))).det = a.1.det
  set M := Formalism.L2.Theta.mt (dblSp A) (p : GA D (dblSp A)) with hMdef
  have key : GlobalTheory.Doubling.leviMat finSumFinEquiv M * rat A.gram⁻¹ = rat A.gram⁻¹ * a.1 := by
    ext i j
    have h := congrFun (congrFun hM (finSumFinEquiv (Sum.inl i))) j
    simp only [HypDec.jX, dblDec, rat, stackRows, Matrix.mul_apply, Matrix.map_apply, Matrix.submatrix_apply,
      Fin.sum_univ_add, finSumFinEquiv_apply_left, finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_natAdd,
      Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr, id] at h
    simp only [GlobalTheory.Doubling.leviMat, rat, Matrix.mul_apply, Matrix.add_apply, Matrix.toBlocks₁₁, Matrix.toBlocks₁₂,
      Matrix.of_apply, Matrix.submatrix_apply, Matrix.map_apply, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right,
      add_mul, Finset.sum_add_distrib]
    exact h
  have hu : IsUnit (rat (D := D) A.gram⁻¹).det := by
    rw [rat, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (Matrix.isUnit_nonsing_inv_det _ (gram_det_ne A).isUnit).map _
  have hd := congrArg Matrix.det key
  rw [Matrix.det_mul, Matrix.det_mul, mul_comm] at hd
  exact hu.mul_left_cancel hd

end GlobalTheory.Core.Rk.SWLaw
