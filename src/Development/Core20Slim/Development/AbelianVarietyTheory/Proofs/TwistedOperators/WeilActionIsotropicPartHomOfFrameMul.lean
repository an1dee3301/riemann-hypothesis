module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.PhaseApply
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
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
public import Formalism.SatakeDualWeyl.Statement
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.IsoFrameAct

open scoped GlobalTheory.MixModel

theorem actO_isoPart_of_mul : ∀ (D : D7) (V W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (a : GL (Fin r) (AE D)) (m : GA D V), HMul.hMul (Formalism.L2.Theta.mt V m) (C.map (incA D)) = HMul.hMul (C.map (incA D)) a.val → ∀ (h : GA D W) (z : Mx D W.rank r), actO V W m h (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C z) = GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C (HMul.hMul (HMul.hMul (Formalism.L2.Theta.mt W h) z) (GlobalTheory.MixModel.adj a.val)) := by
  intro D V W r C a m hm h z
  have e : (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.adj D C * V.gram).map (incA D) =
      GlobalTheory.MixModel.adj (C.map (incA D)) * GlobalTheory.MixModel.gA V := by
    change GlobalTheory.MixModel.rat (Cᴴ * V.gram) = _
    exact Matrix.map_mul
  have hg : GlobalTheory.MixModel.gA V * GlobalTheory.MixModel.giA V = 1 := by
    change (V.gram.map (incA D)) * (V.gram⁻¹.map (incA D)) = 1
    rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 (gram_det_ne V))]
    exact Matrix.map_one _ (map_zero (incA D)) (map_one (incA D))
  have hg' : GlobalTheory.MixModel.giA V * GlobalTheory.MixModel.gA V = 1 := by
    change (V.gram⁻¹.map (incA D)) * (V.gram.map (incA D)) = 1
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 (gram_det_ne V))]
    exact Matrix.map_one _ (map_zero (incA D)) (map_one (incA D))
  have adjmul {l n k : ℕ} (x : Mx D l n) (y : Mx D n k) :
      GlobalTheory.MixModel.adj (x * y) = GlobalTheory.MixModel.adj y * GlobalTheory.MixModel.adj x :=
    Formalism.UG.cT_mul (cA D) x y
  have hinv : Formalism.L2.Theta.mt V m⁻¹ = GlobalTheory.MixModel.giA V *
      (GlobalTheory.MixModel.adj (Formalism.L2.Theta.mt V m) * GlobalTheory.MixModel.gA V) := by
    have hh : GlobalTheory.MixModel.giA V * (GlobalTheory.MixModel.adj (Formalism.L2.Theta.mt V m) * GlobalTheory.MixModel.gA V) * Formalism.L2.Theta.mt V m = 1 := by
      have hr : GlobalTheory.MixModel.adj (Formalism.L2.Theta.mt V m) * GlobalTheory.MixModel.gA V * Formalism.L2.Theta.mt V m = GlobalTheory.MixModel.gA V := mt_rel V m
      rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (GlobalTheory.MixModel.adj _), hr, hg']
    rw [← Matrix.one_mul (Formalism.L2.Theta.mt V m⁻¹), ← hh, Matrix.mul_assoc]
    have hm_inv : Formalism.L2.Theta.mt V m * Formalism.L2.Theta.mt V m⁻¹ = 1 := by
      change (m.val * m⁻¹.val).val = 1
      exact congrArg Units.val (mul_inv_cancel m.val)
    rw [hm_inv, Matrix.mul_one]
  have key : GlobalTheory.MixModel.adj (C.map (incA D)) * (GlobalTheory.MixModel.gA V * (GlobalTheory.MixModel.giA V *
      (GlobalTheory.MixModel.adj (Formalism.L2.Theta.mt V m) * GlobalTheory.MixModel.gA V))) =
      GlobalTheory.MixModel.adj a.val * (GlobalTheory.MixModel.adj (C.map (incA D)) * GlobalTheory.MixModel.gA V) := by
    rw [← Matrix.mul_assoc (GlobalTheory.MixModel.gA V), hg, Matrix.one_mul, ← Matrix.mul_assoc, ← adjmul, hm, adjmul,
      Matrix.mul_assoc]
  change Formalism.L2.Theta.mt W h * (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C z) * Formalism.L2.Theta.mt V m⁻¹ = _
  rw [hinv]
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart]
  rw [e]
  simp only [Matrix.mul_assoc]
  rw [key]

end GlobalTheory.IsoFrameAct

end
