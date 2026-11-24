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
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Basic
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Ring.CharZero
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Basic
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Trace.Defs

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.IsoPartPairing

open GlobalTheory.MixModel

theorem hO_isoPart {D : D7} (V W : HSp D) {r : ℕ} (C C' : Matrix (Fin V.rank) (Fin r) D.host.E)
    (hC : GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.adj D C * V.gram * C' = 1) (u y : Mx D W.rank r) :
    hO V W (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C' u) (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C y) =
      (GlobalTheory.MixModel.adj y ⬝ (GlobalTheory.MixModel.gA W ⬝ u)).trace := by
  have hC0 : Cᴴ * V.gram * C' = 1 := hC
  have hC1 : C'ᴴ * V.gram * C = 1 := by
    have h := congrArg Matrix.conjTranspose hC0
    rwa [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      GlobalTheory.MixModel.gram_conjTranspose, Matrix.conjTranspose_one, ← Matrix.mul_assoc] at h
  have hx : GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C' u = u ⬝ rat (C'ᴴ * V.gram) := rfl
  have hz : GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C y = y ⬝ rat (Cᴴ * V.gram) := rfl
  have hg : giA V ⬝ adj (rat (Cᴴ * V.gram)) = rat C := by
    rw [← rat_conjTranspose, Matrix.conjTranspose_mul, GlobalTheory.MixModel.gram_conjTranspose,
      Matrix.conjTranspose_conjTranspose, giA, ← rat_mul, ← Matrix.mul_assoc,
      Matrix.nonsing_inv_mul _ (GlobalTheory.MixModel.gram_isUnit_det V), Matrix.one_mul]
  rw [hx, hz, hO_eq_trace, adj_mul]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (giA V), hg]
  rw [show rat C ⬝ (adj y ⬝ (gA W ⬝ (u ⬝ rat (C'ᴴ * V.gram)))) = (rat C ⬝ adj y ⬝ gA W ⬝ u) ⬝ rat (C'ᴴ * V.gram) by
    simp only [Matrix.mul_assoc]]
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← rat_mul, hC1, rat_one,
    Matrix.one_mul, Matrix.mul_assoc]

theorem trHalf_add_self {D : D7} (z : AE D) :
    trHalf D z + trHalf D z = Algebra.trace (AF D.host.F) (AE D) (incA D D.host.xi0 * z) := by
  show algebraMap D.host.F (AF D.host.F) (1 / 2) * _ + algebraMap D.host.F (AF D.host.F) (1 / 2) * _ = _
  rw [← add_mul, ← map_add (f := _), add_halves, map_one, one_mul]

theorem symplOH_isoPart_add_self : ∀ (D : D7) (V W : HSp D) (r : ℕ) (C C' : Matrix (Fin V.rank) (Fin r) D.host.E), GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.adj D C * V.gram * C' = 1 → ∀ u y : Mx D W.rank r, symplOH V W (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C' u) (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C y) + symplOH V W (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C' u) (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C y) = Algebra.trace (AF D.host.F) (AE D) (incA D D.host.xi0 * (HMul.hMul (GlobalTheory.MixModel.adj y) (HMul.hMul (GlobalTheory.MixModel.gA W) u)).trace) := by
  intro D V W r C C' hC u y
  rw [symplOH_eq, hO_isoPart V W C C' hC u y, trHalf_add_self]

end GlobalTheory.IsoPartPairing
