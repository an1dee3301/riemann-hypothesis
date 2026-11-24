module

public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhitKA
public import Development.Core20Slim.Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.WhitNDgOfLocalOfSteps
public import Development.Core20Slim.Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.CoefDataExists
public import Development.Core20Slim.Development.WeilBound.CoreStatements.PublishedTheorems.SiegelWeilSchrodinger.SiegelWeilUnitarySchrodingerLit
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IwasawaDecompositionUnitary
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelParabolicUnnMatrixBlockUpperTriangular
public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EisensteinIsotropicLine
public import Development.AbelianVarietyTheory.Definitions.Foundations.AnalyticOnNhdTsumNpow
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianMeasureConjugationStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsAUNeZero
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaCoefficientOfConvergence
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinRationalPoints
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HolomorphicContinuationValueNnrealPowFactor
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsIwasawaOfIsCompact
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralCompChar
public import Development.Core20Slim.Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.BigCellDefs
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Order.IsBotOne
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Instances.Matrix

@[expose] public section

noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.IwaRedHand

open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

theorem mod_of_cg : ∀ (D : D7) (n : ℕ) (lam : Measure (PositivityTheory.GramSchwartzFunctions.BC.hermA D n)), lam.IsAddHaarMeasure → ∀ (a : GL (Fin n) (AE D)) (f : Mx D n n → ℂ), ∫ b, f b.1 ∂lam = ((GlobalTheory.Doubling.absA D (Matrix.GeneralLinearGroup.det a) : ℝ) : ℂ) ^ n * ∫ c, f (a.1 * c.1 * GlobalTheory.MixModel.adj a.1) ∂lam := by
  intro D n lam hlam a f
  have h := GlobalTheory.T.hermitian_measure_conjugation D n lam hlam a (fun c => f c.1)
  have hr0 : 0 < absA D (Matrix.GeneralLinearGroup.det a) :=
    pos_iff_ne_zero.2 (GlobalTheory.ResAniso.ResProp.absAU_ne_zero _)
  have e : ∫ c, f (a.1 * c.1 * adj a.1) ∂lam =
      npow (absA D (Matrix.GeneralLinearGroup.det a)) (-(n : ℂ)) * ∫ b, f b.1 ∂lam := h
  have key : ((absA D (Matrix.GeneralLinearGroup.det a) : ℝ) : ℂ) ^ n *
      npow (absA D (Matrix.GeneralLinearGroup.det a)) (-(n : ℂ)) = 1 := by
    have hne : ((absA D (Matrix.GeneralLinearGroup.det a) : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast hr0.ne'
    unfold npow
    rw [← Complex.cpow_natCast, ← Complex.cpow_add _ _ hne]
    simp
  rw [e, ← mul_assoc, key, one_mul]

end GlobalTheory.CompanionTheory.IwaRedHand
