module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottomTriangleConstantAt
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
public import Development.Core20Slim.Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BottomTripleIntegralEqConstMulLocal
public import Development.Core20Slim.Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BottomConstantTransferAlongTower
public import Mathlib
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnitCharTriangle
public import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
public import Development.AbelianVarietyTheory.Definitions.Divisors.InvVolConjLevelOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.LeastSplitAuxiliaryPrimeThetaChainSpec
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.MemHalfCosetSelf
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.BottomExistsIntegrable
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfDefinite
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Basic
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Hom.Instances
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.BotRatio
theorem bottom_theta_constant_ratio_eq : FunPr.ThetaLocalInputs → IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
    (∀ D, NormSum.Inp D) → SqTop.BotSmall → SqTop.LNe →
    SqTop.GBig fun {D} T _ _ G μ₀ _ _ _ => ∀ (W : G.Weil) (S : GridChoice W Set.univ),
      IsStdChar D W.ψ (-1) → NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (t : T) (A A' WW : HSp D)
      (X : Tri T A A' WW) (c0 : T → ℂ), IsBottomTri W i j X → X.IsConst W.ψ W.θ c0 →
      c0 t ≠ 0 ∧ c0 μ₀ ≠ 0 ∧ ∃ γ : D.what₂.LL, D.what₂.embLL γ * c0 μ₀ = c0 t := by
  intro hPr hK hM _ _ hL
  refine gBig_of_two (_root_.GlobalTheory.T.bottom_triple_integral_eq_const_mul_local hPr hK hM hL) (_root_.GlobalTheory.T.witt_tower_bottom_constant_transfer hPr hK hM) fun {D T Lc sc} G μ₀ C x b ha hb => ?_
  intro W S hψ hN i j t A A' WW X c0 hX hc
  obtain ⟨B, B', WW₁, Y, hY, hS⟩ := hN.bottom i j ⟨A, A', WW, X, hX⟩
  have hr := hS.rationalSums (fun t => (hY.integrable t).1) fun t => (hY.integrable t).2
  obtain ⟨u, hu⟩ := hb W S hψ hN i j B B' WW₁ Y A A' WW X c0 hY hX hc
  obtain ⟨lam, hl⟩ := ha W hψ i j B B' WW₁ Y hY
  have hR := ConstRatio.ratIn_of_definite hY.is (ConstRatio.posDef_of_std hY.std)
    (ConstRatio.posDef_of_std hY.std') (ConstRatio.posDef_of_std hY.stdW) hl hr μ₀
  obtain ⟨κ, hκ, e⟩ := hl.eq_mul hu
  have h1 : ConstRatio.RatIn D.what₂.embLL μ₀ fun t => D.what₂.embLL (u t) * c0 t := by
    rw [show (fun t => D.what₂.embLL (u t) * c0 t) = fun t => κ * lam t from funext e]
    exact (ConstRatio.ratIn_const hκ).mul hR
  have h2 : ConstRatio.RatIn D.what₂.embLL μ₀ c0 :=
    ConstRatio.RatIn.of_mul h1 (ConstRatio.ratIn_of_unit fun t => ⟨u t, rfl⟩) fun t => mul_comm _ _
  obtain ⟨h3, y, hy⟩ := h2 t
  refine ⟨h3, (h2 μ₀).1, y, ?_⟩
  rw [hy, div_mul_cancel₀ _ (h2 μ₀).1]
end GlobalTheory.BotRatio
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bottom_constant_ratio_eq_local_factor_ratio : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
    (∀ D, GlobalTheory.NormSum.Inp D) → GlobalTheory.SqTop.BotSmall → GlobalTheory.SqTop.LNe →
    GlobalTheory.SqTop.GBig fun {D} T _ _ G μ₀ _ _ _ => ∀ (W : G.Weil) (S : GridChoice W Set.univ),
      IsStdChar D W.ψ (-1) → NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (t : T) (A A' WW : HSp D)
      (X : Tri T A A' WW) (c0 : T → ℂ), IsBottomTri W i j X → X.IsConst W.ψ W.θ c0 →
      c0 t ≠ 0 ∧ c0 μ₀ ≠ 0 ∧ ∃ γ : D.what₂.LL, D.what₂.embLL γ * c0 μ₀ = c0 t := by
  first | exact @_root_.GlobalTheory.BotRatio.bottom_theta_constant_ratio_eq | exact _root_.GlobalTheory.BotRatio.bottom_theta_constant_ratio_eq | (intros; apply _root_.GlobalTheory.BotRatio.bottom_theta_constant_ratio_eq <;> assumption)
end
