module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
public import Development.Core20Slim.Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.BigThetaKernelIntegrable
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallThetaKernelTranslateIntegrable
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMatchedFlipThetaIntegral
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
public import Development.Core20Slim.Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.SquareConvolutionLargeBound
public import Development.Core20Slim.Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.SmallConvolutionExistsIntegrableTranslates
public import Development.Core20Slim.Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DominantTermNeZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
public import Development.AbelianVarietyTheory.Definitions.Divisors.BplusOfEquivariant
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsNotRelZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.InvVolConjLevelOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataParams₂
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Formalism.LocalToGlobal.Divisibility.LiftLat
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Prod
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Finsupp.SMul
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
noncomputable section
namespace GlobalTheory.ConstNZ
theorem constK_alt : FunPr.ThetaLocalInputs → IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
    SquareSt.WeilConvergence → SquareSt.LocalMatching → SquareSt.ThetaIntegralsAgree → RowClaim.ConstK := by
  intro h1 h2 hLM h3 h4 h5
  obtain ⟨CF0, hH⟩ := ((_root_.GlobalTheory.T.square_convolution_estimate h1 h2 h3 h4 h5).and (_root_.GlobalTheory.T.exists_integrable_translates_small_convolution h1 h2 h3 h4 h5)).and (_root_.GlobalTheory.T.dominant_term_ne_zero h1 h2 hLM h3 h4 h5)
  refine ⟨CF0, fun ε CF hCF => ?_⟩
  obtain ⟨x₀, hx⟩ := hH ε CF hCF
  refine ⟨x₀, fun D large₂ he hx0 Γ _ _ Pl0 T A Ks _ _ _ R F hS ch hch hsc => ?_⟩
  obtain ⟨⟨hb, hs⟩, hn⟩ := hx D large₂ he hx0 Γ Pl0 T A Ks R F hS ch hch hsc
  intro i j t
  obtain ⟨M, hM, a, τ, τ', n, Φ, hnat, hfl, g, g₁, hI⟩ := hn i j t
  obtain ⟨b', hb'⟩ := ch.rm.onto_big i j (toTens a)
  obtain ⟨b, rfl⟩ := toTens_surjective b'
  have hΘ : IsMatched ch.S.B t ch.rm i j (tensT ch.W a τ) (tensT ch.W b τ') := ⟨a, b, τ, τ', n, Φ, hb', hnat, hfl, rfl, rfl⟩
  obtain ⟨z, hz, hzi⟩ := hs i j t M hM _ _ hΘ g g₁
  have hconv : SquareConv ch.W M _ _ z g g₁ := ⟨hb i j t M hM _ _ hΘ g g₁, hzi⟩
  have hc := hch.const i j t M hM _ _ hΘ z g g₁ hconv
  have hL : zdeg z * ∫ u in M.fd _, kerBig ch.W (tensT ch.W a τ) g g₁ u ∂M.ν _ ≠ 0 := mul_ne_zero hz hI
  rw [hc] at hL
  exact ⟨⟨M, hM, _, _, hΘ, z, g, g₁, hconv, right_ne_zero_of_mul hL⟩, left_ne_zero_of_mul hL⟩
end GlobalTheory.ConstNZ
end
end
