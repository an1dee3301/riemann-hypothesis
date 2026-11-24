module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAlgebraicNumbersExtensionCurveFieldConjLat
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.EmbLLMem
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairIntAt
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.HighestWeightBelow
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TaylorCoeffConjugateSeriesStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmThetaNormBoundHypothesesSatisfiedStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.FoundationProofs.LatticeUnitNormSqNonneg
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralJAndAlgebraicData
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaVacuaConjugatesCmPoints
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockVacEqJets
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsTwoTorsionCMPointAllConjugates
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Init.Core
public import Init.Data.Rat.Basic
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.CharP.IntermediateField
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.FieldTheory.IntermediateField.Basic

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.SumSize GlobalTheory.KerConjMean
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_algebraicNumbers_extension_curveField_conjLattice : ∀ (D : D7), GlobalTheory.NormSum.Inp D → ∀ (δ t0 : ℂ), Crv D D.host.ccK δ → GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D D.host.ccK δ) t0 →
    ∀ (σ : D.what₂.LL →+* ℂ), ∀ ρ ∈ GlobalTheory.KerConjMean.ext D δ t0 σ, ∃ ρ' : Qbar →ₐ[ℚ] ℂ,
      (∀ x, Formalism.MainNotions.StandardLatticesGL3.cj Qbar ρ' (D.what₂.embLL x) = σ x) ∧
      lamConj Qbar ρ' (lamOf D D.host.ccK δ) = lamConj (GlobalTheory.KerConjMean.fld D δ t0) ρ (GlobalTheory.KerConjMean.lat D δ) := by
  first | exact @GlobalTheory.ConjExtend.exists_extension_conj | exact GlobalTheory.ConjExtend.exists_extension_conj | (intros; apply GlobalTheory.ConjExtend.exists_extension_conj <;> assumption)
