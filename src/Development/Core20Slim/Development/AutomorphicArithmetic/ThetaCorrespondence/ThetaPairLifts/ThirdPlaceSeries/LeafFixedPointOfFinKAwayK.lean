module

public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteAndAwayFormula
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
public import Development.Core20Slim.Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SettingAtPoint
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LeafInfinitePlaceBound
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Realised
public import Development.AbelianVarietyTheory.Definitions.Divisors.SlopeTestRemainingChoicesAlt
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.Divisors.TieTest
public import Development.AbelianVarietyTheory.Definitions.Divisors.TupleReadBaseTupleEqFamily
public import Development.AbelianVarietyTheory.Definitions.Divisors.TwistedPlaceChoiceLiesOverPair
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabelDatum
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.MemHalfCosetSelf
public import Development.Core20Slim.Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
public import Development.Core20Slim.Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
public import Formalism.LocalRingCardinality.DataDIV
public import Formalism.LocalRingCardinality.DataExtra
public import Formalism.LocalRingCardinality.DataGatTies
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataParams₂
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.Divisibility.HeckeRI
public import Formalism.LocalToGlobal.Divisibility.InertRationalAdjoint
public import Formalism.LocalToGlobal.Divisibility.LiftLat
public import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
public import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.FunctionalLowerBoundOfConditionsNumeric
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.LocalToGlobal.IndefiniteReal.PartsOrth
public import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
public import Formalism.LocalToGlobal.ProjectiveLattices.CuspidalL2Subspace
public import Formalism.LocalToGlobal.ProjectiveLattices.FamilyUniformisationBasePointOrthogonalBis
public import Formalism.LocalToGlobal.ProjectiveLattices.PartitionExtendByZeroAntitone
public import Formalism.SharpRestriction.FamCore
public import Formalism.SharpRestriction.GlobalTheoremInputs
public import Formalism.SharpRestriction.GrowthBounds.IsResidueClassZero
public import Formalism.SharpRestriction.ParConsts
public import Formalism.SharpRestriction.ParamsHeightRankConstant
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PushInvertible

@[expose] public section

set_option synthInstance.maxHeartbeats 200000

section
namespace LeafFixedPointPairing
section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open GlobalTheory.BigTop GlobalTheory.BigTop.Fun GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw matLat)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat
open Formalism.IndefR.Datum Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta
namespace GlobalTheory.CompanionTheory.LeafFixedPointPlaceNorm
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7}
variable {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}
theorem fp_tie_alt : _root_.GlobalTheory.BigTop.Fun.SettingAtPoint → FinK → AwayK → _root_.GlobalTheory.BigTop.Fun.LeafFixedPoint @Comparison₂ := by
  intro hS hF hA
  obtain ⟨c1, hF⟩ := hF
  obtain ⟨c2, hA⟩ := hA
  refine ⟨max c1 c2, fun CF hCF => ?_⟩
  obtain ⟨C1, hF⟩ := hF CF ((le_max_left _ _).trans hCF)
  obtain ⟨C2, hA⟩ := hA CF ((le_max_right _ _).trans hCF)
  refine hS.imp fun {eps} Fm _ _ a _ => ⟨max (max C1 C2) (max CF 0), fun C hC => ?_⟩
  obtain ⟨x₁, a⟩ := a
  have hC1 : C1 ≤ C := ((le_max_left _ _).trans (le_max_left _ _)).trans hC
  have hC2 : C2 ≤ C := ((le_max_right _ _).trans (le_max_left _ _)).trans hC
  have hCF' : CF ≤ C := ((le_max_left _ _).trans (le_max_right _ _)).trans hC
  have hC0 : 0 ≤ C := ((le_max_right _ _).trans (le_max_right _ _)).trans hC
  obtain ⟨x₂, hF⟩ := hF eps C hC1
  obtain ⟨x₃, hA⟩ := hA eps C hC2
  refine ⟨max x₁ (max x₂ x₃), fun x hx hle i p hp d hd => ?_⟩
  obtain ⟨-, b, hT⟩ := hd
  have hx₁ : x₁ ≤ x := (le_max_left _ _).trans hle
  have hx₂ : x₂ ≤ (Fm.L x i).sc.x := ((le_max_left _ _).trans ((le_max_right _ _).trans hle)).trans (Fm.L_x x i hx).ge
  have hx₃ : x₃ ≤ (Fm.L x i).sc.x := ((le_max_right _ _).trans ((le_max_right _ _).trans hle)).trans (Fm.L_x x i hx).ge
  have hset := a x hx hx₁ i p hp hT.ok.eser
  exact leaf_at hT hC0 hCF'
    (hF _ (Fm.L x i) (Fm.L_eps x i) hx₂ _ _ _ _ _ _ _ hset b.ch hT.ok.is b.atScale hT.ok.field)
    (hA _ (Fm.L x i) (Fm.L_eps x i) hx₃ _ _ _ _ _ _ _ hset b.ch hT.ok.is b.atScale hT.ok.field)
end GlobalTheory.CompanionTheory.LeafFixedPointPlaceNorm
end
end
end LeafFixedPointPairing
section
open GlobalTheory.BigTop GlobalTheory.BigTop.Fun GlobalTheory.SumSize
theorem _root_.GlobalTheory.Adopt.leafFixedPoint_of_finK_awayK : _root_.GlobalTheory.BigTop.Fun.SettingAtPoint → FinK → AwayK → _root_.GlobalTheory.BigTop.Fun.LeafFixedPoint @Comparison₂ := by
  first | exact @_root_.LeafFixedPointPairing.GlobalTheory.CompanionTheory.LeafFixedPointPlaceNorm.fp_tie_alt | exact _root_.LeafFixedPointPairing.GlobalTheory.CompanionTheory.LeafFixedPointPlaceNorm.fp_tie_alt | (intros; apply _root_.LeafFixedPointPairing.GlobalTheory.CompanionTheory.LeafFixedPointPlaceNorm.fp_tie_alt <;> assumption)
end
end
