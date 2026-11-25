module

public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaBoundFittedIdentity
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
public import Development.Core20Slim.Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SettingAtPoint
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Realised
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LeafInfinitePlaceBound
public import Development.Core20Slim.Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GBigAtTiedStatement
public import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
public import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
public import Development.AbelianVarietyTheory.Definitions.Divisors.InvVolConjLevelOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.LeastSplitAuxiliaryPrimeThetaChainSpec
public import Development.AbelianVarietyTheory.Definitions.Divisors.SlopeTestRemainingChoicesAlt
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.Divisors.TieTest
public import Development.AbelianVarietyTheory.Definitions.Divisors.TupleReadBaseTupleEqFamily
public import Development.AbelianVarietyTheory.Definitions.Divisors.TwistedPlaceChoiceLiesOverPair
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
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
public import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
public import Formalism.LocalToGlobal.ProjectiveLattices.CuspidalL2Subspace
public import Formalism.LocalToGlobal.ProjectiveLattices.EmbKCoe
public import Formalism.LocalToGlobal.ProjectiveLattices.FamilyUniformisationBasePointOrthogonalBis
public import Formalism.LocalToGlobal.ProjectiveLattices.PartitionExtendByZeroAntitone
public import Formalism.PairingDivisors.StatementH
public import Formalism.PairingDivisors.StatementX
public import Formalism.SharpRestriction.FamCore
public import Formalism.SharpRestriction.GrowthBounds.IsResidueClassZero
public import Formalism.SharpRestriction.ParConsts
public import Formalism.SharpRestriction.ParamsHeightRankConstant
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Int.DivMod.Basic
public import Init.Data.Int.DivMod.Bootstrap
public import Init.Data.Int.Lemmas
public import Init.Data.Int.Order
public import Init.Data.List.Basic
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Omega.Coeffs
public import Init.Omega.Constraint
public import Init.Omega.Int
public import Init.Omega.LinearCombo
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Algebra.Order.ZeroLEOne
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Cast.Order.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.PartialOrder
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PushInvertible

@[expose] public section

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.BigTop GlobalTheory.BigTop.Fun GlobalTheory.SqTop NumberField
namespace GlobalTheory.BigTop.Fun.ThbTie
end GlobalTheory.BigTop.Fun.ThbTie
open GlobalTheory.BigTop.Fun.ThbTie in
theorem GlobalTheory.BigTop.Fun.thb_tie_alt (hS : _root_.GlobalTheory.BigTop.Fun.SettingAtPoint)
    (hd : Closed FamHyp fun Fm _ => _root_.GlobalTheory.BigTop.EventuallyAtPoints Fm fun x _ i _ => |(Fm.L x i).logDerivativeAtOne| ≤ (Fm.L x i).sc.x ^ (Fm.L x i).sc.eps)
    (hT : ThbSt) : _root_.GlobalTheory.BigTop.Fun.LeafThetaBound @Comparison₂ := by
  have hQ := _root_.GlobalTheory.T.forallLeaves_fitted_of_gBig _ hS hd hT
  refine _root_.GlobalTheory.BigTop.Fun.LeafConditions.mono hQ ?_
  intro D L hT' Gi Gl Kc Y cX ex Csz p CF d C CH _ htie
  refine ⟨htie, fun hq => ?_⟩
  obtain ⟨a, ha⟩ := htie.2
  have hsq := ha.sq
  have hin : ∀ (ij : Sq D) (s : ℤ), 1 ≤ s → s ≤ GlobalTheory.FunObj.SqNum.halfRank D ij.1 ij.2 →
      Formalism.PairingDivisionLocalBalance.HtLe (d.gT ij s) 1 (bTH D C p.Z.x p.Z.b) ∧
        ∀ c, d.zTd ij c s ≠ 0 ∧ Formalism.PairingDivisionLocalBalance.HtLe (d.gT ij s) (d.zTd ij c s) (bTH D C p.Z.x p.Z.b) := by
    intro ij s h1 h2
    obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : (0 : ℤ) ≤ s)
    have h1' : 1 ≤ n := by omega
    have h2' : n ≤ GlobalTheory.FunObj.SqNum.halfRank D ij.1 ij.2 := by omega
    exact hq ij.1 ij.2 n h1' h2' _ _ (hsq.inside ij n h1' h2').1
  have hB0 : ∀ ij : Sq D, 0 ≤ bTH D C p.Z.x p.Z.b := by
    intro ij
    have hr : 1 ≤ GlobalTheory.FunObj.SqNum.halfRank D ij.1 ij.2 := by
      have := D.R.m_add_three_le_k
      unfold GlobalTheory.FunObj.SqNum.halfRank GlobalTheory.ChiGrid.rankV
      have hr : D.R.r = D.R.k + D.R.m - 1 := rfl
      omega
    exact htLe_nonneg (hin ij 1 le_rfl (by exact_mod_cast hr)).1
  have hB : d.O.bTH C p.Z.x p.Z.b = bTH D C p.Z.x p.Z.b := rfl
  have hzT : ∀ ij s, d.O.zT ij s = 1 := hsq.base
  refine ⟨fun ij s h1 h2 => ?_, fun ij s => ?_, fun ij c s => ?_⟩
  · have h2' : s ≤ (GlobalTheory.FunObj.SqNum.halfRank D ij.1 ij.2 : ℤ) :=
      h2.trans_eq (congrArg (fun n : ℕ => (n : ℤ)) (sqRank_half (D := D) ij))
    exact ⟨by rw [hzT]; exact one_ne_zero, fun c => ((hin ij s h1 h2').2 c).1⟩
  · rw [hzT, hB]
    by_cases hs : 1 ≤ s ∧ s ≤ GlobalTheory.FunObj.SqNum.halfRank D ij.1 ij.2
    · exact (hin ij s hs.1 hs.2).1
    · have := (hsq.outside ij s hs).2.1
      change Formalism.PairingDivisionLocalBalance.HtLe (d.gT ij s) 1 _
      rw [this]
      exact htLe_one_zero (hB0 ij)
  · rw [hB]
    by_cases hs : 1 ≤ s ∧ s ≤ GlobalTheory.FunObj.SqNum.halfRank D ij.1 ij.2
    · exact ((hin ij s hs.1 hs.2).2 c).2
    · obtain ⟨e1, e2, -⟩ := hsq.outside ij s hs
      change Formalism.PairingDivisionLocalBalance.HtLe (d.gT ij s) (d.zTd ij c s) _
      rw [e1 c, e2]
      exact htLe_one_zero (hB0 ij)
end
end
