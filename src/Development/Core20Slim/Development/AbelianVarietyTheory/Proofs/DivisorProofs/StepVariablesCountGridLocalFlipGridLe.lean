module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
public import Development.Core20Slim.Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumOKEx
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasCompactSupportFlatIntegrand
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneCosetOfIsTensor
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationLeOneOfMem
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteCoefficientBound
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlatIntegrandFlippedTensorLocallyConstantCompact
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralUnfoldingVariablesMemFieldRange
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemVarLat
public import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum
public import Development.AbelianVarietyTheory.Definitions.Divisors.LeastSplitAuxiliaryPrimeThetaChainSpec
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Definitions.Foundations.SimpleSum
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Int.Lemmas
public import Init.Data.Int.Order
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Omega.Coeffs
public import Init.Omega.Constraint
public import Init.Omega.Int
public import Init.Omega.LinearCombo
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Group.Defs
public import Mathlib.Algebra.Order.Group.Int
public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Ring.Int
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Int
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Basic.Finite.Prod
public import Mathlib.Basic.Finite.Sum
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.SetTheory.Cardinal.NatCard
public import Mathlib.Tactic.Linarith.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Tactic.Zify

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RowTest GlobalTheory.SumSize GlobalTheory.RowClaim
open Formalism.DivisionValues (vw lw)
open MeasureTheory ValuativeRel GlobalTheory.UnfoldLoss

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw
  GlobalTheory.FunObj.borelSpaceKw

namespace GlobalTheory.UnfoldLoss

theorem varCount_le_of_rank_le {k : Type*} [Field k] (G : Grid k) (hs : 1 ≤ G.s) (N : ℕ)
    (hN : ∀ j < G.m, G.rank (G.m, j) ≤ N) : varCount G ≤ G.m * N ^ 2 := by
  unfold varCount
  have hterm : ∀ j : Fin (G.m - 1),
      Nat.card (StepVar (Fin (topRank G (j + 1))) (G.m - 2 - j) (Fin (topRank G j))) ≤ N ^ 2 := by
    intro j
    have hj := j.2
    refine (Finite.card_subtype_le _).trans ?_
    rw [Nat.card_prod, Nat.card_sum, Nat.card_sum]
    simp only [Nat.card_eq_fintype_card, Fintype.card_fin]
    have h1 := topRank_add hs (G := G) (j + 1)
    have h2 := topRank_add hs (G := G) j
    have h3 := hN (j + 1) (by omega)
    have h4 := hN j (by omega)
    rw [sq]
    exact Nat.mul_le_mul (by omega) (by omega)
  calc _ ≤ ∑ _j : Fin (G.m - 1), N ^ 2 := Finset.sum_le_sum fun j _ => hterm j
    _ = (G.m - 1) * N ^ 2 := by simp
    _ ≤ G.m * N ^ 2 := Nat.mul_le_mul_right _ (Nat.sub_le _ _)

theorem varCount_locGrid_le : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (t : T) (w : Pl D.host.E),
    varCount (locGrid G t w) ≤ D.R.m * bigN D ^ 2 := by
  intro D T L sc G t w
  refine varCount_le_of_rank_le (locGrid G t w) (show 1 ≤ D.R.r + 6 by omega) _ fun j hj => ?_
  change j < D.R.m at hj
  have h1 := Nat.mul_le_mul_right D.R.t hj.le
  have hr : D.R.r ≤ D.R.k + D.R.m := by
    have : D.R.r = D.R.k + D.R.m - 1 := rfl
    omega
  change D.R.r + j * D.R.t + D.R.m * (D.R.r + 6) ≤ D.R.k + D.R.m * (D.R.t + (D.R.r + 6) + 1)
  nlinarith

end GlobalTheory.UnfoldLoss
