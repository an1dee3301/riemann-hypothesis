module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareBottomPairsSmallReferenceTuple
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
public import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.ExistsSmallSpherical
public import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
public import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
public import Development.AbelianVarietyTheory.Definitions.Divisors.LeastSplitAuxiliaryPrimeThetaChainSpec
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Data.Cast
public import Init.Data.Rat.Basic
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.Ideal.Defs

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.IndefR Formalism.IndefR.Links IsDedekindDomain NumberField
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.SqTop GlobalTheory.NormSum Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.squareBottomPairs_small_reference_tuple : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {μ₀ : T}, L.Is μ₀ → ∀ (G : GridData L sc) (δ t0 : ℂ) (Q : ℕ) (P P' : Pair D ⊤ δ t0 Q) (i j : Fin D.R.m) 𝔪, IsBottom G μ₀ i j 𝔪 P P' → P.Small (bigN D) (maxWt D sc.cGap) ∧ P'.Small (bigN D) (maxWt D sc.cGap) := by
  first | exact @GlobalTheory.BotSmall.bottom_small | exact GlobalTheory.BotSmall.bottom_small | (intros; apply GlobalTheory.BotSmall.bottom_small <;> assumption)
