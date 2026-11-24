module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareNuTwistedTupleRamifiedAtTwistPlace
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.VpBounds
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToricSumEqHeckeLValueMulAuxiliaryFactors
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinPartEqOneOfLevel
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsValCharTwist
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HeckeTateFunctionalEquationCM
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HeckeLPartialContinuationHolds
public import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
public import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Prelude
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas

@[expose] public section

open NumberField IsDedekindDomain
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.square_nu_twisted_tuple_ramified_at_twist_place : ∀ {D : Formalism.BasicNotions.D7} {T : Type} {L : Formalism.IndefR.Links.LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} (G : GlobalTheory.ChiGrid.GridData L sc) {μ₀ : T}, L.Is μ₀ → ∀ (t : T) (i j : Fin D.R.m), ∀ P ∈ GlobalTheory.SqTop.twPl G t, ¬ (GlobalTheory.FunObj.SqNum.nuH G t i j).UnrAt P := by
  first | exact @GlobalTheory.SqTop.nuH_not_unrAt_twPl | exact GlobalTheory.SqTop.nuH_not_unrAt_twPl | (intros; apply GlobalTheory.SqTop.nuH_not_unrAt_twPl <;> assumption)
