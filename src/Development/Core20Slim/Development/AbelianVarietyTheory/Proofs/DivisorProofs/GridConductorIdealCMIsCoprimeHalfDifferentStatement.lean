module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.GridConductorIdealCMIsCoprimeHalfDifferent
public import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrimeDvdAbsNormHalfDifferent
public import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Data.Nat.Coprime
public import Init.Prelude
public import Mathlib.Algebra.Order.Kleene
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Coprime.Basic
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Operations

@[expose] public section

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open GlobalTheory.ChiGrid GlobalTheory.FunObj.SqNum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gridConductorIdealCM_isCoprime_halfDifferent : ∀ {D : D7} {T : Type} {L : LevCh D T} (P : Places L), Nat.Coprime D.host.pde (D.host.QS * D.host.q) → Nat.Coprime D.host.pde' (D.host.QS * D.host.q) → IsCoprime (condE P) D.host.𝔟 := by
  first | exact @GlobalTheory.FunObj.StdDatum.HalfDiff.condE_isCoprime_bb | exact GlobalTheory.FunObj.StdDatum.HalfDiff.condE_isCoprime_bb | (intros; apply GlobalTheory.FunObj.StdDatum.HalfDiff.condE_isCoprime_bb <;> assumption)
