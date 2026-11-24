module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrimeDvdAbsNormHalfDifferent
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.CondEIsCoprimeHalfDifferent
public import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Data.Nat.Coprime
public import Init.Data.Rat.Basic
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Kleene
public import Mathlib.Algebra.Ring.Action.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Coprime.Basic
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.Ideal.Pointwise

@[expose] public section

noncomputable section

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open GlobalTheory.ChiGrid GlobalTheory.FunObj.SqNum

namespace GlobalTheory.FunObj.StdDatum.HalfDiff

theorem condE_isCoprime_bb {D : D7} {T : Type} {L : LevCh D T} (P : Places L) (h1 : Nat.Coprime D.host.pde (D.host.QS * D.host.q))
    (h2 : Nat.Coprime D.host.pde' (D.host.QS * D.host.q)) : IsCoprime (condE P) D.host.𝔟 :=
  (condE_isCoprime_halfDifferent P ⟨h1, h2⟩).1

end GlobalTheory.FunObj.StdDatum.HalfDiff
