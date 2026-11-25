module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPlaceModelPlaceMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinPartConjMem
public import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.LocalToGlobal.Columns.DecoFin
public import Formalism.LocalToGlobal.Columns.StdLatUnimodular
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Formalism.LocalToGlobal.HeckeThetaElements.IsHeckeElt
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemSum
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Order.Kleene
public import Mathlib.Algebra.Quotient
public import Mathlib.Algebra.Ring.Action.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
public import Mathlib.LinearAlgebra.Quotient.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Ideal.Maximal
public import Mathlib.RingTheory.Ideal.Over
public import Mathlib.RingTheory.Ideal.Pointwise
public import Mathlib.RingTheory.Ideal.Quotient.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FunObj.SqNum

theorem conj_smul_int {D : D7} (x : 𝓞 D.host.E) : (D.host.conj • x : 𝓞 D.host.E) = Formalism.L2.Col.cO _ x := by
  apply RingOfIntegers.ext
  rw [show ((Formalism.L2.Col.cO D.host.E x : 𝓞 D.host.E) : D.host.E) = star (x : D.host.E) from rfl,
    Formalism.BasicNotions.bridge_star_holds D.R D.host]
  rfl

theorem exists_prime_notInert_place : ∀ {D : D7} {T : Type} {L : LevCh D T} (P : Places L) (v : HeightOneSpectrum (𝓞 D.host.F)),
    v ∈ P.S0 → ∃ q : ℕ, q.Prime ∧ ¬ InertQ D q ∧ ((q : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal := by
  intro D T L P v hv
  obtain ⟨e, he⟩ := P.w_split v hv
  have hunder := P.w_over v hv
  obtain ⟨q, hq, hqv⟩ : ∃ q : ℕ, q.Prime ∧ ((q : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal := by
    have := v.isMaximal
    have : Finite (𝓞 D.host.F ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ v.ne_bot
    letI := Ideal.Quotient.field v.asIdeal
    refine ⟨ringChar (𝓞 D.host.F ⧸ v.asIdeal), CharP.char_is_prime (𝓞 D.host.F ⧸ v.asIdeal) _, ?_⟩
    exact Ideal.Quotient.eq_zero_iff_mem.1 (by simpa using CharP.cast_eq_zero (𝓞 D.host.F ⧸ v.asIdeal) (ringChar _))
  refine ⟨q, hq, fun hin => ?_, hqv⟩
  have hqQ : ((q : ℕ) : 𝓞 D.host.E) ∈ (P.w v).asIdeal := by
    have h1 : ((q : ℕ) : 𝓞 D.host.F) ∈ ((P.w v).under (𝓞 D.host.F)).asIdeal := by rw [hunder]; exact hqv
    simpa [HeightOneSpectrum.under] using h1
  have hfix := hin (P.w v).asIdeal (P.w v).isPrime (P.w v).ne_bot hqQ
  have hf : ∀ x, x ∈ (P.w v).asIdeal → Formalism.L2.Col.cO _ x ∈ (P.w v).asIdeal := fun x hx => by
    rw [← conj_smul_int, ← hfix]
    exact Ideal.smul_mem_pointwise_smul _ _ _ hx
  have hmem : ∀ x, x ∈ (P.w v).asIdeal ↔ Formalism.L2.Col.cO _ x ∈ (P.w v).asIdeal := fun x =>
    ⟨hf x, fun hx => by simpa [Formalism.L2.Col.cO_cO] using hf _ hx⟩
  have hc := GlobalTheory.MovedIdem.isIdemAt_conj he hmem
  have e1 : e = Formalism.L2.Theta.cA D e := (GlobalTheory.ExportSeries.idemAt_eq he).symm.trans (GlobalTheory.ExportSeries.idemAt_eq hc)
  have e0 : e = 0 := by
    calc e = e * e := he.1.1.symm
      _ = e * Formalism.L2.Theta.cA D e := by rw [← e1]
      _ = 0 := he.1.2.1
  obtain ⟨x, hxQ, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (P.w v).ne_bot
  have h2 := (he.2 x hx0).1 hxQ
  rw [e0, zero_mul, map_zero] at h2
  exact h2 (zero_mem _)

end GlobalTheory.FunObj.SqNum
