module

public import Mathlib
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.VpBounds
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToricSumEqHeckeLValueMulAuxiliaryFactors
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinPartEqOneOfLevel
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsValCharTwist
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HeckeTateFunctionalEquationCM
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HeckeLPartialContinuationHolds
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelAndTwistPlacesSplitDistinct
public import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
public import Development.AbelianVarietyTheory.Definitions.Divisors.EntireEqOfHalfPlane
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsFinSetSplitPlacesCoprimeConductor
public import Development.AbelianVarietyTheory.Definitions.Divisors.LeastSplitAuxiliaryPrimeThetaChainSpec
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemSum
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.QuotientMetricDivisors.Statement
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Classical
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
public import Mathlib.Algebra.Divisibility.Basic
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Pointwise
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Order.Kleene
public import Mathlib.Algebra.Ring.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Equiv
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Filter
public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Finset.Lattice.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Mathlib.RingTheory.DedekindDomain.Ideal.Basic
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Ideal.Maximal
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.Multiplicity
public import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity
public import Mathlib.SetTheory.Cardinal.Finite

@[expose] public section

open NumberField IsDedekindDomain
open Classical

namespace GlobalTheory.KummerTwistLemmas

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem twist_places_under_split_coprime_conductor : ∀ {D : Formalism.BasicNotions.D7} {T : Type} {L : Formalism.IndefR.Links.LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} (G : GlobalTheory.ChiGrid.GridData L sc) {μ₀ : T}, L.Is μ₀ → ∀ (t : T), GlobalTheory.CMVal.IsFinSetSplitPlacesCoprimeConductor (GlobalTheory.FunObj.SqNum.condF G.pl) ((GlobalTheory.SqTop.twPl G t).image fun P => P.under (𝓞 D.host.F)) := by
  intro D T L sc G μ₀ hL t q hq
  obtain ⟨P, hP, rfl⟩ := Finset.mem_image.1 hq
  have hP' : P ∈ L.Q t ∧ P ∉ G.pl.W0 := by
    simp only [GlobalTheory.SqTop.twPl, Finset.mem_filter] at hP
    rcases Finset.mem_union.1 hP.1 with h | h
    · exact absurd h hP.2
    · exact ⟨h, hP.2⟩
  refine ⟨⟨P, Formalism.DivisionValues.conjPl P, fun e => ?_, rfl, ?_⟩, ?_⟩
  · apply (hL.Q_pl t P hP'.1).2 P hP'.1
    intro c hc
    refine ⟨Formalism.DivisionValues.cO _ c, ?_, rfl⟩
    have h : Formalism.DivisionValues.cO _ c ∈ (Formalism.DivisionValues.conjPl P).asIdeal := Ideal.mem_map_of_mem _ hc
    rwa [← e] at h
  · exact congrArg HeightOneSpectrum.asIdeal (GlobalTheory.TwistTypePlaces.under_conjPl P)
  · have hS : P.under (𝓞 D.host.F) ∉ G.pl.S0 := by
      intro h
      rcases G.pl.mem_S0_of_sum_eq.1 h with h0 | h1
      · exact G.pl.levelPlace_ne_basePlace t P hP'.1 h0
      · apply hP'.2
        rw [G.pl.w_Q t P hP'.1 h1]
        exact Finset.mem_image_of_mem _ h
    have h0 := GlobalTheory.FunObj.SqNum.Model.expIn_condF G.pl (P.under (𝓞 D.host.F))
    rw [if_neg hS] at h0
    have hne : GlobalTheory.FunObj.SqNum.condF G.pl ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun u _ => pow_ne_zero _ u.ne_bot
    exact (multiplicity_eq_zero (FiniteMultiplicity.of_prime_left (P.under (𝓞 D.host.F)).prime hne)).1 h0

end GlobalTheory.KummerTwistLemmas
