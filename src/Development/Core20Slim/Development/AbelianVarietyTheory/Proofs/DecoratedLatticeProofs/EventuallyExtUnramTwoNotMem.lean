module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnramifiedCharacter
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Classical
public import Init.Core
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.PropLemmas
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Divisibility.Basic
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Module.Submodule.Pointwise
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Ring.Basic
public import Mathlib.Algebra.Ring.CharZero
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Basic
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Set.Insert
public import Mathlib.Data.Set.Operations
public import Mathlib.FieldTheory.Perfect
public import Mathlib.FieldTheory.Separable
public import Mathlib.GroupTheory.OreLocalization.OreSet
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Filter.Cofinite
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.DedekindDomain.Different
public import Mathlib.RingTheory.DedekindDomain.Factorization
public import Mathlib.RingTheory.DedekindDomain.Ideal.Basic
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Over
public import Mathlib.RingTheory.Ideal.Prime
public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.RingTheory.OreLocalization.Ring
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.Unramified.Locus
public import Mathlib.Tactic.Push

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair ValuativeRel NumberField Filter IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl

theorem eventually_extUnram_two_notMem : ∀ D : D7, ∀ᶠ v : Pl D in cofinite, GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.ExtUnramAt D v ∧ (2 : 𝓞 D.host.F) ∉ v.asIdeal := by
  intro D
  rw [Filter.eventually_cofinite]
  have h2 : (2 : 𝓞 D.host.F) ≠ 0 := two_ne_zero
  have hB : (Ideal.span {(2 : 𝓞 D.host.F)}) ≠ 0 := by
    simpa [Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot] using h2
  have hfin2 := Ideal.finite_factors hB
  have hfinD := Ideal.finite_factors
    (differentIdeal_ne_bot (A := 𝓞 D.host.F) (B := 𝓞 D.host.E))
  have hfinU : ((fun Q : HeightOneSpectrum (𝓞 D.host.E) => Q.asIdeal.under (𝓞 D.host.F)) ''
      {Q | Q.asIdeal ∣ differentIdeal (𝓞 D.host.F) (𝓞 D.host.E)}).Finite := hfinD.image _
  have hfinA : {v : Pl D | v.asIdeal ∈ (fun Q : HeightOneSpectrum (𝓞 D.host.E) => Q.asIdeal.under (𝓞 D.host.F)) ''
      {Q | Q.asIdeal ∣ differentIdeal (𝓞 D.host.F) (𝓞 D.host.E)}}.Finite :=
    hfinU.preimage (f := fun v : Pl D => v.asIdeal)
      (fun a _ b _ h => HeightOneSpectrum.ext h)
  refine (hfinA.union hfin2).subset fun v hv => ?_
  by_cases h : (2 : 𝓞 D.host.F) ∈ v.asIdeal
  · right
    exact Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 h)
  · left
    have hE : ¬ GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.ExtUnramAt D v := fun hu => hv ⟨hu, h⟩
    unfold GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.ExtUnramAt at hE
    push_neg at hE
    obtain ⟨P, hP, hL, hU⟩ := hE
    have hover : v.asIdeal = P.under (𝓞 D.host.F) := hL.over
    have hPb : P ≠ ⊥ := by
      rintro rfl
      apply v.ne_bot
      rw [hover, Ideal.under_bot]
    refine ⟨⟨P, hP, hPb⟩, ?_, hover.symm⟩
    by_contra hd
    exact hU (not_dvd_differentIdeal_iff.1 hd)

end GlobalTheory.FinPl
