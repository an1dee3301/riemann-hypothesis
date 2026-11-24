module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LineLatAt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FractionalIdealCompletionLocallyPrincipal
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitIdealCompletionAtPlaceEqIntegralAdelesAtPlac
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TmulOneMemIntAt
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PeriodIdealZpowCompletionAdeleConjIff
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemSum
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.BinderNameHint
public import Init.Classical
public import Init.Core
public import Init.Data.Rat.Basic
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Ring.Action.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Nontrivial.Defs
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Logic.Function.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Maximal
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.Ideal.Pointwise
public import Mathlib.RingTheory.Ideal.Prime
public import Mathlib.Tactic.Push

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.ChiGrid
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open scoped Pointwise

namespace GlobalTheory.ModulUnit

variable {D : D7}

theorem exists_sep {v v' : GlobalTheory.FinPl.Pl D} (h : v' ≠ v) :
    ∃ t : 𝓞 D.host.F, t ∈ v'.asIdeal ∧ t ∉ v.asIdeal := by
  by_contra hc
  push_neg at hc
  exact h (HeightOneSpectrum.ext (v'.isMaximal.eq_of_le v.isPrime.ne_top hc))



variable {T : Type} {L : LevCh D T}

theorem exists_mem_modul (P : Places L) (sc : Consts) {v : GlobalTheory.FinPl.Pl D} (hv : v ∉ P.S0) :
    ∃ s : 𝓞 D.host.F, s ∉ v.asIdeal ∧ algebraMap (𝓞 D.host.F) (𝓞 D.host.E) s ∈ P.modul sc := by
  classical
  have hsep : ∀ v' ∈ P.S0, ∃ t : 𝓞 D.host.F, t ∈ v'.asIdeal ∧ t ∉ v.asIdeal :=
    fun v' hv' => exists_sep fun e => hv (e ▸ hv')
  choose! t ht using hsep
  refine ⟨∏ v' ∈ P.S0, t v' ^ P.depth sc v', fun hm => ?_, ?_⟩
  · obtain ⟨v', hv', hm'⟩ := (haveI := v.isPrime; Ideal.IsPrime.prod_mem_iff.1 hm)
    exact (ht v' hv').2 (v.isPrime.mem_of_pow_mem _ hm')
  · rw [map_prod]
    refine Ideal.prod_mem_prod fun v' hv' => ?_
    rw [map_pow]
    refine Ideal.pow_mem_pow ?_ _
    have h : t v' ∈ ((P.w v').under (𝓞 D.host.F)).asIdeal := by rw [P.under_w hv']; exact (ht v' hv').1
    exact h
end GlobalTheory.ModulUnit

namespace GlobalTheory.ModulUnit

variable {D : D7} {T : Type} {L : LevCh D T}

theorem conj_smul_algebraMap (s : 𝓞 D.host.F) :
    D.host.conj • algebraMap (𝓞 D.host.F) (𝓞 D.host.E) s = algebraMap (𝓞 D.host.F) (𝓞 D.host.E) s := by
  apply RingOfIntegers.ext
  show D.host.conj ((s : D.host.F) : D.host.E) = ((s : D.host.F) : D.host.E)
  exact (D.host.conjE_mem_hostF_iff _).1 (s : D.host.F).2

theorem exists_mem_modulBar (P : Places L) (sc : Consts) {v : GlobalTheory.FinPl.Pl D} (hv : v ∉ P.S0) :
    ∃ s : 𝓞 D.host.F, s ∉ v.asIdeal ∧ algebraMap (𝓞 D.host.F) (𝓞 D.host.E) s ∈ P.modulBar sc := by
  obtain ⟨s, hs, hm⟩ := exists_mem_modul P sc hv
  refine ⟨s, hs, ?_⟩
  have := Ideal.smul_mem_pointwise_smul D.host.conj _ _ hm
  rwa [conj_smul_algebraMap] at this

end GlobalTheory.ModulUnit


