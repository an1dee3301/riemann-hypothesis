module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.StepVecCongr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TypePlacesNotPairwiseConjugate
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftLevelsGoodPrimesProperties
public import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
public import Development.AbelianVarietyTheory.Definitions.Divisors.LeastSplitAuxiliaryPrimeThetaChainSpec
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemSum
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.LocalToGlobal.UnitaryNorms.CharHost
public import Formalism.LocalToGlobal.UnitaryNorms.CharTied
public import Formalism.QuotientMetricDivisors.Statement
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Classical
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Fin.Basic
public import Init.Data.List.Basic
public import Init.Data.List.FinRange
public import Init.Data.Nat.Basic
public import Init.Data.Rat.Basic
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Finset.Insert
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Ideal.Defs

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun GlobalTheory.ChainCol
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open Classical

namespace GlobalTheory.LevelPlacesChosen

theorem levelPlaces_subset_chosenPlaces : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) {μ₀ : T},
    L.Is μ₀ → L.Pg ⊆ G.pl.W0 := by
  intro D T L sc G μ₀ hμ P hP
  obtain ⟨k, hk⟩ := (hμ.Pg P).1 hP
  have hK : P.under (𝓞 D.host.K) = L.C.P.pb k := hk
  have hgE : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal := by
    have h1 : ((D.host.g k : ℕ) : 𝓞 D.host.K) ∈ (P.under (𝓞 D.host.K)).asIdeal := by
      rw [hK]; exact L.C.P.pb_over k
    have h2 : algebraMap (𝓞 D.host.K) (𝓞 D.host.E) ((D.host.g k : ℕ) : 𝓞 D.host.K) ∈ P.asIdeal := h1
    rwa [map_natCast] at h2
  have hgF : ((D.host.g k : ℕ) : 𝓞 D.host.F) ∈ (P.under (𝓞 D.host.F)).asIdeal := by
    show algebraMap (𝓞 D.host.F) (𝓞 D.host.E) ((D.host.g k : ℕ) : 𝓞 D.host.F) ∈ P.asIdeal
    rw [map_natCast]; exact hgE
  have hS1 : P.under (𝓞 D.host.F) ∈ S1 D := by
    rw [S1_mem_OmF]
    fin_cases k
    · exact Or.inl hgF
    · exact Or.inr (Or.inl hgF)
  have hS0 : P.under (𝓞 D.host.F) ∈ insert G.pl.v0 (S1 D) := Finset.mem_insert_of_mem hS1
  have hwPg : G.pl.w (P.under (𝓞 D.host.F)) ∈ L.Pg := G.pl.w_g _ k hgF
  have hover : (G.pl.w (P.under (𝓞 D.host.F))).under (𝓞 D.host.F) = P.under (𝓞 D.host.F) := G.pl.w_over _ hS0
  have heq : G.pl.w (P.under (𝓞 D.host.F)) = P := by
    rcases GlobalTheory.GoodPrimes.eq_or_conj_of_under_eq hover with h | h
    · exact h
    · exact absurd ((GlobalTheory.GoodPrimes.isConjPl_iff).2 h)
        (GlobalTheory.TypePlaces.not_isConjPl L.C.P L.Pg hμ.Pg P hP _ hwPg)
  unfold Places.W0
  exact Finset.mem_image.2 ⟨_, hS0, heq⟩

end GlobalTheory.LevelPlacesChosen
