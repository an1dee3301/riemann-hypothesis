module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
public import Development.Core20Slim.Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.ExistsSmallSpherical
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicValuationThetaKernelJetBound
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.HighestWeightBelow
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.VwNatCastNonneg
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.JetKapIff
public import Development.Core20Slim.Development.AutomorphicArithmetic.CyclotomicBounds.WildJets.DepthDrop
public import Development.Core20Slim.Development.AutomorphicArithmetic.CyclotomicBounds.WildJets.PrimeEqOfMemPrimeIdeal
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LevelPlusSubgroup
public import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.MemHalfCosetSelf
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataParams₂
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemSum
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Classical
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Nat.Div.Basic
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Finset.Lattice.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.PadicValNat
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Over
public import Mathlib.RingTheory.Multiplicity

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem UpperTheory.WildA.depth :
    ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GlobalTheory.ChiGrid.GridData L sc} (large₂ : SizeData₂ D), GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.SizeRows large₂ → ∀ {t : T} {p : GlobalTheory.ChiGrid.Pair T} (d : FinDatum G t p), d.P = locPl G t →
      ∀ (w : PlL D) (l : ℕ), l.Prime → (l : 𝓞 D.what₂.LL) ∈ w.asIdeal → Away G t w → ∀ k : ℕ, 0 < k → IsCosetDatum k d →
      ∃ k' : ℕ, 0 < k' ∧ IsCosetDatum k' d ∧ padicValNat l k' ≤ padicValNat l k ∧ (l ∣ k' → GlobalTheory.NormSum.SplitIn D l) := by
  classical
  intro D T L sc G large₂ hS t p d hP w l hl hlw hA k hk hc
  by_cases h : ∃ PP ∈ d.P, ((l : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal
  · obtain ⟨PP, hPP, hlPP⟩ := h
    have key : ((l : ℕ) : 𝓞 D.host.F) ∈ (HeightOneSpectrum.under (𝓞 D.host.F) PP).asIdeal := by
      rw [HeightOneSpectrum.under_asIdeal, Ideal.mem_under, map_natCast]
      exact hlPP
    have hsplit : GlobalTheory.NormSum.SplitIn D l := by
      rw [hP] at hPP
      unfold locPl at hPP
      rcases Finset.mem_union.mp hPP with h0 | hQ
      · unfold GlobalTheory.ChiGrid.Places.W0 at h0
        obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp h0
        rw [G.pl.w_over v hv] at key
        exact UpperTheory.WildA.small_set_primes_split large₂ hS v hv l hl key
      · rcases hA PP hQ with hS0 | hno
        · exact UpperTheory.WildA.small_set_primes_split large₂ hS _ hS0 l hl key
        · exact absurd hlw (hno l hl hlPP)
    exact ⟨k, hk, hc, le_rfl, fun _ => hsplit⟩
  · obtain ⟨k', hk', hnd, hc'⟩ := UpperTheory.WildA.depthDrop d l hl (fun w hw hlw' => h ⟨w, hw, hlw'⟩) k hk hc
    refine ⟨k', hk', hc', ?_, fun hd => absurd hd hnd⟩
    rw [Nat.padicValNat_def, multiplicity_eq_zero_of_not_dvd hnd]
    exact Nat.zero_le _
