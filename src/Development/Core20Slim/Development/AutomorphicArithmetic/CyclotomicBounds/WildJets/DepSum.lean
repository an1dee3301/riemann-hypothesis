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
public import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemSum
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Classical
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Int.Lemmas
public import Init.Data.Nat.Basic
public import Init.Data.Nat.Coprime
public import Init.Data.Nat.Div.Basic
public import Init.Data.Nat.Dvd
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Subsemigroup.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Kleene
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Empty
public import Mathlib.Data.Finset.Filter
public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Finset.Insert
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Finset.Range
public import Mathlib.Data.Int.Cast.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Cast.Order.Basic
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Lattice.Nat
public import Mathlib.Order.Nat
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.Coprime.Basic
public import Mathlib.RingTheory.Coprime.Lemmas
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Lattice
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.RingTheory.Ideal.Over
public import Mathlib.RingTheory.Ideal.Prime
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.Positivity.Core

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

private theorem false_of_coprime_natCast_mem_heightOne {R : Type*} [CommRing R] [IsDomain R] (v : HeightOneSpectrum R)
    (a b : ℕ) (hab : Nat.Coprime a b) (ha : (a : R) ∈ v.asIdeal) (hb : (b : R) ∈ v.asIdeal) : False := by
  obtain ⟨x, y, hxy⟩ := Nat.isCoprime_iff_coprime.2 hab
  have h1 : (x : R) * a + (y : R) * b = 1 := by
    have := congrArg (Int.cast : ℤ → R) hxy
    push_cast at this
    exact this
  apply v.isPrime.ne_top
  rw [Ideal.eq_top_iff_one, ← h1]
  exact add_mem (Ideal.mul_mem_left _ _ ha) (Ideal.mul_mem_left _ _ hb)

private theorem prime_le_absNorm_of_mem_heightOne (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) (l : ℕ)
    (hl : l.Prime) (h : (l : 𝓞 K) ∈ v.asIdeal) : l ≤ Ideal.absNorm v.asIdeal := by
  have hN : Ideal.absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact v.ne_bot
  apply Nat.le_of_dvd (Nat.pos_of_ne_zero hN)
  by_contra hd
  exact false_of_coprime_natCast_mem_heightOne v l _ ((Nat.Prime.coprime_iff_not_dvd hl).2 hd) h (Ideal.absNorm_mem _)

private theorem prime_eq_of_natCast_mem_heightOne {R : Type*} [CommRing R] [IsDomain R] (v : HeightOneSpectrum R)
    (l m : ℕ) (hl : l.Prime) (hm : m.Prime) (h1 : (l : R) ∈ v.asIdeal) (h2 : (m : R) ∈ v.asIdeal) : l = m := by
  by_contra hne
  exact false_of_coprime_natCast_mem_heightOne v l m ((Nat.coprime_primes hl hm).2 hne) h1 h2

theorem UpperTheory.WildA.depSum :
    ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GlobalTheory.ChiGrid.GridData L sc}, ∃ S : Finset ℕ, GlobalTheory.NormSum.Exponents S (fun l => if l.Prime then (depL G l : ℝ) else 0) (sig G) := by
  classical
  intro D T L sc G
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ v ∈ G.pl.S0, Ideal.absNorm v.asIdeal ≤ N := by
    refine ⟨∑ v ∈ G.pl.S0, Ideal.absNorm v.asIdeal, fun v hv => ?_⟩
    exact Finset.single_le_sum (f := fun v : Pl ↥D.host.F => Ideal.absNorm v.asIdeal)
      (fun _ _ => Nat.zero_le _) hv
  obtain ⟨S, hS⟩ : ∃ S : Finset ℕ, ∀ l, l ∈ S ↔ l.Prime ∧ l ≤ N :=
    ⟨(Finset.range (N + 1)).filter Nat.Prime, fun l => by
      rw [Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff, and_comm]⟩
  have key : ∀ v ∈ G.pl.S0, ∀ l : ℕ, l.Prime → ((l : ℕ) : 𝓞 D.host.E) ∈ (G.pl.w v).asIdeal →
      l ≤ Ideal.absNorm v.asIdeal := by
    intro v hv l hl h
    apply prime_le_absNorm_of_mem_heightOne _ v l hl
    have := G.pl.w_over v hv
    rw [← this]
    simpa [IsDedekindDomain.HeightOneSpectrum.under] using h
  have hdep : ∀ l : ℕ, depL G l ≤
      ∑ v ∈ G.pl.S0.filter (fun v => ((l : ℕ) : 𝓞 D.host.E) ∈ (G.pl.w v).asIdeal), G.pl.depth sc v := by
    intro l
    unfold GlobalTheory.SumSize.depL
    apply Finset.sup_le
    intro PP hPP
    obtain ⟨hPP1, hmem⟩ := Finset.mem_filter.1 hPP
    unfold GlobalTheory.ChiGrid.Places.W0 at hPP1
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hPP1
    rw [(GlobalTheory.FunObj.depthAt_w G hv).2]
    exact Finset.single_le_sum (f := fun v => G.pl.depth sc v) (fun _ _ => Nat.zero_le _)
      (Finset.mem_filter.2 ⟨hv, hmem⟩)
  have hinner : ∀ v ∈ G.pl.S0,
      ∑ l ∈ S.filter (fun l : ℕ => ((l : ℕ) : 𝓞 D.host.E) ∈ (G.pl.w v).asIdeal), Real.log (l : ℝ) ≤
        Real.log (Ideal.absNorm v.asIdeal : ℝ) := by
    intro v hv
    rcases (S.filter (fun l : ℕ => ((l : ℕ) : 𝓞 D.host.E) ∈ (G.pl.w v).asIdeal)).eq_empty_or_nonempty
      with he | ⟨l0, hl0⟩
    · rw [he, Finset.sum_empty]
      exact Real.log_natCast_nonneg _
    · obtain ⟨hl0S, hl0P⟩ := Finset.mem_filter.1 hl0
      have hp0 : l0.Prime := ((hS l0).1 hl0S).1
      have hsub : S.filter (fun l : ℕ => ((l : ℕ) : 𝓞 D.host.E) ∈ (G.pl.w v).asIdeal) ⊆ {l0} := by
        intro m hm
        rw [Finset.mem_singleton]
        obtain ⟨hmS, hmP⟩ := Finset.mem_filter.1 hm
        exact prime_eq_of_natCast_mem_heightOne _ m l0 ((hS m).1 hmS).1 hp0 hmP hl0P
      calc _ ≤ ∑ l ∈ ({l0} : Finset ℕ), Real.log (l : ℝ) :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => Real.log_natCast_nonneg i)
        _ = Real.log (l0 : ℝ) := Finset.sum_singleton _ _
        _ ≤ _ := by
          apply Real.log_le_log (by exact_mod_cast hp0.pos)
          exact_mod_cast key v hv l0 hp0 hl0P
  refine ⟨S, ?_⟩
  unfold GlobalTheory.NormSum.Exponents
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro l hl
    exact ((hS l).1 hl).1
  · intro l
    dsimp only
    split_ifs <;> positivity
  · intro l hl
    dsimp only
    split_ifs with hp
    · have h0 : depL G l = 0 := by
        apply Nat.eq_zero_of_le_zero
        refine (hdep l).trans (le_of_eq (Finset.sum_eq_zero ?_))
        intro v hv'
        obtain ⟨hv, hmem⟩ := Finset.mem_filter.1 hv'
        exact absurd ((hS l).2 ⟨hp, (key v hv l hp hmem).trans (hN v hv)⟩) hl
      rw [h0, Nat.cast_zero]
    · rfl
  · dsimp only
    calc ∑ l ∈ S, (if l.Prime then (depL G l : ℝ) else 0) * Real.log (l : ℝ)
        ≤ ∑ l ∈ S, ∑ v ∈ G.pl.S0, (if ((l : ℕ) : 𝓞 D.host.E) ∈ (G.pl.w v).asIdeal then
            (G.pl.depth sc v : ℝ) * Real.log (l : ℝ) else 0) := by
          apply Finset.sum_le_sum
          intro l hl
          have hp : l.Prime := ((hS l).1 hl).1
          rw [if_pos hp, ← Finset.sum_filter, ← Finset.sum_mul]
          apply mul_le_mul_of_nonneg_right _ (Real.log_natCast_nonneg l)
          exact_mod_cast hdep l
      _ = ∑ v ∈ G.pl.S0, (G.pl.depth sc v : ℝ) *
            ∑ l ∈ S.filter (fun l : ℕ => ((l : ℕ) : 𝓞 D.host.E) ∈ (G.pl.w v).asIdeal), Real.log (l : ℝ) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl (fun v _ => ?_)
          rw [Finset.mul_sum, Finset.sum_filter]
      _ ≤ ∑ v ∈ G.pl.S0, (G.pl.depth sc v : ℝ) * Real.log (Ideal.absNorm v.asIdeal : ℝ) := by
          apply Finset.sum_le_sum
          intro v hv
          exact mul_le_mul_of_nonneg_left (hinner v hv) (by positivity)
      _ = sig G := by
          unfold GlobalTheory.SumSize.sig
          rfl
