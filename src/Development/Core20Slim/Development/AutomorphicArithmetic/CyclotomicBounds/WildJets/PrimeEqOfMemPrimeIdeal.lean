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
public import Formalism.LocalToGlobal.UnitaryNorms.LeastSplitAuxiliaryPrimeThetaChainSpec
public import Development.Core20Slim.Formalism.LocalToGlobal.UnitaryNorms.CharShare
public import Batteries.Classes.RatCast
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LevelPlusSubgroup
public import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
public import Development.AbelianVarietyTheory.Definitions.Divisors.LeastSplitAuxiliaryPrimeThetaChainSpec
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataParams
public import Formalism.LocalRingCardinality.DataParamsT
public import Formalism.LocalRingCardinality.DataParams₂
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.SharpRestriction.Divisibility.AbsolutelyIrreducibleSpan
public import Formalism.SharpRestriction.ElevenLe
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Fin.Basic
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Nat.Coprime
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Int.Cast.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Int.Cast.Lemmas
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.Coprime.Basic
public import Mathlib.RingTheory.Coprime.Lemmas
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Lattice
public import Mathlib.RingTheory.Ideal.Prime

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

private theorem UpperTheory.WildA.prime_eq_of_mem_prime_ideal {R : Type} [CommRing R] {I : Ideal R} (hI : I.IsPrime) {a b : ℕ} (ha : a.Prime)
    (hb : b.Prime) (hai : (a : R) ∈ I) (hbi : (b : R) ∈ I) : a = b := by
  by_contra hne
  have h : Nat.Coprime a b := (Nat.coprime_primes ha hb).2 hne
  obtain ⟨u, v, e⟩ := (Nat.isCoprime_iff_coprime.2 h).map (Int.castRingHom R)
  apply hI.ne_top
  rw [Ideal.eq_top_iff_one, ← e]
  simp only [eq_intCast, Int.cast_natCast]
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hai) (Ideal.mul_mem_left _ _ hbi)

private theorem UpperTheory.WildA.split_of_split_class {D : D7} {p : ℕ} (h : D.host.cls p = .splitK) : GlobalTheory.NormSum.SplitIn D p := by
  right
  unfold Formalism.BasicNotions.Host.cls primeClass at h
  split_ifs at h with h1 h2 h3 h4 <;> first | exact h4 | cases h

theorem UpperTheory.WildA.small_set_primes_split :
    ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GlobalTheory.ChiGrid.GridData L sc} (large₂ : SizeData₂ D), GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.SizeRows large₂ → ∀ v ∈ G.pl.S0, ∀ l : ℕ, l.Prime → ((l : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal →
      GlobalTheory.NormSum.SplitIn D l := by
  intro D T L sc G large₂ hS v hv l hl hlv
  obtain ⟨⟨Pm, -, -⟩, -⟩ := hS
  have key : ∀ p : ℕ, p.Prime → p ∈ D.host.levelPrimes → ((p : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal →
      GlobalTheory.NormSum.SplitIn D l := fun p hp hm h => by
    rw [UpperTheory.WildA.prime_eq_of_mem_prime_ideal v.isPrime hl hp hlv h]
    exact UpperTheory.WildA.split_of_split_class (Pm.level_split p hm)
  rcases G.pl.mem_S0_of_sum_eq.1 hv with rfl | h1
  · rw [UpperTheory.WildA.prime_eq_of_mem_prime_ideal G.pl.v0.isPrime hl (Formalism.L2.Host.leastSplitAuxiliaryPrimeThetaChain_spec D).1 hlv G.pl.basePlace_over_qZero]
    exact Or.inr (Formalism.L2.Host.split_prime_jacobi_neg_d D)
  · rcases (S1_mem_OmF D).1 h1 with h | h | h | h
    · exact key _ (D.host.g_prime 0) (D.host.g_level 0) h
    · exact key _ (D.host.g_prime 1) (D.host.g_level 1) h
    · exact key _ D.host.pde_prime D.host.pde_level.1 h
    · exact key _ D.host.pde'_prime D.host.pde_level.2 h
