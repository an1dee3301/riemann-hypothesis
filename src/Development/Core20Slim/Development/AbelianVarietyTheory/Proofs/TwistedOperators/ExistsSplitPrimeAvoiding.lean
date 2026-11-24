module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.IteratedLiftChains
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AbsNormEqOfNcardPlacesOver
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.FlagMeasures.CardEqNcardPrimesOver
public import Development.Core20Slim.Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.HermitianPerpSubgroup
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIrreducible
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NcardPrimesOverOfStabilizer
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Function
public import Init.Data.Int.Basic
public import Init.Data.Int.DivMod.Basic
public import Init.Data.Int.Order
public import Init.Data.Nat.Basic
public import Init.Data.Nat.Coprime
public import Init.Data.Nat.Div.Basic
public import Init.Data.Nat.Dvd
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Omega.Coeffs
public import Init.Omega.Constraint
public import Init.Omega.Int
public import Init.Omega.LinearCombo
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.EuclideanDomain.Int
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Order.Kleene
public import Mathlib.Algebra.Prime.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Int.Cast.Lemmas
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.Nat.Prime.Int
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.BoundedOrder.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.Coprime.Basic
public import Mathlib.RingTheory.Coprime.Lemmas
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.Ideal.Lattice
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Ideal.Maximal
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.RingTheory.Ideal.Over
public import Mathlib.RingTheory.Ideal.Prime
public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.RingTheory.PrincipalIdealDomain
public import Mathlib.SetTheory.Cardinal.Finite

@[expose] public section

open MeasureTheory NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Links
open GlobalTheory.IndefiniteRowSideFullHecke.IteratedLiftChains GlobalTheory.PRep GlobalTheory.LFun
open Formalism.UG (IsCommensurated Hecke)
open Formalism.MainNotions.SchurIrreducible (IsSplit)

namespace GlobalTheory.SplitChoice

theorem exists_place_over (K : Type) [Field K] [NumberField K] {p : ℕ} (hp : p.Prime) :
    ∃ v : HeightOneSpectrum (𝓞 K), (p : 𝓞 K) ∈ v.asIdeal := by
  have hmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.1 hp).irreducible
  obtain ⟨Q, hQ, hQc⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 K) (Ideal.span {(p : ℤ)})
    (by rw [(RingHom.injective_iff_ker_eq_bot (algebraMap ℤ (𝓞 K))).1 (FaithfulSMul.algebraMap_injective _ _)]; exact bot_le)
  have hm : ((p : ℕ) : 𝓞 K) ∈ Q := by
    have : (p : ℤ) ∈ Q.comap (algebraMap ℤ (𝓞 K)) := by
      change (p : ℤ) ∈ Ideal.under ℤ Q
      rw [hQc]
      exact Ideal.mem_span_singleton_self _
    simpa using this
  refine ⟨⟨Q, hQ.isPrime, fun h0 => ?_⟩, hm⟩
  rw [h0, Ideal.mem_bot] at hm
  exact hp.ne_zero (by exact_mod_cast hm)

theorem natCast_notMem_of_absNorm_lt {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) {p : ℕ}
    (hp : p.Prime) (h : Ideal.absNorm v.asIdeal < p) : (p : 𝓞 K) ∉ v.asIdeal := by
  intro hmem
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 := fun h0 => v.ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)
  have hcop : Nat.Coprime p (Ideal.absNorm v.asIdeal) :=
    (Nat.Prime.coprime_iff_not_dvd hp).2 fun hd => absurd (Nat.le_of_dvd (Nat.pos_of_ne_zero h0) hd) (by omega)
  obtain ⟨a, b, hab⟩ := (Nat.isCoprime_iff_coprime.2 hcop).map (Int.castRingHom (𝓞 K))
  simp only [eq_intCast, Int.cast_natCast] at hab
  exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
    (hab ▸ Ideal.add_mem _ (Ideal.mul_mem_left _ _ hmem) (Ideal.mul_mem_left _ _ (Ideal.absNorm_mem _))))

theorem splitsCompletely_of_modEq_one (D : D7) {p : ℕ} (hp : p.Prime)
    (hc : p ≡ 1 [MOD D.host.QS * D.host.q * D.host.d]) : SplitsCompletely D p := by
  obtain ⟨h1, -, h3⟩ := GlobalTheory.HostSplit.split_completely_of_modEq_one D.R D.host p hp hc
  have hs : GlobalTheory.IndefiniteRowSideFullHecke.FlagUnipotentStabilizers.SplitsCompletely D.host.E p := by
    unfold GlobalTheory.IndefiniteRowSideFullHecke.FlagUnipotentStabilizers.SplitsCompletely
    rw [GlobalTheory.SplitResidue.card_eq_ncard_primesOver D.host.E hp, ← GlobalTheory.HostSplit.ncard_placesOver D.host.E hp, h1]
  refine ⟨hp, fun w hw => ⟨h3 w hw, ?_⟩⟩
  haveI := w.isPrime
  have hs' := (GlobalTheory.SplitResidue.card_eq_ncard_primesOver D.host.E hp).symm.trans hs
  exact (GlobalTheory.LocSplit.split_prime hp hs' w.asIdeal hw).1


end GlobalTheory.SplitChoice
