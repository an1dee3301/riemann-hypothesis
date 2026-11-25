module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrimeDvdAbsNormHalfDifferent
public import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
public import Development.AbelianVarietyTheory.Definitions.Divisors.LeastSplitAuxiliaryPrimeThetaChainSpec
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataParams
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemSum
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
public import Formalism.SharpRestriction.LevelLetterCocycles.TwGood
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Classical
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Fin.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Nat.Coprime
public import Init.Data.Nat.Div.Basic
public import Init.Data.Nat.Gcd
public import Init.Data.Rat.Basic
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Divisibility.Basic
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Order.Kleene
public import Mathlib.Algebra.Ring.Action.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.GCD.BigOperators
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.Logic.Function.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Basic
public import Mathlib.Order.BoundedOrder.Basic
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.Coprime.Basic
public import Mathlib.RingTheory.DedekindDomain.Ideal.Basic
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Lattice
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Ideal.Maximal
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.Ideal.Pointwise
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.ModelLatIn

@[expose] public section

noncomputable section

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions
open GlobalTheory.ChiGrid GlobalTheory.FunObj.SqNum

namespace GlobalTheory.FunObj.StdDatum.HalfDiff

theorem isCoprime_of_natCast_mem {D : D7} {I : Ideal (𝓞 D.host.E)} {N : ℕ} (hN : Nat.Coprime N (D.host.QS * D.host.q))
    (hI : (N : 𝓞 D.host.E) ∈ I) : IsCoprime I D.host.𝔟 := by
  rw [Ideal.isCoprime_iff_sup_eq]
  by_contra h
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ h
  have hb : D.host.𝔟 ≤ M := le_sup_right.trans hle
  have h0 : M ≠ ⊥ := fun e => ReciprocityTheory.ChartRestriction.G.PullbackSections.MLI.bb_ne_bot D (eq_bot_iff.2 (e ▸ hb))
  let P : HeightOneSpectrum (𝓞 D.host.E) := ⟨M, hM.isPrime, h0⟩
  exact GlobalTheory.HalfCompare.not_mem_of_coprime P hN (GlobalTheory.HalfCompare.two_q_mem (P := P) (Ideal.dvd_iff_le.2 hb))
    (hle (Ideal.mem_sup_left hI))

theorem coprime_of_mod {a b m : ℕ} (h : a % m = 1) (hb : b ∣ m) : Nat.Coprime a b := by
  have : Nat.Coprime a m := by rw [Nat.Coprime, Nat.gcd_comm, Nat.gcd_rec, h, Nat.gcd_one_left]
  exact this.coprime_dvd_right hb

theorem exists_nat_mem_place_coprime {D : D7} {T : Type} {L : LevCh D T} (P : Places L)
    (h : Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q)) {v : HeightOneSpectrum (𝓞 D.host.F)} (hv : v ∈ P.S0) :
    ∃ p : ℕ, Nat.Coprime p (D.host.QS * D.host.q) ∧ ((p : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal := by
  have hg : ∀ k, Nat.Coprime (D.host.g k) (D.host.QS * D.host.q) := fun k =>
    coprime_of_mod (D.ntypes.g_cond k) (dvd_mul_right _ _)
  rcases P.mem_S0_of_sum_eq.1 hv with rfl | h1
  · exact ⟨q0 D, coprime_of_mod (leastSplitAuxiliaryPrimeThetaChain_spec D).2.1
      (Dvd.dvd.mul_left ⟨D.host.d, rfl⟩ _), P.basePlace_over_qZero⟩
  · rcases (S1_mem_OmF D).1 h1 with h' | h' | h' | h'
    · exact ⟨_, hg 0, h'⟩
    · exact ⟨_, hg 1, h'⟩
    · exact ⟨_, h.1, h'⟩
    · exact ⟨_, h.2, h'⟩

theorem exists_nat_mem_condE {D : D7} {T : Type} {L : LevCh D T} (P : Places L)
    (h : Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q)) :
    ∃ N : ℕ, Nat.Coprime N (D.host.QS * D.host.q) ∧ (N : 𝓞 D.host.E) ∈ SqNum.condE P := by
  classical
  choose! p hp hm using fun v (hv : v ∈ P.S0) => exists_nat_mem_place_coprime P h hv
  refine ⟨∏ v ∈ P.S0, p v ^ condExp P v, Nat.Coprime.prod_left fun v hv => (hp v hv).pow_left _, ?_⟩
  unfold SqNum.condE
  push_cast
  refine Ideal.prod_mem_prod fun v hv => Ideal.pow_mem_pow ?_ _
  have h1 : ((p v : ℕ) : 𝓞 D.host.F) ∈ ((P.w v).under (𝓞 D.host.F)).asIdeal := by
    rw [P.under_w hv]; exact hm v hv
  simpa using Ideal.mem_comap.1 h1

theorem condE_isCoprime_halfDifferent {D : D7} {T : Type} {L : LevCh D T} (P : Places L)
    (h : Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q)) :
    IsCoprime (SqNum.condE P) D.host.𝔟 ∧ IsCoprime (D.host.conj • SqNum.condE P) D.host.𝔟 := by
  obtain ⟨N, hN, hm⟩ := exists_nat_mem_condE P h
  refine ⟨isCoprime_of_natCast_mem hN hm, isCoprime_of_natCast_mem hN ?_⟩
  have h1 := Ideal.smul_mem_pointwise_smul D.host.conj _ _ hm
  have h2 : D.host.conj • (N : 𝓞 D.host.E) = N := map_natCast (MulSemiringAction.toRingHom _ _ D.host.conj) N
  rwa [h2] at h1

end GlobalTheory.FunObj.StdDatum.HalfDiff

end
