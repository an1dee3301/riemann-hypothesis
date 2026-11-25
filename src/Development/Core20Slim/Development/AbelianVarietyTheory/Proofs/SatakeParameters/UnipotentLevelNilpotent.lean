module

public import Mathlib
public import Formalism.LocalToGlobal.KernelLattices.FirstKernelLawReading
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.PeriodLatticeFinitelyGenerated
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Int.Lemmas
public import Init.Data.Int.Order
public import Init.Data.Nat.Basic
public import Init.Data.Nat.Coprime
public import Init.Data.Nat.Div.Basic
public import Init.Data.Nat.Gcd
public import Init.Data.Zero
public import Init.Omega.Coeffs
public import Init.Omega.Constraint
public import Init.Omega.Int
public import Init.Omega.LinearCombo
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.NonUnitalHom
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.Divisibility.Basic
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Conj
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Subsemigroup.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Inductions
public import Mathlib.Algebra.Quotient
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Logic.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Int.Cast.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Int.Cast.Lemmas
public import Mathlib.Data.Int.GCD
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.GroupTheory.Coset.Defs
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Basic
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Lattice
public import Mathlib.RingTheory.Ideal.Prime
public import Mathlib.RingTheory.Polynomial.Basic
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.L2.DIV Classical

namespace GlobalTheory.UnipVol

section Group

theorem index_eq_prime_pow {G : Type*} [Group G] (H : Subgroup G) [H.FiniteIndex] {p : ℕ} (hp : p.Prime)
    (hroot : ∀ (g : G) (m : ℕ), m.Coprime p → g ^ m ∈ H → g ∈ H) : ∃ k, H.index = p ^ k := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hN : ∀ (g : G) (m : ℕ), m.Coprime p → g ^ m ∈ H.normalCore → g ∈ H.normalCore := by
    intro g m hm hg
    have hg' : ∀ b : G, b * g ^ m * b⁻¹ ∈ H := hg
    show ∀ b : G, b * g * b⁻¹ ∈ H
    intro b
    refine hroot _ m hm ?_
    rw [conj_pow]
    exact hg' b
  have hfin : Finite (G ⧸ H.normalCore) := Subgroup.finite_quotient_of_finiteIndex
  have hP : IsPGroup p (G ⧸ H.normalCore) := by
    intro x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    have ho : orderOf (g : G ⧸ H.normalCore) ≠ 0 := (orderOf_pos _).ne'
    obtain ⟨s, m, hm, he⟩ := Nat.exists_eq_pow_mul_and_not_dvd ho p hp.ne_one
    refine ⟨s, ?_⟩
    have h1 : (g ^ p ^ s) ^ m ∈ H.normalCore := by
      rw [← QuotientGroup.eq_one_iff, ← pow_mul, QuotientGroup.mk_pow, ← he]
      exact pow_orderOf_eq_one _
    have h2 := hN _ m ((Nat.Prime.coprime_iff_not_dvd hp).2 hm).symm h1
    rw [← QuotientGroup.mk_pow]
    exact (QuotientGroup.eq_one_iff _).2 h2
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hP
  have h3 : H.index ∣ p ^ k := by
    rw [← hk]
    exact Subgroup.index_dvd_of_le (Subgroup.normalCore_le H)
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).1 h3
  exact ⟨j, hj⟩

end Group

section Poly

open Polynomial

theorem exists_one_add_X_pow (m : ℕ) : ∃ w : ℤ[X], (1 + X) ^ m - 1 = X * ((m : ℤ[X]) + X * w) := by
  induction m with
  | zero => exact ⟨0, by simp⟩
  | succ m ih =>
    obtain ⟨w, hw⟩ := ih
    refine ⟨(m : ℤ[X]) + w + X * w, ?_⟩
    have : (1 + X : ℤ[X]) ^ (m + 1) - 1 = (1 + X) * ((1 + X) ^ m - 1) + X := by ring
    rw [this, hw]
    push_cast
    ring

theorem exists_pow_expansion (m k : ℕ) :
    ∃ v : ℤ[X], ((1 + X : ℤ[X]) ^ m - 1) ^ k = (m : ℤ[X]) ^ k * X ^ k + X ^ (k + 1) * v := by
  obtain ⟨w, hw⟩ := exists_one_add_X_pow m
  obtain ⟨z, hz⟩ := sub_dvd_pow_sub_pow ((m : ℤ[X]) + X * w) (m : ℤ[X]) k
  refine ⟨w * z, ?_⟩
  rw [hw, mul_pow]
  have : ((m : ℤ[X]) + X * w) ^ k = (m : ℤ[X]) ^ k + ((m : ℤ[X]) + X * w - (m : ℤ[X])) * z := by rw [← hz]; ring
  rw [this]
  ring

theorem smul_mem_of_pow {A V : Type*} [Ring A] [AddCommGroup V] [Module A V] (M : AddSubgroup V) (ν : A) {d : ℕ}
    (hν : ν ^ d = 0) (m : ℕ) (hdiv : ∀ x, m • x ∈ M → x ∈ M)
    (hu : ∀ x ∈ M, ((1 + ν) ^ m - 1) • x ∈ M) : ∀ x ∈ M, ν • x ∈ M := by
  have hdivk : ∀ (k : ℕ) x, (m ^ k) • x ∈ M → x ∈ M := by
    intro k
    induction k with
    | zero => intro x hx; simpa using hx
    | succ k ih =>
      intro x hx
      refine hdiv x (ih _ ?_)
      rwa [smul_smul, ← pow_succ]
  have huk : ∀ (k : ℕ), ∀ x ∈ M, (((1 + ν) ^ m - 1) ^ k) • x ∈ M := by
    intro k
    induction k with
    | zero => intro x hx; simpa using hx
    | succ k ih =>
      intro x hx
      rw [pow_succ, mul_smul]
      exact ih _ (hu x hx)
  have key : ∀ j k, d ≤ k + j → ∀ (f : ℤ[X]), ∀ x ∈ M, (aeval ν (X ^ k * f)) • x ∈ M := by
    intro j
    induction j with
    | zero =>
      intro k hk f x _
      have : ν ^ k = 0 := pow_eq_zero_of_le (by omega) hν
      simp [this]
    | succ j ih =>
      intro k hk f x hx
      have h1 : (aeval ν (X ^ k : ℤ[X])) • x ∈ M := by
        obtain ⟨v, hv⟩ := exists_pow_expansion m k
        refine hdivk k _ ?_
        have h2 : aeval ν (((1 + X : ℤ[X]) ^ m - 1) ^ k) = ((1 + ν) ^ m - 1) ^ k := by simp
        have h3 := huk k x hx
        rw [← h2, hv, map_add (f := _), add_smul] at h3
        have h4 := ih (k + 1) (by omega) v x hx
        have h5 := M.sub_mem h3 h4
        rw [add_sub_cancel_right] at h5
        convert h5 using 1
        rw [map_mul, mul_smul, map_pow, map_pow, map_natCast, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul]
      have e : X ^ k * f = C (f.coeff 0) * X ^ k + X ^ (k + 1) * f.divX := by
        conv_lhs => rw [← divX_mul_X_add f]
        ring
      rw [e, map_add (f := _), add_smul]
      refine M.add_mem ?_ (ih (k + 1) (by omega) _ x hx)
      rw [map_mul, mul_smul, aeval_C]
      have : ∀ (a : ℤ) (y : V), y ∈ M → (algebraMap ℤ A a) • y ∈ M := by
        intro a y hy
        rw [eq_intCast, Int.cast_smul_eq_zsmul]
        exact M.zsmul_mem hy a
      exact this _ _ h1
  intro x hx
  simpa using key d 1 (by omega) 1 x hx

end Poly

section Unip

variable {k : Type} [CommRing k] {n c : ℕ}




end Unip

section Stab

variable {E : Type} [Field E] [NumberField E] [StarRing E]





theorem natCast_notMem {P : HeightOneSpectrum (𝓞 E)} {p m : ℕ} (hpP : (p : 𝓞 E) ∈ P.asIdeal) (hm : m.Coprime p) :
    (m : 𝓞 E) ∉ P.asIdeal := by
  intro h
  have h1 : (((m.gcd p : ℕ) : ℤ) : 𝓞 E) ∈ P.asIdeal := by
    rw [Nat.gcd_eq_gcd_ab]
    push_cast
    exact add_mem (Ideal.mul_mem_right _ _ h) (Ideal.mul_mem_right _ _ hpP)
  rw [hm.gcd_eq_one] at h1
  exact P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (by simpa using h1))


end Stab


end GlobalTheory.UnipVol
