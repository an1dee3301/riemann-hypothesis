module

public import Mathlib
public import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterUnramifiedAeAndExistsLevel
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.GlintPrincRelIndexNeZero
public import Init.Classical
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Int.Lemmas
public import Init.Data.Int.Order
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Omega.Coeffs
public import Init.Omega.Constraint
public import Init.Omega.Int
public import Init.Omega.LinearCombo
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Group.WithOne.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.GroupWithZero.WithZero
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Order.Group.Int
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Order.IsBotOne
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Monoid.TypeTags
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Algebra.Order.Monoid.Unbundled.TypeTags
public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Algebra.Order.ZeroLEOne
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Logic.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Range
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Lattice
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Nonunits
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.Valuation.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Valued.ValuationTopology

@[expose] public section

open NumberField IsDedekindDomain Formalism.L2.Host

namespace GlobalTheory.LocUnitPow

variable {L : Type} [Field L] [NumberField L]

theorem le_exp_neg_one' {γ : WithZero (Multiplicative ℤ)} (h : γ < 1) : γ ≤ WithZero.exp (-1 : ℤ) := by
  rcases eq_or_ne γ 0 with rfl | h0
  · exact zero_le
  · rw [← WithZero.exp_log h0] at h ⊢
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at h
    rw [WithZero.exp_le_exp]
    omega

theorem val_pow_sub_one_le {v : HeightOneSpectrum (𝓞 L)} {z : v.adicCompletion L} (hz : Valued.v z = 1) (i : ℕ) :
    Valued.v (z ^ i - 1) ≤ Valued.v (z - 1) := by
  induction i with
  | zero => simp
  | succ m ih =>
    have e : z ^ (m + 1) - 1 = z ^ m * (z - 1) + (z ^ m - 1) := by ring
    rw [e]
    refine Valuation.map_add_le _ ?_ ih
    rw [map_mul, map_pow, hz, one_pow, one_mul]

theorem val_pow_sub_one_step {v : HeightOneSpectrum (𝓞 L)} {N : ℕ}
    (hN : Valued.v (N : v.adicCompletion L) ≤ WithZero.exp (-1 : ℤ))
    {z : v.adicCompletion L} (hz : Valued.v z = 1) {j : ℤ} (hj : Valued.v (z - 1) ≤ WithZero.exp (-j)) (hj1 : 1 ≤ j) :
    Valued.v (z ^ N - 1) ≤ WithZero.exp (-(j + 1)) := by
  have e : z ^ N - 1 = (z - 1) * ((∑ i ∈ Finset.range N, (z ^ i - 1)) + (N : v.adicCompletion L)) := by
    rw [← geom_sum_mul, Finset.sum_sub_distrib]
    simp [mul_comm]
  have hS : Valued.v ((∑ i ∈ Finset.range N, (z ^ i - 1)) + (N : v.adicCompletion L)) ≤ WithZero.exp (-1 : ℤ) := by
    refine Valuation.map_add_le _ ?_ hN
    refine Valuation.map_sum_le _ fun i _ => ?_
    exact (val_pow_sub_one_le hz i).trans (hj.trans (WithZero.exp_le_exp.mpr (by omega)))
  rw [e, map_mul]
  calc _ ≤ WithZero.exp (-j) * WithZero.exp (-1 : ℤ) := mul_le_mul' hj hS
    _ = _ := by rw [← WithZero.exp_add]; congr 1; ring

theorem val_pow_pow_sub_one_le {v : HeightOneSpectrum (𝓞 L)} {N : ℕ}
    (hN : Valued.v (N : v.adicCompletion L) ≤ WithZero.exp (-1 : ℤ))
    {z : v.adicCompletion L} (hz : Valued.v z = 1) (hz1 : Valued.v (z - 1) ≤ WithZero.exp (-1 : ℤ)) (k : ℕ) :
    Valued.v (z ^ (N ^ k) - 1) ≤ WithZero.exp (-((k : ℤ) + 1)) := by
  induction k with
  | zero => simpa using hz1
  | succ k ih =>
    rw [pow_succ, pow_mul]
    have hzk : Valued.v (z ^ N ^ k) = 1 := by rw [map_pow, hz, one_pow]
    have := val_pow_sub_one_step hN hzk ih (by omega)
    convert this using 3
    push_cast
    ring

theorem loc_pow_eq_one : ∀ (L : Type) [Field L] [NumberField L] (χ : Formalism.L2.Host.HChar L) (v : HeightOneSpectrum (𝓞 L))
    (x : (v.adicCompletion L)ˣ), Formalism.L2.Host.IsUnitAt v x → ∃ m : ℕ, 0 < m ∧ χ.loc v x ^ m = 1 := by
  intro L _ _ χ v x hx
  obtain ⟨n, hn⟩ := GlobalTheory.Mem.UnrAe.exists_levelLe χ v
  have := Formalism.UG.P.glint_finite_residueField (F := L) v
  let _ := Fintype.ofFinite (IsLocalRing.ResidueField (v.adicCompletionIntegers L))
  set N := Fintype.card (IsLocalRing.ResidueField (v.adicCompletionIntegers L)) with hNdef
  have hN2 : 1 < N := Fintype.one_lt_card
  have hNv : Valued.v (N : v.adicCompletion L) ≤ WithZero.exp (-1 : ℤ) := by
    have hr : IsLocalRing.residue (v.adicCompletionIntegers L) (N : v.adicCompletionIntegers L) = 0 := by
      rw [map_natCast]; exact FiniteField.cast_card_eq_zero _
    rw [IsLocalRing.residue_eq_zero_iff] at hr
    have hlt : Valued.v (((N : v.adicCompletionIntegers L)) : v.adicCompletion L) < 1 :=
      (Valuation.mem_maximalIdeal_iff (v := (Valued.v : Valuation (v.adicCompletion L) (WithZero (Multiplicative ℤ))))).1 hr
    have e : (((N : v.adicCompletionIntegers L)) : v.adicCompletion L) = (N : v.adicCompletion L) := by
      push_cast; rfl
    rw [e] at hlt
    exact le_exp_neg_one' hlt
  have hxO : (x : v.adicCompletion L) ∈ v.adicCompletionIntegers L := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers]; exact hx.le
  set y : v.adicCompletionIntegers L := ⟨x, hxO⟩
  have hyu : IsUnit y := HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one.2 hx
  have hr : IsLocalRing.residue _ y ≠ 0 := by
    rw [ne_eq, IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not]
    exact hyu
  have hp : IsLocalRing.residue _ (y ^ (N - 1) - 1) = 0 := by
    rw [map_sub, map_pow, map_one, FiniteField.pow_card_sub_one_eq_one _ hr, sub_self]
  rw [IsLocalRing.residue_eq_zero_iff] at hp
  have hlt : Valued.v (((y ^ (N - 1) - 1 : v.adicCompletionIntegers L)) : v.adicCompletion L) < 1 :=
    (Valuation.mem_maximalIdeal_iff (v := (Valued.v : Valuation (v.adicCompletion L) (WithZero (Multiplicative ℤ))))).1 hp
  have e : (((y ^ (N - 1) - 1 : v.adicCompletionIntegers L)) : v.adicCompletion L) =
      (x : v.adicCompletion L) ^ (N - 1) - 1 := by
    push_cast; rfl
  rw [e] at hlt
  have hx1 := le_exp_neg_one' hlt
  have hz : Valued.v ((x : v.adicCompletion L) ^ (N - 1)) = 1 := by
    rw [map_pow, show Valued.v (x : v.adicCompletion L) = 1 from hx, one_pow]
  have key := val_pow_pow_sub_one_le hNv hz hx1 n
  refine ⟨(N - 1) * N ^ n, Nat.mul_pos (by omega) (pow_pos (by omega) _), ?_⟩
  rw [← map_pow]
  refine hn _ (GlobalTheory.Mem.UnrAe.isUnitAt_pow hx _) ?_
  rw [Units.val_pow_eq_pow_val, pow_mul]
  exact key.trans (WithZero.exp_le_exp.mpr (by omega))

end GlobalTheory.LocUnitPow
