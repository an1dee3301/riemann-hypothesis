module

public import Mathlib
public import Development.Core20Slim.GroundTheory.GlobalFields.LocalFieldAtPlace
public import Development.Core20Slim.GroundTheory.GlobalFields.KummerTheory.LocalIndex
public import Development.Core20Slim.GroundTheory.GlobalFields.LocalAtPlace
public import GroundTheory.LocalFields.UnitsBasic
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.NeZero
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.IsField
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Group.Even
public import Mathlib.Algebra.Group.Hom.Basic
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Irreducible.Defs
public import Mathlib.Algebra.Group.Irreducible.Lemmas
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Even
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.Algebra.Group.WithOne.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.GroupWithZero.WithZero
public import Mathlib.Algebra.Notation.Prod
public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.Algebra.Order.Group.Unbundled.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Order.Kleene
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
public import Mathlib.Algebra.Order.Ring.Basic
public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Equiv
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Algebra.Ring.Units
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Logic.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.Real.Star
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.GroupTheory.Index
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Mathlib.Order.Basic
public import Mathlib.Order.BoundedOrder.Basic
public import Mathlib.Order.CompleteLattice.Defs
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.RootsOfUnity.Basic
public import Mathlib.RingTheory.RootsOfUnity.EnoughRootsOfUnity
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.Valuation.Basic
public import Mathlib.RingTheory.Valuation.Integers
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.RingTheory.Valuation.ValuativeRel.Basic
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Tactic.Linarith.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Valued.ValuationTopology
public import Mathlib.Topology.UniformSpace.Defs

set_option synthInstance.maxHeartbeats 400000

@[expose] public section

namespace GroundTheory.Global

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField ValuativeRel
  GroundTheory.LocalField

section FinitePlace

variable {K : Type*} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

theorem coe_mem_adicCompletionIntegers (x : 𝒪[v.adicCompletion K]) :
    (x : v.adicCompletion K) ∈ v.adicCompletionIntegers K :=
  (mem_valuationInteger_iff v (x : v.adicCompletion K)).1 x.2

theorem coe_mem_valuationInteger (x : v.adicCompletionIntegers K) :
    (x : v.adicCompletion K) ∈ 𝒪[v.adicCompletion K] :=
  (mem_valuationInteger_iff v (x : v.adicCompletion K)).2 x.2

def integerEquivAdicCompletionIntegers :
    𝒪[v.adicCompletion K] ≃+* v.adicCompletionIntegers K where
  toFun x := ⟨x, coe_mem_adicCompletionIntegers v x⟩
  invFun x := ⟨x, coe_mem_valuationInteger v x⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

@[simp]
theorem coe_integerEquivAdicCompletionIntegers (x : 𝒪[v.adicCompletion K]) :
    ((integerEquivAdicCompletionIntegers v x : v.adicCompletionIntegers K) :
      v.adicCompletion K) = x :=
  rfl

theorem natCard_residueField_adicCompletion :
    Nat.card 𝓀[v.adicCompletion K] = Ideal.absNorm v.asIdeal := by
  rw [← natCard_residueField_adicCompletionIntegers v]
  exact Nat.card_congr
    (IsLocalRing.ResidueField.mapEquiv (integerEquivAdicCompletionIntegers v)).toEquiv

theorem norm_eq_absNorm_zpow_neg_ord {x : v.adicCompletion K} (hx : x ≠ 0) :
    ‖x‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ (-ord x) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[v.adicCompletion K]
  set p := unitsEquivIntProd hϖ (Units.mk0 x hx)
  have hxp : x = ((ϖ : v.adicCompletion K)) ^ (Multiplicative.toAdd p.1) *
      ((p.2 : 𝒪[v.adicCompletion K]) : v.adicCompletion K) := by
    rw [← coe_unitsOfIntProd hϖ, ← unitsEquivIntProd_symm_apply hϖ, MulEquiv.symm_apply_apply]
    rfl
  have hord : Multiplicative.toAdd p.1 = ord x := by
    rw [unitsEquivIntProd_fst hϖ]
    rfl
  have hϖ' : Irreducible (integerEquivAdicCompletionIntegers v ϖ) :=
    hϖ.map (integerEquivAdicCompletionIntegers v)
  have hnϖ : ‖(ϖ : v.adicCompletion K)‖ = (Ideal.absNorm v.asIdeal : ℝ)⁻¹ := by
    have h := normalizedAbv_of_irreducible v hϖ'
    rw [normalizedAbv_apply, coe_integerEquivAdicCompletionIntegers] at h
    exact h
  have hu : ‖((p.2 : 𝒪[v.adicCompletion K]) : v.adicCompletion K)‖ = 1 := by
    have hunit : IsUnit (integerEquivAdicCompletionIntegers v p.2) :=
      p.2.isUnit.map (integerEquivAdicCompletionIntegers v)
    have h1 := (adicCompletionIntegers.isUnit_iff_valued_eq_one).1 hunit
    have h0 : ((p.2 : 𝒪[v.adicCompletion K]) : v.adicCompletion K) ≠ 0 := by
      exact_mod_cast p.2.ne_zero
    rw [← normalizedAbv_apply, normalizedAbv_eq_zpow v h0]
    rw [coe_integerEquivAdicCompletionIntegers] at h1
    rw [h1]
    simp
  conv_lhs => rw [hxp]
  rw [norm_mul, norm_zpow, hnϖ, hu, mul_one, hord, inv_zpow']

variable {v}

theorem natCast_ne_zero_adicCompletion {n : ℕ} (hn : n ≠ 0) :
    (n : v.adicCompletion K) ≠ 0 := by
  rw [← map_natCast (algebraMap K (v.adicCompletion K)), ne_eq,
    map_eq_zero_iff _ (algebraMap K (v.adicCompletion K)).injective]
  exact_mod_cast hn

variable (v)

theorem index_range_powMonoidHom_adicCompletion {n : ℕ} (hn : n ≠ 0) :
    ((powMonoidHom n : (v.adicCompletion K)ˣ →* (v.adicCompletion K)ˣ).range.index : ℝ) =
      n * Nat.card (rootsOfUnity n (v.adicCompletion K)) / ‖(n : v.adicCompletion K)‖ := by
  have hn' := natCast_ne_zero_adicCompletion (v := v) hn
  rw [index_range_powMonoidHom hn', natCard_residueField_adicCompletion,
    norm_eq_absNorm_zpow_neg_ord v hn', zpow_neg, div_inv_eq_mul]

theorem index_range_powMonoidHom_adicCompletion_of_hasEnoughRootsOfUnity {n : ℕ} [NeZero n]
    [HasEnoughRootsOfUnity (v.adicCompletion K) n] :
    ((powMonoidHom n : (v.adicCompletion K)ˣ →* (v.adicCompletion K)ˣ).range.index : ℝ) =
      n ^ 2 / ‖(n : v.adicCompletion K)‖ := by
  rw [index_range_powMonoidHom_adicCompletion v (NeZero.ne n),
    HasEnoughRootsOfUnity.natCard_rootsOfUnity, sq]


end FinitePlace

section Archimedean

theorem exists_pos_real_pow_eq {x : ℝ} (hx : 0 < x) {n : ℕ} (hn : n ≠ 0) :
    ∃ y : ℝ, 0 < y ∧ y ^ n = x :=
  ⟨x ^ (n⁻¹ : ℝ), Real.rpow_pos_of_pos hx _, Real.rpow_inv_natCast_pow hx.le hn⟩

theorem mem_range_powMonoidHom_real_iff_of_even {n : ℕ} (hn : n ≠ 0) (he : Even n) (x : ℝˣ) :
    x ∈ (powMonoidHom n : ℝˣ →* ℝˣ).range ↔ 0 < (x : ℝ) := by
  rw [MonoidHom.mem_range]
  constructor
  · rintro ⟨y, rfl⟩
    rw [powMonoidHom_apply, Units.val_pow_eq_pow_val]
    exact he.pow_pos y.ne_zero
  · intro hx
    obtain ⟨y, hy, hyx⟩ := exists_pos_real_pow_eq hx hn
    refine ⟨Units.mk0 y hy.ne', ?_⟩
    ext
    rw [powMonoidHom_apply, Units.val_pow_eq_pow_val, Units.val_mk0, hyx]

theorem range_powMonoidHom_real_of_odd {n : ℕ} (ho : Odd n) :
    (powMonoidHom n : ℝˣ →* ℝˣ).range = ⊤ := by
  have hn : n ≠ 0 := by rintro rfl; simp at ho
  refine eq_top_iff.2 fun x _ ↦ ?_
  rw [MonoidHom.mem_range]
  rcases lt_or_gt_of_ne x.ne_zero with hx | hx
  · obtain ⟨y, hy, hyx⟩ := exists_pos_real_pow_eq (neg_pos.2 hx) hn
    refine ⟨Units.mk0 (-y) (neg_ne_zero.2 hy.ne'), ?_⟩
    ext
    rw [powMonoidHom_apply, Units.val_pow_eq_pow_val, Units.val_mk0, ho.neg_pow, hyx, neg_neg]
  · obtain ⟨y, hy, hyx⟩ := exists_pos_real_pow_eq hx hn
    refine ⟨Units.mk0 y hy.ne', ?_⟩
    ext
    rw [powMonoidHom_apply, Units.val_pow_eq_pow_val, Units.val_mk0, hyx]

theorem index_range_powMonoidHom_real_of_even {n : ℕ} (hn : n ≠ 0) (he : Even n) :
    (powMonoidHom n : ℝˣ →* ℝˣ).range.index = 2 := by
  rw [Subgroup.index_eq_two_iff]
  refine ⟨-1, fun b ↦ ?_⟩
  rw [mem_range_powMonoidHom_real_iff_of_even hn he, mem_range_powMonoidHom_real_iff_of_even hn he,
    Units.val_mul, Units.val_neg, Units.val_one, mul_neg_one]
  rcases lt_or_gt_of_ne b.ne_zero with hb | hb
  · exact Or.inl ⟨neg_pos.2 hb, hb.not_gt⟩
  · exact Or.inr ⟨hb, by linarith⟩

theorem index_range_powMonoidHom_real_of_odd {n : ℕ} (ho : Odd n) :
    (powMonoidHom n : ℝˣ →* ℝˣ).range.index = 1 := by
  rw [range_powMonoidHom_real_of_odd ho, Subgroup.index_top]

theorem index_range_powMonoidHom_real {n : ℕ} (hn : n ≠ 0) :
    (powMonoidHom n : ℝˣ →* ℝˣ).range.index = if Even n then 2 else 1 := by
  split_ifs with he
  · exact index_range_powMonoidHom_real_of_even hn he
  · exact index_range_powMonoidHom_real_of_odd (Nat.not_even_iff_odd.1 he)

theorem range_powMonoidHom_complex {n : ℕ} (hn : n ≠ 0) :
    (powMonoidHom n : ℂˣ →* ℂˣ).range = ⊤ := by
  refine eq_top_iff.2 fun x _ ↦ ?_
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (x : ℂ) (Nat.pos_of_ne_zero hn)
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [zero_pow hn] at hz
    exact x.ne_zero hz.symm
  refine ⟨Units.mk0 z hz0, ?_⟩
  ext
  rw [powMonoidHom_apply, Units.val_pow_eq_pow_val, Units.val_mk0, hz]

theorem index_range_powMonoidHom_complex {n : ℕ} (hn : n ≠ 0) :
    (powMonoidHom n : ℂˣ →* ℂˣ).range.index = 1 := by
  rw [range_powMonoidHom_complex hn, Subgroup.index_top]

end Archimedean

end GroundTheory.Global
