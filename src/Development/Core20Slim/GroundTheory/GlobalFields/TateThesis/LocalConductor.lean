module

public import Mathlib
public import GroundTheory.GlobalFields.TateThesis.NoSmallSubgroups
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Int.Lemmas
public import Init.Data.Int.Order
public import Init.Data.Order.Lemmas
public import Init.Data.Zero
public import Init.Omega.Coeffs
public import Init.Omega.Constraint
public import Init.Omega.Int
public import Init.Omega.LinearCombo
public import Init.Omega.Logic
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Submonoid.Units
public import Mathlib.Algebra.Group.Subsemigroup.Defs
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Group.WithOne.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Algebra.GroupWithZero.Range
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.GroupWithZero.Units.Lemmas
public import Mathlib.Algebra.GroupWithZero.WithZero
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.Group.Int
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Range
public import Mathlib.Algebra.Order.GroupWithZero.WithZero
public import Mathlib.Algebra.Order.IsBotOne
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Monoid.TypeTags
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.TypeTags
public import Mathlib.Algebra.Order.Monoid.Units
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Nontrivial.Defs
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.Filter.Map
public import Mathlib.Order.Lattice
public import Mathlib.Order.Monotone.Defs
public import Mathlib.Order.Notation
public import Mathlib.Order.RelClasses
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.Valuation.Basic
public import Mathlib.RingTheory.Valuation.Discrete.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.GroupWithZero
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.OpenSubgroup
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.ValuativeRel.ValuativeTopology
public import Mathlib.Topology.Algebra.Valued.ValuationTopology
public import Mathlib.Topology.Algebra.Valued.ValuedField
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Maps.Basic
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

namespace GroundTheory.Global

open Topology Filter IsDedekindDomain WithZero

noncomputable section

theorem exists_le_ker_of_noSmallSubgroups {G H : Type*} [Group G] [TopologicalSpace G] [Group H]
    [TopologicalSpace H] {P : Subgroup G → Prop}
    (hP : ∀ W ∈ 𝓝 (1 : G), ∃ L : Subgroup G, P L ∧ (L : Set G) ⊆ W) (hH : NoSmallSubgroups H)
    (χ : G →* H) (hχ : Continuous χ) : ∃ L : Subgroup G, P L ∧ L ≤ χ.ker := by
  obtain ⟨U, hU, hsmall⟩ := hH
  have hW : χ ⁻¹' U ∈ 𝓝 (1 : G) := hχ.continuousAt.preimage_mem_nhds (by rwa [map_one])
  obtain ⟨L, hL, hLW⟩ := hP _ hW
  refine ⟨L, hL, ?_⟩
  rw [← Subgroup.map_eq_bot_iff]
  refine hsmall _ ?_
  rintro _ ⟨x, hx, rfl⟩
  exact hLW hx

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K]
  [IsFractionRing R K] (v : HeightOneSpectrum R)

def unitsLevel (n : ℕ) : Subgroup (v.adicCompletion K)ˣ where
  carrier := {x | Valued.v (x : v.adicCompletion K) = 1 ∧
    Valued.v ((x : v.adicCompletion K) - 1) ≤ exp (-(n : ℤ))}
  one_mem' := by simp
  mul_mem' {x y} hx hy := by
    refine ⟨by simp [hx.1, hy.1], ?_⟩
    have : ((x * y : (v.adicCompletion K)ˣ) : v.adicCompletion K) - 1 =
        (x : v.adicCompletion K) * ((y : v.adicCompletion K) - 1) +
          ((x : v.adicCompletion K) - 1) := by
      push_cast; ring
    rw [this]
    refine Valuation.map_add_le _ ?_ hx.2
    rw [map_mul, hx.1, one_mul]
    exact hy.2
  inv_mem' {x} hx := by
    have hx0 : (x : v.adicCompletion K) ≠ 0 := x.ne_zero
    refine ⟨by simp [hx.1], ?_⟩
    have : ((x⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) - 1 =
        (x : v.adicCompletion K)⁻¹ * (1 - (x : v.adicCompletion K)) := by
      rw [Units.val_inv_eq_inv_val, mul_sub, mul_one, inv_mul_cancel₀ hx0]
    rw [this, map_mul, map_inv₀, hx.1, inv_one, one_mul, Valuation.map_sub_swap]
    exact hx.2

variable {v} in
theorem mem_unitsLevel {n : ℕ} {x : (v.adicCompletion K)ˣ} :
    x ∈ unitsLevel v n ↔ Valued.v (x : v.adicCompletion K) = 1 ∧
      Valued.v ((x : v.adicCompletion K) - 1) ≤ exp (-(n : ℤ)) :=
  Iff.rfl



theorem unitsLevel_zero :
    unitsLevel (K := K) v 0 = (Submonoid.ofClass (v.adicCompletionIntegers K)).units := by
  ext x
  rw [Submonoid.mem_units_iff, mem_unitsLevel]
  change _ ↔ (x : v.adicCompletion K) ∈ v.adicCompletionIntegers K ∧
    ((x⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) ∈ v.adicCompletionIntegers K
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, HeightOneSpectrum.mem_adicCompletionIntegers,
    Units.val_inv_eq_inv_val, map_inv₀]
  constructor
  · rintro ⟨h1, -⟩
    simp [h1]
  · rintro ⟨h1, h2⟩
    have hx0 : Valued.v (x : v.adicCompletion K) ≠ 0 := by simp
    have h3 : 1 ≤ Valued.v (x : v.adicCompletion K) := by
      exact (inv_le_one₀ (zero_lt_iff.2 hx0)).1 h2
    refine ⟨le_antisymm h1 h3, ?_⟩
    rw [Nat.cast_zero, neg_zero, exp_zero]
    exact Valuation.map_sub_le _ h1 (by simp)

theorem unitsLevel_antitone : Antitone (unitsLevel (K := K) v) := by
  intro m n hmn x hx
  refine ⟨hx.1, hx.2.trans ?_⟩
  rw [exp_le_exp]
  omega

theorem isOpen_unitsLevel (n : ℕ) : IsOpen (unitsLevel (K := K) v n : Set (v.adicCompletion K)ˣ) := by
  refine Subgroup.isOpen_of_mem_nhds (g := 1) _ ?_
  obtain ⟨a, ha⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective (K := K) (v := v)
    (exp (-(n : ℤ)))
  have ha0 : Valued.v a ≠ 0 := by simp [ha]
  have h1 : {y : v.adicCompletion K | Valued.v y = 1} ∈ 𝓝 (1 : v.adicCompletion K) := by
    simpa using Valued.locally_const (x := (1 : v.adicCompletion K)) (by simp)
  have h2 : {y : v.adicCompletion K | Valued.v (y - 1) ≤ exp (-(n : ℤ))} ∈
      𝓝 (1 : v.adicCompletion K) := by
    have hc : Continuous fun y : v.adicCompletion K ↦ y - 1 + a :=
      (continuous_id.sub continuous_const).add continuous_const
    have h := hc.continuousAt.preimage_mem_nhds (x := (1 : v.adicCompletion K))
      (by simpa using Valued.locally_const (x := a) ha0)
    refine Filter.mem_of_superset h fun y hy ↦ ?_
    have hy' : Valued.v (y - 1 + a) = exp (-(n : ℤ)) := by rw [← ha]; exact hy
    have : y - 1 = (y - 1 + a) - a := by ring
    change Valued.v (y - 1) ≤ exp (-(n : ℤ))
    rw [this]
    exact Valuation.map_sub_le _ hy'.le ha.le
  have h3 := Units.continuous_val.continuousAt.preimage_mem_nhds (x := (1 : (v.adicCompletion K)ˣ))
    (by rw [Units.val_one]; exact Filter.inter_mem h1 h2)
  exact Filter.mem_of_superset h3 fun x hx ↦ hx

theorem exists_unitsLevel_subset {t : Set (v.adicCompletion K)ˣ} (ht : t ∈ 𝓝 1) :
    ∃ n : ℕ, 1 ≤ n ∧ (unitsLevel (K := K) v n : Set (v.adicCompletion K)ˣ) ⊆ t := by
  rw [Units.isEmbedding_val₀.nhds_eq_comap, Units.val_one, mem_comap] at ht
  obtain ⟨t', ht', hsub⟩ := ht
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds.1 ht'
  set c := MonoidWithZeroHom.ValueGroup₀.embedding γ.1 with hc
  have hc0 : c ≠ 0 := fun h ↦ γ.ne_zero
    (MonoidWithZeroHom.ValueGroup₀.embedding_injective (h.trans (map_zero _).symm))
  refine ⟨(-(log c)).toNat + 1, by omega, fun x hx ↦ hsub (hγ ?_)⟩
  change Valued.v.restrict ((x : v.adicCompletion K) - 1) < γ.1
  rw [Valuation.restrict_lt_iff_lt_embedding, ← hc]
  refine hx.2.trans_lt (lt_of_lt_of_eq ?_ (exp_log hc0))
  rw [exp_lt_exp]
  omega

section Character

variable {H : Type*} [Group H] [TopologicalSpace H]






end Character

end

end GroundTheory.Global
