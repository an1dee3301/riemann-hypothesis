module

public import Mathlib
public import Development.Core20Slim.GroundTheory.GlobalFields.IdeleGroups.ClassGroup
public import Development.Core20Slim.GroundTheory.GlobalFields.IdeleGroups.InfiniteProjInfiniteEmbeddingOfNe
public import Init.Classical
public import Init.Core
public import Init.Data.Function
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Submonoid.Operations
public import Mathlib.Algebra.Group.Subsemigroup.Defs
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Group.WithOne.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.GroupWithZero.WithZero
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Order.Monoid.TypeTags
public import Mathlib.Algebra.Order.Monoid.Unbundled.TypeTags
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.Ring.Int
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Union
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.ClassNumber
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.Order.Basic
public import Mathlib.Order.BoundedOrder.Basic
public import Mathlib.Order.CompleteLattice.Defs
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Defs
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Filter.Cofinite
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.Lattice
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.ClassGroup.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Valuation
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.DedekindDomain.SInteger
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.Valuation.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring

set_option synthInstance.maxHeartbeats 400000

@[expose] public section

namespace GroundTheory.Global

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero FractionalIdeal
open scoped NumberField.AdeleRing nonZeroDivisors

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

namespace IdeleGroup

def sIdeles (S : Set (HeightOneSpectrum (𝓞 K))) : Subgroup (IdeleGroup K) where
  carrier := {x | ∀ v ∉ S, ord v x = 0}
  one_mem' v _ := ord_one v
  mul_mem' {x y} hx hy v hv := by rw [ord_mul, hx v hv, hy v hv, add_zero]
  inv_mem' {x} hx v hv := by rw [ord_inv, hx v hv, neg_zero]

variable (S : Set (HeightOneSpectrum (𝓞 K)))

theorem mem_sIdeles {x : IdeleGroup K} : x ∈ sIdeles S ↔ ∀ v ∉ S, ord v x = 0 :=
  Iff.rfl

theorem mem_sIdeles_iff {x : IdeleGroup K} :
    x ∈ sIdeles S ↔ ∀ v ∉ S, (x : 𝔸[K]).2 v ∈ v.adicCompletionIntegers K ∧
      ((x⁻¹ : IdeleGroup K) : 𝔸[K]).2 v ∈ v.adicCompletionIntegers K := by
  simp only [mem_sIdeles, ord_eq_zero_iff]

theorem standardOpenSubgroup_le_sIdeles : standardOpenSubgroup K ≤ sIdeles S :=
  fun _ hx v _ ↦ mem_standardOpenSubgroup_iff_ord.1 hx v

theorem sIdeles_mono {S T : Set (HeightOneSpectrum (𝓞 K))} (h : S ⊆ T) :
    sIdeles S ≤ sIdeles T :=
  fun _ hx v hv ↦ hx v fun hvS ↦ hv (h hvS)

theorem neg_log_eq_zero_iff {y : ℤᵐ⁰} (hy : y ≠ 0) : -log y = 0 ↔ y = 1 := by
  rw [neg_eq_zero]
  constructor
  · intro h
    rw [← exp_log hy, h, exp_zero]
  · rintro rfl
    exact log_one

theorem diagonal_mem_sIdeles_iff (a : Kˣ) : diagonal K a ∈ sIdeles S ↔ a ∈ S.unit K := by
  have ha : ∀ v : HeightOneSpectrum (𝓞 K), v.valuation K (a : K) ≠ 0 := fun v ↦
    (Valuation.ne_zero_iff _).2 a.ne_zero
  simp only [mem_sIdeles, ord_diagonal, neg_log_eq_zero_iff (ha _)]
  rfl

theorem exists_diagonal_mul_of_sup_eq_top (h : (diagonal K).range ⊔ sIdeles S = ⊤)
    (x : IdeleGroup K) : ∃ a : Kˣ, ∃ s ∈ sIdeles S, diagonal K a * s = x := by
  have hx : x ∈ (diagonal K).range ⊔ sIdeles S := h ▸ Subgroup.mem_top x
  obtain ⟨_, ⟨a, rfl⟩, s, hs, hx⟩ := Subgroup.mem_sup.1 hx
  exact ⟨a, s, hs, hx⟩

theorem sup_sIdeles_eq_top_of_subset {S T : Set (HeightOneSpectrum (𝓞 K))} (hST : S ⊆ T)
    (h : (diagonal K).range ⊔ sIdeles S = ⊤) : (diagonal K).range ⊔ sIdeles T = ⊤ :=
  eq_top_iff.2 (h.symm.le.trans (sup_le_sup_left (sIdeles_mono hST) _))

theorem exists_finset_sup_sIdeles_eq_top :
    ∃ S : Finset (HeightOneSpectrum (𝓞 K)),
      (diagonal K).range ⊔ sIdeles (S : Set (HeightOneSpectrum (𝓞 K))) = ⊤ := by
  classical
  choose x hx using toClassGroup_surjective (K := K)
  let S : Finset (HeightOneSpectrum (𝓞 K)) := Finset.univ.biUnion fun c ↦
    (Filter.eventually_cofinite.1 (eventually_ord_eq_zero (x c))).toFinset
  have hxS : ∀ c, x c ∈ sIdeles (S : Set (HeightOneSpectrum (𝓞 K))) := by
    intro c v hv
    by_contra h
    exact hv (Finset.mem_biUnion.2 ⟨c, Finset.mem_univ c, Set.Finite.mem_toFinset _ |>.2 h⟩)
  refine ⟨S, eq_top_iff.2 fun y _ ↦ ?_⟩
  have hker : y * (x (toClassGroup y))⁻¹ ∈ (toClassGroup (K := K)).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hx, mul_inv_cancel]
  rw [ker_toClassGroup] at hker
  have h := mul_mem (sup_le_sup_left (standardOpenSubgroup_le_sIdeles _) _ hker)
    (Subgroup.mem_sup_right (hxS (toClassGroup y)))
  rwa [inv_mul_cancel_right] at h

def sUnitsToSIdeles : S.unit K →* sIdeles S :=
  ((diagonal K).comp (S.unit K).subtype).codRestrict (sIdeles S) fun a ↦
    (diagonal_mem_sIdeles_iff S a).2 a.2

@[simp]
theorem coe_sUnitsToSIdeles (a : S.unit K) :
    (sUnitsToSIdeles S a : IdeleGroup K) = diagonal K a :=
  rfl

def sIdelesToIdeleClassGroup : sIdeles S →* IdeleClassGroup K :=
  (IdeleClassGroup.mk K).comp (sIdeles S).subtype

@[simp]
theorem sIdelesToIdeleClassGroup_apply (s : sIdeles S) :
    sIdelesToIdeleClassGroup S s = IdeleClassGroup.mk K s :=
  rfl

theorem sUnitsToSIdeles_injective : Function.Injective (sUnitsToSIdeles S) := fun _ _ h ↦
  Subtype.ext (diagonal_injective K (congrArg Subtype.val h))

theorem range_sUnitsToSIdeles :
    (sUnitsToSIdeles S).range = (sIdelesToIdeleClassGroup S).ker := by
  ext y
  constructor
  · rintro ⟨a, rfl⟩
    rw [MonoidHom.mem_ker, sIdelesToIdeleClassGroup_apply, coe_sUnitsToSIdeles]
    exact IdeleClassGroup.mk_diagonal K a
  · intro hy
    rw [MonoidHom.mem_ker, sIdelesToIdeleClassGroup_apply, ← MonoidHom.mem_ker,
      IdeleClassGroup.ker_mk] at hy
    obtain ⟨a, ha⟩ := hy
    have haS : a ∈ S.unit K := (diagonal_mem_sIdeles_iff S a).1 (ha ▸ y.2)
    exact ⟨⟨a, haS⟩, Subtype.ext ha⟩

theorem sIdelesToIdeleClassGroup_surjective_iff :
    Function.Surjective (sIdelesToIdeleClassGroup S) ↔ (diagonal K).range ⊔ sIdeles S = ⊤ := by
  constructor
  · intro h
    refine eq_top_iff.2 fun y _ ↦ ?_
    obtain ⟨s, hs⟩ := h (IdeleClassGroup.mk K y)
    rw [sIdelesToIdeleClassGroup_apply] at hs
    have hr : (s : IdeleGroup K)⁻¹ * y ∈ (diagonal K).range := by
      rw [← IdeleClassGroup.ker_mk, MonoidHom.mem_ker, map_mul, map_inv, hs, inv_mul_cancel]
    have h' := mul_mem (Subgroup.mem_sup_right (S := (diagonal K).range) s.2)
      (Subgroup.mem_sup_left (T := sIdeles S) hr)
    rwa [mul_inv_cancel_left] at h'
  · intro h c
    obtain ⟨y, rfl⟩ := IdeleClassGroup.mk_surjective K c
    obtain ⟨a, s, hs, rfl⟩ := exists_diagonal_mul_of_sup_eq_top S h y
    refine ⟨⟨s, hs⟩, ?_⟩
    rw [sIdelesToIdeleClassGroup_apply, map_mul, IdeleClassGroup.mk_diagonal]
    exact (one_mul (IdeleClassGroup.mk K s)).symm

theorem sUnits_sIdeles_exact (h : (diagonal K).range ⊔ sIdeles S = ⊤) :
    Function.Injective (sUnitsToSIdeles S) ∧
      (sUnitsToSIdeles S).range = (sIdelesToIdeleClassGroup S).ker ∧
      Function.Surjective (sIdelesToIdeleClassGroup S) :=
  ⟨sUnitsToSIdeles_injective S, range_sUnitsToSIdeles S,
    (sIdelesToIdeleClassGroup_surjective_iff S).2 h⟩

end IdeleGroup

end

end GroundTheory.Global
