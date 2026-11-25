module

public import Mathlib
public import GroundTheory.GlobalFields.SUnits
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Int.Lemmas
public import Init.Data.Int.Order
public import Init.Data.Nat.Basic
public import Init.Data.Nat.Div.Basic
public import Init.Data.Nat.Gcd
public import Init.Data.NeZero
public import Init.Data.Zero
public import Init.Omega.Coeffs
public import Init.Omega.Constraint
public import Init.Omega.Int
public import Init.Omega.LinearCombo
public import Init.Prelude
public import Mathlib.Algebra.EuclideanDomain.Int
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Basic
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Algebra.Module.Torsion.Free
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Order.IsBotOne
public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Algebra.Quotient
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Set.CoeSort
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Subtype
public import Mathlib.GroupTheory.Coset.Defs
public import Mathlib.GroupTheory.Finiteness
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.IndexNSmul
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.GroupTheory.Torsion
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Dimension.Torsion.Basic
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
public import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
public import Mathlib.Order.CompleteLattice.Defs
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Defs
public import Mathlib.Order.Defs.Lattice
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.DedekindDomain.SInteger
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.PrincipalIdealDomain
public import Mathlib.RingTheory.RootsOfUnity.EnoughRootsOfUnity
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.SetTheory.Cardinal.Finite

set_option synthInstance.maxHeartbeats 400000

@[expose] public section

namespace GroundTheory.Global

open NumberField IsDedekindDomain Module

noncomputable section

section PowerIndex

variable {G : Type*} [CommGroup G]

theorem mem_torsion_of_pow_mem_torsion {n : ℕ} (hn : n ≠ 0) {x : G}
    (hx : x ^ n ∈ CommGroup.torsion G) : x ∈ CommGroup.torsion G := by
  rw [CommGroup.mem_torsion] at hx ⊢
  exact (isOfFinOrder_pow.1 hx).resolve_right hn

theorem range_powMonoidHom_subgroupOf_torsion {n : ℕ} (hn : n ≠ 0) :
    (powMonoidHom n : G →* G).range.subgroupOf (CommGroup.torsion G) =
      (powMonoidHom n : CommGroup.torsion G →* CommGroup.torsion G).range := by
  ext ⟨t, ht⟩
  rw [Subgroup.mem_subgroupOf, MonoidHom.mem_range, MonoidHom.mem_range]
  constructor
  · rintro ⟨x, hx⟩
    rw [powMonoidHom_apply] at hx
    refine ⟨⟨x, mem_torsion_of_pow_mem_torsion hn ?_⟩, Subtype.ext ?_⟩
    · rw [hx]
      exact ht
    · exact hx
  · rintro ⟨x, hx⟩
    exact ⟨x, congrArg Subtype.val hx⟩

theorem range_powMonoidHom_sup_torsion (n : ℕ) :
    (powMonoidHom n : G →* G).range ⊔ CommGroup.torsion G =
      (powMonoidHom n : G ⧸ CommGroup.torsion G →* G ⧸ CommGroup.torsion G).range.comap
        (QuotientGroup.mk' (CommGroup.torsion G)) := by
  ext x
  simp only [Subgroup.mem_comap, MonoidHom.mem_range, powMonoidHom_apply]
  constructor
  · intro hx
    obtain ⟨_, ⟨b, rfl⟩, t, ht, rfl⟩ := Subgroup.mem_sup.1 hx
    refine ⟨QuotientGroup.mk' _ b, ?_⟩
    have h1 : QuotientGroup.mk' (CommGroup.torsion G) t = 1 := (QuotientGroup.eq_one_iff t).2 ht
    rw [map_mul, h1, mul_one, powMonoidHom_apply, map_pow]
  · rintro ⟨q, hq⟩
    obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective (CommGroup.torsion G) q
    have ht : (b ^ n)⁻¹ * x ∈ CommGroup.torsion G := by
      rw [← QuotientGroup.eq]
      rw [← map_pow] at hq
      exact hq
    have h := Subgroup.mul_mem_sup (S := (powMonoidHom n : G →* G).range)
      (T := CommGroup.torsion G) ⟨b, rfl⟩ ht
    rwa [powMonoidHom_apply, mul_inv_cancel_left] at h

instance finite_additive_quotient_torsion [Group.FG G] :
    Module.Finite ℤ (Additive (G ⧸ CommGroup.torsion G)) := by
  rw [Module.Finite.iff_addGroup_fg, AddGroup.fg_iff_addMonoid_fg, ← Monoid.fg_iff_add_fg,
    ← Group.fg_iff_monoid_fg]
  infer_instance

theorem index_range_powMonoidHom_eq_pow_mul [Group.FG G] {n : ℕ} (hn : n ≠ 0) :
    (powMonoidHom n : G →* G).range.index =
      n ^ finrank ℤ (Additive (G ⧸ CommGroup.torsion G)) *
        (powMonoidHom n : CommGroup.torsion G →* CommGroup.torsion G).range.index := by
  set T := CommGroup.torsion G
  set N := (powMonoidHom n : G →* G).range
  have hQ : (powMonoidHom n : G ⧸ T →* G ⧸ T).range.index =
      n ^ finrank ℤ (Additive (G ⧸ T)) :=
    AddSubgroup.index_range_nsmul (Additive (G ⧸ T)) n
  have hsup : (N ⊔ T).index = n ^ finrank ℤ (Additive (G ⧸ T)) := by
    rw [range_powMonoidHom_sup_torsion, Subgroup.index_comap_of_surjective _
      (QuotientGroup.mk'_surjective T), hQ]
  have hrel : N.relIndex T = (powMonoidHom n : T →* T).range.index := by
    rw [Subgroup.relIndex, range_powMonoidHom_subgroupOf_torsion hn]
  rw [← Subgroup.relIndex_mul_index (le_sup_left : N ≤ N ⊔ T), Subgroup.relIndex_sup_left, hrel,
    hsup, mul_comm]

end PowerIndex

section SUnit

variable {K : Type*} [Field K] [NumberField K] (S : Set (HeightOneSpectrum (𝓞 K)))

namespace SUnit

theorem finrank_quotient_torsion [Finite S] :
    finrank ℤ (Additive (S.unit K ⧸ CommGroup.torsion (S.unit K))) = Units.rank K + Nat.card S := by
  rw [← finrank_eq S]
  exact finrank_quotient_torsion_eq (M := Additive (S.unit K))

theorem dvd_natCard_torsion (n : ℕ) [NeZero n] [HasEnoughRootsOfUnity K n] :
    n ∣ Nat.card (CommGroup.torsion (S.unit K)) := by
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot K n
  set u : Kˣ := (hζ.isUnit (NeZero.ne n)).unit
  have hu : IsPrimitiveRoot u n := IsPrimitiveRoot.coe_units_iff.1 hζ
  have hfin : IsOfFinOrder u := by
    rw [← orderOf_pos_iff, ← hu.eq_orderOf]
    exact NeZero.pos n
  let u' : S.unit K := ⟨u, fun v _ ↦ valuation_eq_one_of_isOfFinOrder hfin v⟩
  have hfin' : IsOfFinOrder u' := by
    rw [← orderOf_pos_iff, ← orderOf_injective (S.unit K).subtype Subtype.val_injective]
    exact orderOf_pos_iff.mpr hfin
  let t : CommGroup.torsion (S.unit K) := ⟨u', hfin'⟩
  have ht : orderOf t = n := by
    rw [← orderOf_injective (CommGroup.torsion (S.unit K)).subtype Subtype.val_injective,
      ← orderOf_injective (S.unit K).subtype Subtype.val_injective]
    exact hu.eq_orderOf.symm
  rw [← ht]
  exact orderOf_dvd_natCard t

theorem index_range_powMonoidHom (n : ℕ) [NeZero n] [HasEnoughRootsOfUnity K n] [Finite S] :
    (powMonoidHom n : S.unit K →* S.unit K).range.index =
      n ^ (Fintype.card (InfinitePlace K) + Nat.card S) := by
  have hpos : 0 < InfinitePlace.nrRealPlaces K + InfinitePlace.nrComplexPlaces K := by
    rw [← InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces]
    exact Fintype.card_pos
  rw [index_range_powMonoidHom_eq_pow_mul (NeZero.ne n), finrank_quotient_torsion,
    IsCyclic.index_powMonoidHom_range, Nat.gcd_eq_right (dvd_natCard_torsion S n), ← pow_succ,
    Units.rank, InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces]
  congr 1
  omega

end SUnit

end SUnit

end

end GroundTheory.Global
