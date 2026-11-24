module

public import Mathlib
public import Development.Core20Slim.GroundTheory.GlobalFields.TateThesis.Conductor
public import Development.Core20Slim.GroundTheory.GlobalFields.IdeleGroups.InfiniteProjInfiniteEmbeddingOfNe
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Int.Lemmas
public import Init.Data.Int.Order
public import Init.Data.Nat.Basic
public import Init.Data.Nat.Lemmas
public import Init.Data.Zero
public import Init.Omega.Coeffs
public import Init.Omega.Constraint
public import Init.Omega.Int
public import Init.Omega.LinearCombo
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.Divisibility.Basic
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.FiniteSupport.Defs
public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Module.Submodule.Pointwise
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Notation.Prod
public import Mathlib.Algebra.Notation.Support
public import Mathlib.Algebra.Order.Kleene
public import Mathlib.Algebra.Ring.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.Order.BoundedOrder.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.DedekindDomain.Factorization
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.Ideal.Basic
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Maximal
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.Ideal.Prime
public import Mathlib.RingTheory.Multiplicity
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Homeomorph.Defs

@[expose] public section

open Topology Filter NumberField IsDedekindDomain Function
open scoped NumberField.AdeleRing

namespace GroundTheory.Global

noncomputable section

section Ideals

variable {R : Type*} [CommRing R] [IsDedekindDomain R]


omit [IsDedekindDomain R] in
theorem asIdeal_pow_eq_one_iff (v : HeightOneSpectrum R) {k : ℕ} : v.asIdeal ^ k = 1 ↔ k = 0 := by
  constructor
  · intro h
    by_contra hk
    have hle : v.asIdeal ^ k ≤ v.asIdeal := Ideal.pow_le_self hk
    rw [h, Ideal.one_eq_top, top_le_iff] at hle
    exact v.isPrime.ne_top hle
  · rintro rfl
    exact pow_zero _

omit [IsDedekindDomain R] in
theorem mulSupport_asIdeal_pow (a : HeightOneSpectrum R → ℕ) :
    mulSupport (fun v : HeightOneSpectrum R ↦ v.asIdeal ^ a v) = support a := by
  ext v
  simp only [mem_mulSupport, mem_support, ne_eq, asIdeal_pow_eq_one_iff]

theorem finprod_asIdeal_pow_ne_bot (a : HeightOneSpectrum R → ℕ) :
    (∏ᶠ v : HeightOneSpectrum R, v.asIdeal ^ a v) ≠ ⊥ :=
  finprod_induction (fun I : Ideal R ↦ I ≠ ⊥) one_ne_zero (fun _ _ hx hy ↦ mul_ne_zero hx hy)
    fun v ↦ pow_ne_zero _ v.ne_bot

theorem finprod_asIdeal_pow_dvd_iff {a : HeightOneSpectrum R → ℕ} (ha : (support a).Finite)
    {I : Ideal R} (hI : I ≠ ⊥) :
    (∏ᶠ v : HeightOneSpectrum R, v.asIdeal ^ a v) ∣ I ↔
      ∀ v : HeightOneSpectrum R, a v ≤ multiplicity v.asIdeal I := by
  have hfa : HasFiniteMulSupport fun v : HeightOneSpectrum R ↦ v.asIdeal ^ a v := by
    rw [HasFiniteMulSupport, mulSupport_asIdeal_pow]
    exact ha
  constructor
  · intro h v
    have h1 : v.asIdeal ^ a v ∣ I := (finprod_mem_dvd v hfa).trans h
    have h2 := HeightOneSpectrum.multiplicity_le_of_ideal_ge v (Ideal.le_of_dvd h1) hI
    rwa [multiplicity_pow_self_of_prime (HeightOneSpectrum.prime v)] at h2
  · intro h
    have hm : HasFiniteMulSupport fun v : HeightOneSpectrum R ↦
        v.asIdeal ^ multiplicity v.asIdeal I := by
      simpa only [HeightOneSpectrum.maxPowDividing_eq_pow_multiplicity hI] using
        Ideal.hasFiniteMulSupport hI
    have hmb : HasFiniteMulSupport fun v : HeightOneSpectrum R ↦
        v.asIdeal ^ (multiplicity v.asIdeal I - a v) := by
      rw [HasFiniteMulSupport, mulSupport_asIdeal_pow] at hm ⊢
      refine hm.subset fun v hv ↦ ?_
      simp only [mem_support, ne_eq] at hv ⊢
      omega
    have hsplit : (fun v : HeightOneSpectrum R ↦ v.asIdeal ^ multiplicity v.asIdeal I) =
        fun v ↦ v.asIdeal ^ a v * v.asIdeal ^ (multiplicity v.asIdeal I - a v) :=
      funext fun v ↦ by rw [← pow_add, Nat.add_sub_cancel' (h v)]
    conv_rhs => rw [← Ideal.finprod_heightOneSpectrum_pow_multiplicity hI]
    rw [hsplit, finprod_mul_distrib hfa hmb]
    exact dvd_mul_right _ _

theorem asIdeal_dvd_finprod_iff {a : HeightOneSpectrum R → ℕ} (ha : (support a).Finite)
    (v : HeightOneSpectrum R) :
    v.asIdeal ∣ ∏ᶠ w : HeightOneSpectrum R, w.asIdeal ^ a w ↔ 1 ≤ a v := by
  have hfa : HasFiniteMulSupport fun v : HeightOneSpectrum R ↦ v.asIdeal ^ a v := by
    rw [HasFiniteMulSupport, mulSupport_asIdeal_pow]
    exact ha
  constructor
  · intro h
    classical
    rw [finprod_eq_prod_of_mulSupport_subset _ (s := ha.toFinset)
      (by rw [mulSupport_asIdeal_pow, ha.coe_toFinset])] at h
    obtain ⟨w, hw, hvw⟩ := ((HeightOneSpectrum.prime v).dvd_finsetProd_iff _).1 h
    have hvw' := (HeightOneSpectrum.prime v).dvd_of_dvd_pow hvw
    have heq : v = w := HeightOneSpectrum.ext (associated_iff_eq.1
      ((HeightOneSpectrum.prime v).associated_of_dvd (HeightOneSpectrum.prime w) hvw'))
    subst heq
    rw [Set.Finite.mem_toFinset, mem_support] at hw
    omega
  · intro h
    exact (dvd_pow_self _ (by omega)).trans (finprod_mem_dvd v hfa)

end Ideals

namespace IdeleGroup

variable {K : Type*} [Field K] [NumberField K] {H : Type*} [Group H] [TopologicalSpace H]

def conductor (χ : (FiniteAdeleRing (𝓞 K) K)ˣ →* H) : Ideal (𝓞 K) :=
  ∏ᶠ v : HeightOneSpectrum (𝓞 K), v.asIdeal ^ conductorExponentAt χ v

omit [TopologicalSpace H] in
theorem conductor_ne_bot (χ : (FiniteAdeleRing (𝓞 K) K)ˣ →* H) : conductor χ ≠ ⊥ :=
  finprod_asIdeal_pow_ne_bot _

def idealLevel (𝔪 : Ideal (𝓞 K)) : Subgroup (FiniteAdeleRing (𝓞 K) K)ˣ :=
  finiteLevel fun v ↦ multiplicity v.asIdeal 𝔪

theorem idealLevel_le_ker_iff (hH : NoSmallSubgroups H) (χ : (FiniteAdeleRing (𝓞 K) K)ˣ →* H)
    (hχ : Continuous χ) {𝔪 : Ideal (𝓞 K)} (h𝔪 : 𝔪 ≠ ⊥) :
    idealLevel 𝔪 ≤ χ.ker ↔ conductor χ ∣ 𝔪 := by
  rw [idealLevel, finiteLevel_le_ker_iff hH χ hχ, conductor,
    finprod_asIdeal_pow_dvd_iff (finite_support_conductorExponentAt hH χ hχ) h𝔪]

theorem dvd_conductor_iff (hH : NoSmallSubgroups H) (χ : (FiniteAdeleRing (𝓞 K) K)ˣ →* H)
    (hχ : Continuous χ) (v : HeightOneSpectrum (𝓞 K)) :
    v.asIdeal ∣ conductor χ ↔ 1 ≤ conductorExponentAt χ v :=
  asIdeal_dvd_finprod_iff (finite_support_conductorExponentAt hH χ hχ) v

theorem not_dvd_conductor_iff (hH : NoSmallSubgroups H) (χ : (FiniteAdeleRing (𝓞 K) K)ˣ →* H)
    (hχ : Continuous χ) (v : HeightOneSpectrum (𝓞 K)) :
    ¬ v.asIdeal ∣ conductor χ ↔
      (Submonoid.ofClass (v.adicCompletionIntegers K)).units ≤
        (χ.comp (finiteUnitsSingle v)).ker := by
  rw [dvd_conductor_iff hH χ hχ, ← conductorExponentAt_eq_zero_iff hH χ hχ,
    Nat.one_le_iff_ne_zero, not_not]

def ofFinite : (FiniteAdeleRing (𝓞 K) K)ˣ →* IdeleGroup K :=
  (ContinuousMulEquiv.symm (prodEquiv K)).toMulEquiv.toMonoidHom.comp (MonoidHom.inr _ _)

theorem continuous_ofFinite : Continuous (ofFinite (K := K)) := by
  have : Continuous fun x : (FiniteAdeleRing (𝓞 K) K)ˣ ↦
      ContinuousMulEquiv.symm (prodEquiv K) ((1 : (InfiniteAdeleRing K)ˣ), x) :=
    (ContinuousMulEquiv.symm (prodEquiv K)).continuous.comp (continuous_const.prodMk continuous_id)
  exact this

@[simp]
theorem toFinite_ofFinite (x : (FiniteAdeleRing (𝓞 K) K)ˣ) : toFinite K (ofFinite x) = x := by
  change ((prodEquiv K) ((ContinuousMulEquiv.symm (prodEquiv K)) (1, x))).2 = x
  rw [ContinuousMulEquiv.apply_symm_apply]

@[simp]
theorem toInfinite_ofFinite (x : (FiniteAdeleRing (𝓞 K) K)ˣ) : toInfinite K (ofFinite x) = 1 := by
  change ((prodEquiv K) ((ContinuousMulEquiv.symm (prodEquiv K)) (1, x))).1 = 1
  rw [ContinuousMulEquiv.apply_symm_apply]

theorem mem_standardOpenSubgroup_iff_toFinite_mem (x : IdeleGroup K) :
    x ∈ standardOpenSubgroup K ↔ toFinite K x ∈ finiteLevel 0 := by
  rw [mem_standardOpenSubgroup, mem_finiteLevel]
  refine forall_congr' fun v ↦ ?_
  rw [Pi.zero_apply, unitsLevel_zero, Submonoid.mem_units_iff]
  rfl

theorem map_idealLevel_le_ker_iff (hH : NoSmallSubgroups H) (χ : IdeleGroup K →* H)
    (hχ : Continuous χ) {𝔪 : Ideal (𝓞 K)} (h𝔪 : 𝔪 ≠ ⊥) :
    (idealLevel 𝔪).map ofFinite ≤ χ.ker ↔ conductor (χ.comp ofFinite) ∣ 𝔪 := by
  rw [Subgroup.map_le_iff_le_comap, MonoidHom.comap_ker]
  exact idealLevel_le_ker_iff hH _ (hχ.comp continuous_ofFinite) h𝔪

end IdeleGroup

end

end GroundTheory.Global
