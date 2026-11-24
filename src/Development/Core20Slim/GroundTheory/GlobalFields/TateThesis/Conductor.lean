module

public import Mathlib
public import Development.Core20Slim.GroundTheory.GlobalFields.IdeleGroups.InfiniteProjInfiniteEmbeddingOfNe
public import Development.Core20Slim.GroundTheory.GlobalFields.IdeleGroups.Restricted
public import Development.Core20Slim.GroundTheory.GlobalFields.TateThesis.LocalConductor
public import GroundTheory.GlobalFields.TateThesis.NoSmallSubgroups
public import Init.ByCases
public import Init.Classical
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.PropLemmas
public import Init.SimpLemmas
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Submonoid.Units
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Notation.Support
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Set.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Set.Operations
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.BoundedOrder.Basic
public import Mathlib.Order.CompleteBooleanAlgebra
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Defs.Prop
public import Mathlib.Order.Filter.Basic
public import Mathlib.Order.Filter.Cofinite
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.Filter.Map
public import Mathlib.Order.Filter.Pi
public import Mathlib.Order.Heyting.Basic
public import Mathlib.Order.Notation
public import Mathlib.Order.SetNotation
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Algebra.RestrictedProduct.Basic
public import Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace
public import Mathlib.Topology.Basic
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.Topology.Maps.Basic
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open Topology Filter NumberField IsDedekindDomain Function
open scoped NumberField.AdeleRing RestrictedProduct

namespace GroundTheory.Global

noncomputable section

namespace IdeleGroup

variable {K : Type*} [Field K] [NumberField K]

def finiteComponent (v : HeightOneSpectrum (𝓞 K)) :
    (FiniteAdeleRing (𝓞 K) K)ˣ →* (v.adicCompletion K)ˣ :=
  Units.map (_root_.RestrictedProduct.evalMonoidHom
    (fun w : HeightOneSpectrum (𝓞 K) ↦ w.adicCompletion K) v)

@[simp]
theorem coe_finiteComponent (v : HeightOneSpectrum (𝓞 K)) (x : (FiniteAdeleRing (𝓞 K) K)ˣ) :
    ((finiteComponent v x : (v.adicCompletion K)ˣ) : v.adicCompletion K) =
      (x : FiniteAdeleRing (𝓞 K) K) v :=
  rfl

theorem continuous_finiteComponent (v : HeightOneSpectrum (𝓞 K)) :
    Continuous (finiteComponent (K := K) v) :=
  Units.continuous_map (_root_.RestrictedProduct.continuous_eval v)

def finiteUnitsSingle (v : HeightOneSpectrum (𝓞 K)) :
    (v.adicCompletion K)ˣ →* (FiniteAdeleRing (𝓞 K) K)ˣ :=
  Units.map (finiteAdeleSingle v)


@[simp]
theorem finiteComponent_finiteUnitsSingle (v : HeightOneSpectrum (𝓞 K))
    (x : (v.adicCompletion K)ˣ) : finiteComponent v (finiteUnitsSingle v x) = x := by
  ext
  simp [finiteUnitsSingle]


def finiteLevel (n : HeightOneSpectrum (𝓞 K) → ℕ) : Subgroup (FiniteAdeleRing (𝓞 K) K)ˣ :=
  ⨅ v, (unitsLevel v (n v)).comap (finiteComponent v)

theorem mem_finiteLevel {n : HeightOneSpectrum (𝓞 K) → ℕ} {x : (FiniteAdeleRing (𝓞 K) K)ˣ} :
    x ∈ finiteLevel n ↔ ∀ v, finiteComponent v x ∈ unitsLevel v (n v) := by
  simp only [finiteLevel, Subgroup.mem_iInf, Subgroup.mem_comap]

theorem finiteLevel_antitone {m n : HeightOneSpectrum (𝓞 K) → ℕ} (h : m ≤ n) :
    finiteLevel n ≤ finiteLevel m := fun _ hx ↦
  mem_finiteLevel.2 fun v ↦ unitsLevel_antitone v (h v) (mem_finiteLevel.1 hx v)

theorem finiteLevel_le_finiteLevel_zero (n : HeightOneSpectrum (𝓞 K) → ℕ) :
    finiteLevel n ≤ finiteLevel 0 :=
  finiteLevel_antitone fun v ↦ Nat.zero_le (n v)


theorem finiteUnitsEquiv_apply_eq (x : (FiniteAdeleRing (𝓞 K) K)ˣ) (v : HeightOneSpectrum (𝓞 K)) :
    finiteUnitsEquiv K x v = finiteComponent v x :=
  Units.ext rfl

theorem isOpen_finiteLevel_zero :
    IsOpen (finiteLevel (K := K) 0 : Set (FiniteAdeleRing (𝓞 K) K)ˣ) := by
  have h := (_root_.RestrictedProduct.isOpen_forall_mem
    (R := fun v : HeightOneSpectrum (𝓞 K) ↦ (v.adicCompletion K)ˣ)
    (A := fun v ↦ ((Submonoid.ofClass (v.adicCompletionIntegers K)).units :
      Set (v.adicCompletion K)ˣ))
    (fun v ↦ isOpen_units_adicCompletionIntegers K v)).preimage (finiteUnitsEquiv K).continuous
  convert h using 1
  ext x
  simp only [SetLike.mem_coe, mem_finiteLevel, Pi.zero_apply, unitsLevel_zero, Set.mem_preimage,
    Set.mem_ofPred_eq]
  exact forall_congr' fun v ↦ by rw [← finiteUnitsEquiv_apply_eq]; rfl

theorem isOpen_finiteLevel {n : HeightOneSpectrum (𝓞 K) → ℕ} (hn : (support n).Finite) :
    IsOpen (finiteLevel n : Set (FiniteAdeleRing (𝓞 K) K)ˣ) := by
  have : (finiteLevel n : Set (FiniteAdeleRing (𝓞 K) K)ˣ) =
      (finiteLevel (K := K) 0 : Set (FiniteAdeleRing (𝓞 K) K)ˣ) ∩
      ⋂ v ∈ hn.toFinset, finiteComponent v ⁻¹'
        (unitsLevel (K := K) v (n v) : Set (v.adicCompletion K)ˣ) := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe]
    refine ⟨fun hx ↦ ⟨finiteLevel_le_finiteLevel_zero n hx, fun v _ ↦ mem_finiteLevel.1 hx v⟩,
      fun ⟨h0, h⟩ ↦ mem_finiteLevel.2 fun v ↦ ?_⟩
    by_cases hv : n v = 0
    · rw [hv]
      exact mem_finiteLevel.1 h0 v
    · exact h v (by simpa using hv)
  rw [this]
  exact isOpen_finiteLevel_zero.inter (isOpen_biInter_finset fun v _ ↦
    (isOpen_unitsLevel v (n v)).preimage (continuous_finiteComponent v))

theorem exists_finiteLevel_subset {W : Set (FiniteAdeleRing (𝓞 K) K)ˣ} (hW : W ∈ 𝓝 1) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 K)), ∃ n : HeightOneSpectrum (𝓞 K) → ℕ,
      (∀ v ∈ S, 1 ≤ n v) ∧ (∀ v ∉ S, n v = 0) ∧
        (finiteLevel n : Set (FiniteAdeleRing (𝓞 K) K)ˣ) ⊆ W := by
  classical
  let e := finiteUnitsEquiv K
  let es := ContinuousMulEquiv.symm e
  have hS : (cofinite : Filter (HeightOneSpectrum (𝓞 K))) ≤ 𝓟 Set.univ := by simp
  have hW1 : es ⁻¹' W ∈ 𝓝 (1 : Πʳ v : HeightOneSpectrum (𝓞 K),
      [(v.adicCompletion K)ˣ, (Submonoid.ofClass (v.adicCompletionIntegers K)).units]) :=
    es.continuous.continuousAt.preimage_mem_nhds (by change W ∈ 𝓝 (es 1); rwa [map_one es])
  have hW2 := (_root_.RestrictedProduct.continuous_inclusion
    (R := fun v : HeightOneSpectrum (𝓞 K) ↦ (v.adicCompletion K)ˣ)
    (A := fun v ↦ ((Submonoid.ofClass (v.adicCompletionIntegers K)).units :
      Set (v.adicCompletion K)ˣ)) hS).continuousAt.preimage_mem_nhds (x := 1) hW1
  rw [_root_.RestrictedProduct.isEmbedding_coe_of_principal.nhds_eq_comap, mem_comap] at hW2
  obtain ⟨t, ht, htW⟩ := hW2
  rw [nhds_pi, Filter.mem_pi'] at ht
  obtain ⟨I, u, hu, hIu⟩ := ht
  choose N hN hNu using fun v ↦ exists_unitsLevel_subset v (hu v)
  refine ⟨I, fun v ↦ if v ∈ I then N v else 0, fun v hv ↦ by simp [hv, hN v],
    fun v hv ↦ by simp [hv], ?_⟩
  intro x hx
  rw [SetLike.mem_coe, mem_finiteLevel] at hx
  have hx0 : ∀ v, e x v ∈ (Submonoid.ofClass (v.adicCompletionIntegers K)).units := fun v ↦ by
    rw [finiteUnitsEquiv_apply_eq, ← unitsLevel_zero]
    exact unitsLevel_antitone v (Nat.zero_le _) (hx v)
  let z : Πʳ v : HeightOneSpectrum (𝓞 K),
      [(v.adicCompletion K)ˣ, (Submonoid.ofClass (v.adicCompletionIntegers K)).units]_[𝓟 Set.univ] :=
    ⟨fun v ↦ e x v, Filter.eventually_principal.2 fun v _ ↦ hx0 v⟩
  have hz := htW (show (z : Π v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ) ∈ t from
    hIu fun v hv ↦ by
      have := hx v
      simp only [Finset.mem_coe.1 hv, if_true] at this
      exact hNu v (by rw [← finiteUnitsEquiv_apply_eq] at this; exact this))
  have hzx : _root_.RestrictedProduct.inclusion _ _ hS z = e x := rfl
  rw [Set.mem_preimage, Set.mem_preimage, hzx] at hz
  rwa [show es (e x) = x from ContinuousMulEquiv.symm_apply_apply e x] at hz

section Character

variable {H : Type*} [Group H] [TopologicalSpace H]

theorem exists_finiteLevel_le_ker (hH : NoSmallSubgroups H)
    (χ : (FiniteAdeleRing (𝓞 K) K)ˣ →* H) (hχ : Continuous χ) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 K)), ∃ n : HeightOneSpectrum (𝓞 K) → ℕ,
      (∀ v ∈ S, 1 ≤ n v) ∧ (∀ v ∉ S, n v = 0) ∧ finiteLevel n ≤ χ.ker := by
  obtain ⟨L, ⟨S, n, h1, h0, rfl⟩, hL⟩ := exists_le_ker_of_noSmallSubgroups
    (P := fun L ↦ ∃ S : Finset (HeightOneSpectrum (𝓞 K)), ∃ n : HeightOneSpectrum (𝓞 K) → ℕ,
      (∀ v ∈ S, 1 ≤ n v) ∧ (∀ v ∉ S, n v = 0) ∧ L = finiteLevel n)
    (fun W hW ↦ by
      obtain ⟨S, n, h1, h0, h⟩ := exists_finiteLevel_subset hW
      exact ⟨_, ⟨S, n, h1, h0, rfl⟩, h⟩) hH χ hχ
  exact ⟨S, n, h1, h0, hL⟩

theorem exists_finiteLevel_le_ker_circle (χ : (FiniteAdeleRing (𝓞 K) K)ˣ →* Circle)
    (hχ : Continuous χ) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 K)), ∃ n : HeightOneSpectrum (𝓞 K) → ℕ,
      (∀ v ∈ S, 1 ≤ n v) ∧ (∀ v ∉ S, n v = 0) ∧ finiteLevel n ≤ χ.ker :=
  exists_finiteLevel_le_ker Circle.noSmallSubgroups χ hχ





end Character

end IdeleGroup

end

end GroundTheory.Global
