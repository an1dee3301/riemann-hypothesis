module

public import Mathlib
public import Development.Core20Slim.GroundTheory.GlobalFields.IdeleGroups.InfiniteProjInfiniteEmbeddingOfNe
public import Development.Core20Slim.GroundTheory.GlobalFields.IdeleGroups.Restricted
public import Development.Core20Slim.GroundTheory.GlobalFields.Adele.Topology
public import Init.Classical
public import Init.Core
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Submonoid.Units
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Notation.Prod
public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.WithAbs
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SProd
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Prod.Basic
public import Mathlib.Data.Set.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Set.Lattice.Indexed
public import Mathlib.Data.Set.Operations
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Filter.Basic
public import Mathlib.Order.Filter.Cofinite
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.Notation
public import Mathlib.Order.SetNotation
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Algebra.Group.Units
public import Mathlib.Topology.Algebra.RestrictedProduct.Basic
public import Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Basic
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.Topology.Maps.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open Filter Topology TopologicalSpace NumberField IsDedekindDomain
open scoped RestrictedProduct NumberField.AdeleRing

namespace GroundTheory.Global

namespace RestrictedProduct

variable {ι : Type*} {R : ι → Type*} [∀ i, TopologicalSpace (R i)] {A : (i : ι) → Set (R i)}

theorem isOpen_setOf_forall_mem (hAopen : ∀ i, IsOpen (A i)) {V : ∀ i, Set (R i)}
    (hV : ∀ i, IsOpen (V i)) (hVA : ∀ᶠ i in cofinite, V i = A i) :
    IsOpen {x : Πʳ i, [R i, A i] | ∀ i, x i ∈ V i} := by
  set S : Set ι := {i | V i = A i}
  have hSf : Sᶜ.Finite := hVA
  have hEq : {x : Πʳ i, [R i, A i] | ∀ i, x i ∈ V i} =
      {x : Πʳ i, [R i, A i] | ∀ i, i ∈ S → x.1 i ∈ A i} ∩
        ⋂ i ∈ Sᶜ, (fun x : Πʳ i, [R i, A i] ↦ x i) ⁻¹' V i := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage]
    constructor
    · intro h
      exact ⟨fun i hi ↦ (show V i = A i from hi) ▸ h i, fun i _ ↦ h i⟩
    · rintro ⟨h1, h2⟩ i
      by_cases hi : i ∈ S
      · rw [show V i = A i from hi]
        exact h1 i hi
      · exact h2 i hi
  rw [hEq]
  exact (_root_.RestrictedProduct.isOpen_forall_imp_mem hAopen).inter
    (hSf.isOpen_biInter fun i _ ↦ (hV i).preimage (_root_.RestrictedProduct.continuous_eval i))

theorem isTopologicalBasis (hAopen : ∀ i, IsOpen (A i)) :
    IsTopologicalBasis {s : Set (Πʳ i, [R i, A i]) | ∃ V : ∀ i, Set (R i),
      (∀ i, IsOpen (V i)) ∧ (∀ᶠ i in cofinite, V i = A i) ∧ s = {x | ∀ i, x i ∈ V i}} := by
  classical
  refine isTopologicalBasis_of_isOpen_of_nhds ?_ ?_
  · rintro _ ⟨V, hV, hVA, rfl⟩
    exact isOpen_setOf_forall_mem hAopen hV hVA
  · intro x u hxu hu
    set T : Set ι := {i | x i ∈ A i}
    have hT : cofinite ≤ 𝓟 T := le_principal_iff.mpr x.2
    obtain ⟨x', hxx'⟩ :=
      _root_.RestrictedProduct.exists_inclusion_eq_of_eventually R A hT (fun i hi ↦ hi)
    have hu' : IsOpen (_root_.RestrictedProduct.inclusion R A hT ⁻¹' u) :=
      hu.preimage (_root_.RestrictedProduct.continuous_inclusion hT)
    rw [_root_.RestrictedProduct.isEmbedding_coe_of_principal.isInducing.isOpen_iff] at hu'
    obtain ⟨t, ht, htu⟩ := hu'
    have hx't : (x' : ∀ i, R i) ∈ t := by
      have : x' ∈ _root_.RestrictedProduct.inclusion R A hT ⁻¹' u := by
        rw [Set.mem_preimage, hxx']
        exact hxu
      rw [← htu] at this
      exact this
    obtain ⟨I, W, hW, hIW⟩ := isOpen_pi_iff.1 ht _ hx't
    let V : ∀ i, Set (R i) := fun i ↦
      (if i ∈ I then W i else Set.univ) ∩ (if i ∈ T then A i else Set.univ)
    refine ⟨{y | ∀ i, y i ∈ V i}, ⟨V, fun i ↦ ?_, ?_, rfl⟩, ?_, ?_⟩
    · refine IsOpen.inter ?_ ?_
      · split_ifs with h
        exacts [(hW i h).1, isOpen_univ]
      · split_ifs
        exacts [hAopen i, isOpen_univ]
    · filter_upwards [x.2, I.finite_toSet.compl_mem_cofinite] with i hi hiI
      have hiI' : i ∉ I := hiI
      have hiT : i ∈ T := hi
      simp only [V, if_neg hiI', if_pos hiT, Set.univ_inter]
    · intro i
      rw [← hxx']
      refine ⟨?_, ?_⟩
      · split_ifs with h
        exacts [(hW i h).2, Set.mem_univ _]
      · split_ifs with h
        exacts [eventually_principal.1 x'.2 i h, Set.mem_univ _]
    · intro y hy
      let y' : Πʳ i, [R i, A i]_[𝓟 T] := ⟨y.1, eventually_principal.2 fun i hi ↦ by
        have := (hy i).2
        simp only [if_pos hi] at this
        exact this⟩
      have hy' : y' ∈ _root_.RestrictedProduct.inclusion R A hT ⁻¹' u := by
        rw [← htu]
        refine hIW fun i hi ↦ ?_
        have := (hy i).1
        simp only [if_pos (Finset.mem_coe.1 hi)] at this
        exact this
      exact hy'

end RestrictedProduct

namespace IdeleGroup

variable (K : Type*) [Field K] [NumberField K]

theorem finiteProj_eq (v : HeightOneSpectrum (𝓞 K)) (x : IdeleGroup K) :
    finiteProj v x = (prodRestrictedEquiv K x).2 v :=
  Units.ext rfl

theorem infiniteProj_eq (w : InfinitePlace K) (x : IdeleGroup K) :
    infiniteProj w x = ContinuousMulEquiv.piUnits (prodRestrictedEquiv K x).1 w :=
  Units.ext rfl

theorem isTopologicalBasis :
    IsTopologicalBasis {s : Set (IdeleGroup K) |
      ∃ (U : ∀ w : InfinitePlace K, Set (w.Completion)ˣ)
        (V : ∀ v : HeightOneSpectrum (𝓞 K), Set (v.adicCompletion K)ˣ),
        (∀ w, IsOpen (U w)) ∧ (∀ v, IsOpen (V v)) ∧
        (∀ᶠ v in cofinite, V v =
          ((Submonoid.ofClass (v.adicCompletionIntegers K)).units : Set (v.adicCompletion K)ˣ)) ∧
        s = {x | (∀ w, infiniteProj w x ∈ U w) ∧ ∀ v, finiteProj v x ∈ V v}} := by
  set e := prodRestrictedEquiv K
  set p := (ContinuousMulEquiv.piUnits :
    (InfiniteAdeleRing K)ˣ ≃ₜ* ∀ w : InfinitePlace K, (w.Completion)ˣ)
  refine isTopologicalBasis_of_isOpen_of_nhds ?_ ?_
  · rintro _ ⟨U, V, hU, hV, hVO, rfl⟩
    have h1 : IsOpen {x : IdeleGroup K | ∀ w, infiniteProj w x ∈ U w} := by
      simp only [Set.ofPred_forall]
      exact isOpen_iInter_of_finite fun w ↦ (hU w).preimage (continuous_infiniteProj w)
    have h2 : IsOpen {x : IdeleGroup K | ∀ v, finiteProj v x ∈ V v} := by
      simp only [finiteProj_eq]
      exact (RestrictedProduct.isOpen_setOf_forall_mem
        (fun v ↦ isOpen_units_adicCompletionIntegers K v) hV hVO).preimage
          (continuous_snd.comp e.continuous)
    exact h1.inter h2
  · intro x u hxu hu
    have hu' : IsOpen (e.symm ⁻¹' u) := hu.preimage e.symm.continuous
    have hxu' : e x ∈ e.symm ⁻¹' u := by simpa using hxu
    obtain ⟨a, b, ha, hb, hxa, hxb, hab⟩ := isOpen_prod_iff.1 hu' (e x).1 (e x).2 hxu'
    obtain ⟨_, ⟨V, hV, hVO, rfl⟩, hxV, hVb⟩ :=
      (RestrictedProduct.isTopologicalBasis
        (fun v ↦ isOpen_units_adicCompletionIntegers K v)).exists_subset_of_mem_open hxb hb
    have ha' : IsOpen (p.symm ⁻¹' a) := ha.preimage p.symm.continuous
    have hxa' : p (e x).1 ∈ p.symm ⁻¹' a := by
      change p.symm (p (e x).1) ∈ a
      exact (congrArg (fun z : (InfiniteAdeleRing K)ˣ ↦ z ∈ a)
        (p.symm_apply_apply (e x).1)).mpr hxa
    obtain ⟨U, hU, hUa⟩ := isOpen_pi_iff'.1 ha' _ hxa'
    refine ⟨{y | (∀ w, infiniteProj w y ∈ U w) ∧ ∀ v, finiteProj v y ∈ V v},
      ⟨U, V, fun w ↦ (hU w).1, hV, hVO, rfl⟩, ⟨fun w ↦ ?_, fun v ↦ ?_⟩, ?_⟩
    · rw [infiniteProj_eq]
      exact (hU w).2
    · rw [finiteProj_eq]
      exact hxV v
    · rintro y ⟨hyU, hyV⟩
      have hya : (e y).1 ∈ a := by
        have : p (e y).1 ∈ p.symm ⁻¹' a := hUa fun w _ ↦ by
          rw [← infiniteProj_eq]
          exact hyU w
        change p.symm (p (e y).1) ∈ a at this
        exact (congrArg (fun z : (InfiniteAdeleRing K)ˣ ↦ z ∈ a)
          (p.symm_apply_apply (e y).1)).mp this
      have hyb : (e y).2 ∈ b := hVb fun v ↦ by
        rw [← finiteProj_eq]
        exact hyV v
      have := hab (Set.mk_mem_prod hya hyb)
      simpa using this

end IdeleGroup

end GroundTheory.Global
