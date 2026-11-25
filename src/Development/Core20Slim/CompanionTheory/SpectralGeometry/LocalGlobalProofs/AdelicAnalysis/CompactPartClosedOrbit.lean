module

public import Mathlib
public import Init.Classical
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pretransitive
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Set.CoeSort
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Lattice.Bounded
public import Mathlib.Data.Set.Lattice.Indexed
public import Mathlib.Data.Set.Operations
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.SetNotation
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Group.OpenMapping
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Topology.Baire.LocallyCompactRegular
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Closure
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Compactness.LocallyCompact
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Neighborhoods
public import Mathlib.Topology.Separation.Basic
public import Mathlib.Topology.Separation.Hausdorff

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.Adelic

theorem compact_part_closed_orbit :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
      [LocallyCompactSpace G] [SecondCountableTopology G] (V : Type) [TopologicalSpace V]
      [T2Space V] [LocallyCompactSpace V] (a : G → V → V),
      (Continuous fun p : G × V => a p.1 p.2) → (∀ y, a 1 y = y) →
      (∀ g h y, a (g * h) y = a g (a h y)) →
      ∀ (Z : Set V) (x : V), IsClosed Z → (∀ y, y ∈ Z ↔ ∃ g, a g x = y) →
      ∀ Ω : Set V, IsCompact Ω → ∃ C : Set G, IsCompact C ∧ ∀ y ∈ Ω, y ∈ Z → ∃ c ∈ C, a c x = y := by
  intro G _ _ _ _ _ _ V _ _ _ a ha h1 hmul Z x hZ hZx Ω hΩ
  have hmem : ∀ (g : G) (z : Z), a g z ∈ Z := by
    intro g z
    obtain ⟨h, hh⟩ := (hZx z).1 z.2
    exact (hZx _).2 ⟨g * h, by rw [hmul, hh]⟩
  letI : MulAction G Z :=
    { smul := fun g z => ⟨a g z, hmem g z⟩
      one_smul := fun z => Subtype.ext (h1 z)
      mul_smul := fun g h z => Subtype.ext (hmul g h z) }
  haveI : ContinuousSMul G Z :=
    ⟨Continuous.subtype_mk
      (ha.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)))
      (fun p => hmem p.1 p.2)⟩
  haveI : MulAction.IsPretransitive G Z := by
    refine ⟨fun z w => ?_⟩
    obtain ⟨g, hg⟩ := (hZx z).1 z.2
    obtain ⟨h, hh⟩ := (hZx w).1 w.2
    refine ⟨h * g⁻¹, Subtype.ext ?_⟩
    show a (h * g⁻¹) z = w
    rw [← hg, ← hmul, inv_mul_cancel_right, hh]
  haveI : LocallyCompactSpace Z := hZ.locallyCompactSpace
  haveI : BaireSpace Z := BaireSpace.of_t2Space_locallyCompactSpace
  have hx : x ∈ Z := (hZx x).2 ⟨1, h1 x⟩
  have hopen := isOpenMap_smul_of_sigmaCompact (G := G) (X := Z) ⟨x, hx⟩
  choose K hK hKn using fun g : G => exists_compact_mem_nhds g
  have hS : IsCompact ((Subtype.val : Z → V) ⁻¹' Ω) :=
    hZ.isClosedEmbedding_subtypeVal.isCompact_preimage hΩ
  obtain ⟨t, ht⟩ := hS.elim_finite_subcover
    (fun g => (fun h : G => h • (⟨x, hx⟩ : Z)) '' interior (K g))
    (fun g => hopen _ isOpen_interior) (by
      intro z _
      obtain ⟨g, hg⟩ := (hZx z).1 z.2
      exact Set.mem_iUnion.2 ⟨g, g, mem_interior_iff_mem_nhds.2 (hKn g), Subtype.ext hg⟩)
  refine ⟨⋃ g ∈ t, K g, t.isCompact_biUnion fun g _ => hK g, ?_⟩
  intro y hyΩ hyZ
  have hy := ht (show (⟨y, hyZ⟩ : Z) ∈ (Subtype.val : Z → V) ⁻¹' Ω from hyΩ)
  rw [Set.mem_iUnion₂] at hy
  obtain ⟨g, hgt, c, hc, hcy⟩ := hy
  exact ⟨c, Set.mem_biUnion hgt (interior_subset hc), congrArg Subtype.val hcy⟩

end GlobalTheory.CompanionTheory.Adelic
