module

public import Mathlib
public import Development.Core20Slim.GroundTheory.GlobalFields.IdeleGroups.NormOneCompact
public import Development.Core20Slim.GroundTheory.GlobalFields.TateThesis.IdeleMeasureNormOne
public import Development.Core20Slim.GroundTheory.GlobalFields.IdeleGroups.IdeleNorms
public import Development.Core20Slim.GroundTheory.GlobalFields.IdeleGroups.InfiniteProjInfiniteEmbeddingOfNe
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Positive.Ring
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SProd
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open NumberField Set
open GroundTheory.Global GroundTheory.Global.IdeleGroup

namespace GroundTheory.Automorphic

namespace Reduction

variable {K : Type*} [Field K] [NumberField K]

theorem exists_isCompact_mul_mem_of_ideleModule_mem_Icc {a : ℝ} (ha : 0 < a) (b : ℝ) :
    ∃ S : Set (IdeleGroup K), IsCompact S ∧ ∀ s : IdeleGroup K,
      a ≤ (ideleModule K s : ℝ) → (ideleModule K s : ℝ) ≤ b → ∃ c : Kˣ, diagonal K c * s ∈ S := by
  obtain ⟨D, hD, -, hxD⟩ := exists_isCompact_normOneSubgroup K
  obtain ⟨w₀⟩ : Nonempty (InfinitePlace K) := inferInstance
  set I : Set {r : ℝ // 0 < r} := Subtype.val ⁻¹' Icc a b with hI
  have hIc : IsCompact I := by
    rw [Subtype.isCompact_iff]
    have : Subtype.val '' I = Icc a b := by
      ext r
      constructor
      · rintro ⟨t, ht, rfl⟩
        exact ht
      · intro hr
        exact ⟨⟨r, lt_of_lt_of_le ha hr.1⟩, hr, rfl⟩
    rw [this]
    exact isCompact_Icc
  refine ⟨(fun p : IdeleGroup K × {r : ℝ // 0 < r} => p.1 * moduleSection w₀ p.2) '' (D ×ˢ I),
    (hD.prod hIc).image (continuous_fst.mul ((continuous_moduleSection w₀).comp continuous_snd)),
    fun s has hsb => ?_⟩
  obtain ⟨c, hc⟩ := hxD _ (mul_inv_moduleSection_mem w₀ s)
  refine ⟨c, ⟨(diagonal K c * (s * (moduleSection w₀ (ideleModule K s))⁻¹), ideleModule K s),
    ⟨hc, has, hsb⟩, ?_⟩⟩
  simp only [mul_assoc, inv_mul_cancel, mul_one]

end Reduction

end GroundTheory.Automorphic
