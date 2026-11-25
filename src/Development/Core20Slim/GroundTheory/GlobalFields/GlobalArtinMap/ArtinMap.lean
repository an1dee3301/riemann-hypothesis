module

public import Mathlib
public import Development.Core20Slim.GroundTheory.GlobalFields.ExistenceTheorem.ExistsIsAbelianGaloisRangeIdeleClassNormEqOfFini
public import Development.Core20Slim.GroundTheory.GlobalFields.NormResidueSymbol.RestrictNormalInfiniteLocalSymbol
public import Development.Core20Slim.GroundTheory.GlobalFields.NormResidueSymbol.FunctorialLocal
public import Development.Core20Slim.GroundTheory.LocalFields.MaximalAbelianExtension
public import Development.Core20Slim.GroundTheory.GlobalFields.GlobalReciprocity.General
public import Development.Core20Slim.GroundTheory.GlobalFields.IdeleGroups.InfiniteProjInfiniteEmbeddingOfNe
public import Development.Core20Slim.GroundTheory.GlobalFields.NormResidueSymbol.RangeFiniteLocalNormLeKerLocalSymbol
public import Development.Core20Slim.GroundTheory.GlobalFields.NormResidueSymbol.RangeIdeleNormLeKerIdeleSymbol
public import Init.Classical
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Set.CoeSort
public import Mathlib.Data.Set.Defs
public import Mathlib.FieldTheory.Galois.Abelian
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.Galois.Profinite
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.FieldTheory.IntermediateField.Algebraic
public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.FieldTheory.KrullTopology
public import Mathlib.FieldTheory.Normal.Defs
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Basic
public import Mathlib.Order.BoundedOrder.Basic
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Defs
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Directed
public import Mathlib.Order.Notation
public import Mathlib.Order.SetNotation
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Algebra.Group.Quotient
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Connected.Separation
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Separation.Hausdorff

set_option synthInstance.maxHeartbeats 400000

@[expose] public section

namespace GroundTheory.Global

open IsDedekindDomain NumberField IntermediateField IdeleGroup GroundTheory.LocalField SemiLocal

noncomputable section

universe u

section Restrict

variable {K : Type*} [Field K] [NumberField K] {Ω : Type*} [Field Ω] [Algebra K Ω]

theorem reciprocityMap_apply_of_le {L L' : IntermediateField K Ω} [FiniteDimensional K L]
    [IsAbelianGalois K L] [FiniteDimensional K L'] [IsAbelianGalois K L'] (h : L ≤ L')
    (c : IdeleClassGroup K) (l : L) :
    ((reciprocityMap K L' c ⟨l, h l.2⟩ : L') : Ω) = ((reciprocityMap K L c l : L) : Ω) := by
  let _ : Algebra L L' := (IntermediateField.inclusion h).toAlgebra
  have : IsScalarTower K L L' := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  obtain ⟨x, rfl⟩ := IdeleClassGroup.mk_surjective K c
  rw [reciprocityMap_mk, reciprocityMap_mk, ← restrictNormal_ideleSymbol (L := L) (M := L')]
  exact congrArg Subtype.val (AlgEquiv.restrictNormal_commutes (ideleSymbol K L' x) L l).symm

variable [IsGalois K Ω]


omit [NumberField K] in
theorem restrictAb_eq_of_le {L L' : IntermediateField K Ω} [Normal K L] [Normal K L']
    (hL' : L' ≤ maximalAbelianExtension K Ω) (h : L ≤ L')
    {σ τ : maximalAbelianExtension K Ω ≃ₐ[K] maximalAbelianExtension K Ω}
    (hστ : restrictAb L' hL' σ = restrictAb L' hL' τ) :
    restrictAb L (h.trans hL') σ = restrictAb L (h.trans hL') τ := by
  ext l
  have e := congrArg (fun ρ : L' ≃ₐ[K] L' ↦ ((ρ ⟨l, h l.2⟩ : L') : Ω)) hστ
  simp only [restrictAb_apply] at e ⊢
  exact e

theorem restrictAb_eq_reciprocityMap_of_le {L L' : IntermediateField K Ω} [FiniteDimensional K L]
    [IsAbelianGalois K L] [FiniteDimensional K L'] [IsAbelianGalois K L'] (h : L ≤ L')
    {c : IdeleClassGroup K} {τ : maximalAbelianExtension K Ω ≃ₐ[K] maximalAbelianExtension K Ω}
    (hτ : restrictAb L' (le_maximalAbelianExtension L') τ = reciprocityMap K L' c) :
    restrictAb L (le_maximalAbelianExtension L) τ = reciprocityMap K L c := by
  ext l
  have e := congrArg (fun ρ : L' ≃ₐ[K] L' ↦ ((ρ ⟨l, h l.2⟩ : L') : Ω)) hτ
  simp only [restrictAb_apply] at e ⊢
  rw [e, reciprocityMap_apply_of_le h]

end Restrict

section ArtinMap

variable (K : Type*) [Field K] [NumberField K] (Ω : Type*) [Field Ω] [Algebra K Ω] [IsGalois K Ω]

instance nonempty_finiteAbelianExtensions : Nonempty (finiteAbelianExtensions K Ω) :=
  ⟨⟨⊥, inferInstance, inferInstance⟩⟩


variable {K Ω} in
def fiberOver (c : IdeleClassGroup K) (L : finiteAbelianExtensions K Ω) :
    Set (maximalAbelianExtension K Ω ≃ₐ[K] maximalAbelianExtension K Ω) :=
  haveI := L.2.1
  haveI := L.2.2
  {τ | restrictAb (L : IntermediateField K Ω) (le_maximalAbelianExtension _) τ =
    reciprocityMap K (L : IntermediateField K Ω) c}

theorem exists_restrictAb_eq_reciprocityMap (c : IdeleClassGroup K) :
    ∃ τ : maximalAbelianExtension K Ω ≃ₐ[K] maximalAbelianExtension K Ω,
      ∀ (L : IntermediateField K Ω) [FiniteDimensional K L] [IsAbelianGalois K L],
        restrictAb L (le_maximalAbelianExtension L) τ = reciprocityMap K L c := by
  have hcl : ∀ L : finiteAbelianExtensions K Ω, IsClosed (fiberOver c L) := fun L ↦ by
    have := L.2.1
    have := L.2.2
    exact isClosed_eq (continuous_restrictAb _ _) continuous_const
  have hne : ∀ L : finiteAbelianExtensions K Ω, (fiberOver c L).Nonempty := fun L ↦ by
    have := L.2.1
    have := L.2.2
    exact restrictAb_surjective (L : IntermediateField K Ω) _ _
  have hdir : Directed (· ⊇ ·) (fiberOver (Ω := Ω) c) := by
    intro L₁ L₂
    have := L₁.2.1
    have := L₁.2.2
    have := L₂.2.1
    have := L₂.2.2
    refine ⟨⟨(L₁ : IntermediateField K Ω) ⊔ L₂, inferInstance, inferInstance⟩, fun τ hτ ↦ ?_,
      fun τ hτ ↦ ?_⟩
    · exact restrictAb_eq_reciprocityMap_of_le le_sup_left hτ
    · exact restrictAb_eq_reciprocityMap_of_le le_sup_right hτ
  obtain ⟨τ, hτ⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
    (fiberOver c) hdir hne (fun L ↦ (hcl L).isCompact) hcl
  refine ⟨τ, fun L _ _ ↦ ?_⟩
  exact Set.mem_iInter.1 hτ ⟨L, inferInstance, inferInstance⟩

def artinMap : IdeleClassGroup K →* (maximalAbelianExtension K Ω ≃ₐ[K] maximalAbelianExtension K Ω) where
  toFun c := (exists_restrictAb_eq_reciprocityMap K Ω c).choose
  map_one' := ext_restrictAb fun L _ _ ↦ by
    rw [(exists_restrictAb_eq_reciprocityMap K Ω 1).choose_spec L, map_one, map_one]
  map_mul' c d := ext_restrictAb fun L _ _ ↦ by
    rw [(exists_restrictAb_eq_reciprocityMap K Ω (c * d)).choose_spec L, map_mul, map_mul,
      (exists_restrictAb_eq_reciprocityMap K Ω c).choose_spec L,
      (exists_restrictAb_eq_reciprocityMap K Ω d).choose_spec L]

variable {K Ω}

@[simp]
theorem restrictAb_artinMap (L : IntermediateField K Ω) [FiniteDimensional K L] [IsAbelianGalois K L]
    (c : IdeleClassGroup K) :
    restrictAb L (le_maximalAbelianExtension L) (artinMap K Ω c) = reciprocityMap K L c :=
  (exists_restrictAb_eq_reciprocityMap K Ω c).choose_spec L


theorem continuous_artinMap : Continuous (artinMap K Ω) :=
  continuous_iff_restrictAb.2 fun L _ _ ↦ by
    simp only [restrictAb_artinMap]
    exact continuous_reciprocityMap

end ArtinMap

section Local

variable {K : Type*} [Field K] [NumberField K] {Ω : Type*} [Field Ω] [Algebra K Ω] [IsGalois K Ω]
  (L : IntermediateField K Ω) [FiniteDimensional K L] [IsAbelianGalois K L]

theorem restrictAb_artinMap_finiteEmbedding (v : HeightOneSpectrum (𝓞 K))
    (a : (v.adicCompletion K)ˣ) :
    restrictAb L (le_maximalAbelianExtension L)
        (artinMap K Ω (IdeleClassGroup.mk K (finiteEmbedding v a))) = localSymbol L v a := by
  rw [restrictAb_artinMap, reciprocityMap_mk, ideleSymbol_finiteEmbedding]


end Local

end

end GroundTheory.Global
