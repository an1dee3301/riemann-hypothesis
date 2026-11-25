module

public import Mathlib
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitHomeoApply
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SProd
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Image
public import Mathlib.Data.Set.Operations
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Map
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.MeasurableSpace.Embedding
public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.NullMeasurable
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Compactness.LocallyCompact
public import Mathlib.Topology.Compactness.SigmaCompact
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.Topology.Separation.Basic
public import Mathlib.Topology.Separation.Hausdorff

@[expose] public section

open MeasureTheory Topology
open scoped ENNReal NNReal Matrix Pointwise

namespace GlobalTheory.CompanionTheory.SplitExtLat

theorem setLIntegral_splitHomeo_image_prod
    (P G₁ : Type) [Group P] [TopologicalSpace P] [IsTopologicalGroup P] [LocallyCompactSpace P]
    [SecondCountableTopology P] [T2Space P] [MeasurableSpace P] [BorelSpace P]
    [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁] [LocallyCompactSpace G₁]
    [SecondCountableTopology G₁] [T2Space G₁] [MeasurableSpace G₁] [BorelSpace G₁]
    (ι : G₁ →* P) (π : P →* G₁) (hι : Continuous ι) (hπ : Continuous π)
    (hπι : ∀ u, π (ι u) = u) (ν : Measure π.ker) [ν.IsHaarMeasure]
    (μ₁ : Measure G₁) [μ₁.IsHaarMeasure] (D : Set π.ker) (𝓕₁ : Set G₁) :
    MeasurableSet D → NullMeasurableSet 𝓕₁ μ₁ →
      NullMeasurableSet (GlobalTheory.CompanionTheory.SplitExtLat.splitHomeo ι π hι hπ hπι '' (D ×ˢ 𝓕₁))
        (Measure.map (GlobalTheory.CompanionTheory.SplitExtLat.splitHomeo ι π hι hπ hπι) (ν.prod μ₁)) ∧
      ∀ f : P → ℝ≥0∞, Measurable f →
        ∫⁻ p in (GlobalTheory.CompanionTheory.SplitExtLat.splitHomeo ι π hι hπ hπι '' (D ×ˢ 𝓕₁)), f p
            ∂(Measure.map (GlobalTheory.CompanionTheory.SplitExtLat.splitHomeo ι π hι hπ hπι) (ν.prod μ₁)) =
          ∫⁻ u in 𝓕₁, ∫⁻ m in D, f ((m : P) * ι u) ∂ν ∂μ₁ := by
  intro hD h𝓕
  have hker : IsClosed ((π.ker : Set P)) := by
    rw [MonoidHom.coe_ker]
    exact isClosed_singleton.preimage hπ
  have hsc : SecondCountableTopology π.ker :=
    TopologicalSpace.Subtype.secondCountableTopology (π.ker : Set P)
  have hlc : LocallyCompactSpace π.ker := hker.locallyCompactSpace
  have hσc : SigmaCompactSpace π.ker := sigmaCompactSpace_of_locallyCompact_secondCountable
  have hνσ : SigmaFinite ν := Measure.IsHaarMeasure.sigmaFinite ν
  set e := GlobalTheory.CompanionTheory.SplitExtLat.splitHomeo ι π hι hπ hπι with he
  have hemb : MeasurableEmbedding e := e.measurableEmbedding
  refine ⟨?_, ?_⟩
  · rw [e.image_eq_preimage_symm]
    exact (hD.nullMeasurableSet.prod h𝓕).preimage
      (MeasurableEquiv.quasiMeasurePreserving_symm (ν.prod μ₁) e.toMeasurableEquiv)
  · intro f hf
    rw [hemb.restrict_map, Set.preimage_image_eq _ e.injective, hemb.lintegral_map,
      ← Measure.prod_restrict, lintegral_prod_symm']
    · rfl
    · exact hf.comp hemb.measurable

end GlobalTheory.CompanionTheory.SplitExtLat
