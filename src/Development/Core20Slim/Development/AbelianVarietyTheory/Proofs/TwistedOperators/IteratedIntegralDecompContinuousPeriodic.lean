module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.MeanXMulStarRat
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.MeanSquareAddFundamentalDomainOfCocompact
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Actions
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Algebra.Torsor.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Countable.Defs
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib.MeasureTheory.OuterMeasure.AE
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Filter.Basic
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Tactic.Abel
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Group.Torsor
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Compactness.Lindelof
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.ContinuousOn
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.EMetricSpace.Defs
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.MetricSpace.Polish
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Metrizable.Basic
public import Mathlib.Topology.Metrizable.CompletelyMetrizable
public import Mathlib.Topology.Metrizable.Uniformity
public import Mathlib.Topology.Metrizable.Urysohn
public import Mathlib.Topology.Order
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.IsoMean

theorem iterInt_continuous_periodic : ∀ (D : D7) (V W : HSp D) (a b k : ℕ) (f₁ f₃ : Mx D a b → WO V W) (f₂ : Mx D 1 k → WO V W), Continuous f₁ → Continuous f₂ → Continuous f₃ → (∀ s s', f₁ (s + s') = f₁ s + f₁ s') → (∀ r ∈ GlobalTheory.MixModel.ratMx D a b, f₁ r ∈ ratL W V) → ∀ (μ : Measure (Mx D a b)) (𝓨 : Set (Mx D a b)), IsCovolOne (GlobalTheory.MixModel.ratMx D a b) μ 𝓨 → ∀ (η : Measure (Mx D 1 k)) (𝓩 : Set (Mx D 1 k)), η.IsAddHaarMeasure → IsAddFundamentalDomain (GlobalTheory.MixModel.ratMx D 1 k) 𝓩 η → ∀ T : WO V W → ℂ, Continuous T → (∀ γ ∈ ratL W V, ∀ u, T (γ + u) = T u) → Continuous (fun s => ∫ z in 𝓩, (∫ y in 𝓨, T (f₁ s + f₂ z + f₃ y) ∂μ) ∂η) ∧ ∀ r ∈ GlobalTheory.MixModel.ratMx D a b, ∀ s, ∫ z in 𝓩, (∫ y in 𝓨, T (f₁ (r + s) + f₂ z + f₃ y) ∂μ) ∂η = ∫ z in 𝓩, (∫ y in 𝓨, T (f₁ s + f₂ z + f₃ y) ∂μ) ∂η := by
  intro D V W a b k f₁ f₃ f₂ hf₁ hf₂ hf₃ hadd hrat μ 𝓨 hcov η 𝓩 hη h𝓩 T hT hper
  obtain ⟨-, -, hμ1⟩ := hcov

  obtain ⟨-, -, -, -, -, K, hK, hKcov⟩ := GlobalTheory.MixModel.lattice_Mx D W.rank V.rank
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn (f := T) hT.continuousOn
  have hbd : ∀ u, ‖T u‖ ≤ M := by
    intro u
    obtain ⟨γ, hγ, hγK⟩ := hKcov u
    have hγ' : γ ∈ ratL W V := by rw [GlobalTheory.MixModel.ratL_eq]; exact hγ
    rw [← hper γ hγ' u]
    exact hM _ hγK
  haveI : SecondCountableTopology (Mx D 1 k) := (GlobalTheory.MixModel.lattice_Mx D 1 k).2.2.1
  haveI : SecondCountableTopology (Mx D a b) := (GlobalTheory.MixModel.lattice_Mx D a b).2.2.1
  haveI : BorelSpace (Mx D 1 k) := ⟨rfl⟩
  haveI : BorelSpace (Mx D a b) := ⟨rfl⟩

  have hY : μ 𝓨 < ⊤ := by rw [hμ1]; exact ENNReal.one_lt_top
  have hZ : η 𝓩 < ⊤ := by
    obtain ⟨hg, -, hsc, -, hd, K', hK', hK'cov⟩ := GlobalTheory.MixModel.lattice_Mx D 1 k
    haveI : Countable (GlobalTheory.MixModel.ratMx D 1 k) :=
      TopologicalSpace.separableSpace_iff_countable.mp inferInstance
    exact GlobalTheory.measure_addFundamentalDomain_lt_top_of_cocompact _ hK' hK'cov η h𝓩
  haveI : IsFiniteMeasure (μ.restrict 𝓨) := ⟨by rw [Measure.restrict_apply_univ]; exact hY⟩
  haveI : IsFiniteMeasure (η.restrict 𝓩) := ⟨by rw [Measure.restrict_apply_univ]; exact hZ⟩

  have hIc : Continuous (fun p : Mx D a b × Mx D 1 k => ∫ y in 𝓨, T (f₁ p.1 + f₂ p.2 + f₃ y) ∂μ) := by
    set_option synthInstance.maxHeartbeats 200000 in
      refine continuous_of_dominated (bound := fun _ => M) ?_ ?_ (integrable_const M) ?_
    · intro p
      exact (hT.comp (continuous_const.add hf₃)).aestronglyMeasurable
    · intro p
      exact Filter.Eventually.of_forall fun y => hbd _
    · refine Filter.Eventually.of_forall fun y => hT.comp ?_
      exact ((hf₁.comp continuous_fst).add (hf₂.comp continuous_snd)).add continuous_const
  refine ⟨?_, ?_⟩
  · set_option synthInstance.maxHeartbeats 200000 in
      refine continuous_of_dominated (bound := fun _ => M * μ.real 𝓨) ?_ ?_ (integrable_const _) ?_
    · intro s
      exact (hIc.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
    · intro s
      exact Filter.Eventually.of_forall fun z =>
        norm_setIntegral_le_of_norm_le_const hY (fun y _ => hbd _)
    · exact Filter.Eventually.of_forall fun z => hIc.comp (continuous_id.prodMk continuous_const)
  · intro r hr s
    have h : ∀ z y, T (f₁ (r + s) + f₂ z + f₃ y) = T (f₁ s + f₂ z + f₃ y) := by
      intro z y
      have e : f₁ (r + s) + f₂ z + f₃ y = f₁ r + (f₁ s + f₂ z + f₃ y) := by
        rw [hadd]; abel
      rw [e, hper _ (hrat r hr)]
    simp only [h]

end GlobalTheory.IsoMean

end
