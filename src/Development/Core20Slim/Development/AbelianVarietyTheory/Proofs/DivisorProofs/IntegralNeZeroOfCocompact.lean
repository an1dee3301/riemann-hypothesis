module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReindexDblIncM
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.LagrInt
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.MeanSquareAddFundamentalDomainOfCocompact
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalMatricesDiscreteCocompactAdelicMatrixSpa
public import Formalism.LocalToGlobal.IndefiniteReal.DatumF
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pointwise.Set.Basic
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pointwise.Set.Scalar
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Actions
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Notation.Support
public import Mathlib.Algebra.Order.IsBotOne
public import Mathlib.Algebra.Order.Monoid.Canonical.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Countable.Defs
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
public import Mathlib.MeasureTheory.Group.Arithmetic
public import Mathlib.MeasureTheory.Group.Defs
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib.MeasureTheory.OuterMeasure.AE
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Filter.Basic
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Compactness.Lindelof
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.ContinuousOn
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.EMetricSpace.Defs
public import Mathlib.Topology.GDelta.MetrizableSpace
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.MetricSpace.Polish
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Metrizable.Basic
public import Mathlib.Topology.Metrizable.CompletelyMetrizable
public import Mathlib.Topology.Metrizable.Uniformity
public import Mathlib.Topology.Order
public import Mathlib.Topology.Separation.Basic
public import Mathlib.Topology.Separation.GDelta
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.Separation.Regular
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open scoped TensorProduct Matrix Pointwise
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

namespace GlobalTheory.PeriodicPositiveIntegral

theorem integral_ne_zero_of_cocompact {G : Type} [AddGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G] (Γ : AddSubgroup G) [Countable Γ] {K : Set G}
    (hK : IsCompact K) (hKc : ∀ x : G, ∃ γ ∈ Γ, γ + x ∈ K)
    (I : G → ℂ) (hI : Continuous I) (hper : ∀ γ ∈ Γ, ∀ u, I (γ + u) = I u)
    (hnn : ∀ u, 0 ≤ (I u).re) (h0 : 0 < (I 0).re) (ν : Measure G) [ν.IsAddHaarMeasure] (𝓕 : Set G)
    (h𝓕 : IsAddFundamentalDomain Γ 𝓕 ν) (hfin : ν 𝓕 < ⊤) : ∫ u in 𝓕, I u ∂ν ≠ 0 := by
  haveI : IsFiniteMeasure (ν.restrict 𝓕) := ⟨by rwa [Measure.restrict_apply_univ]⟩
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hI.continuousOn
  have hint : Integrable I (ν.restrict 𝓕) := by
    refine Integrable.of_bound hI.aestronglyMeasurable C (Filter.Eventually.of_forall fun w => ?_)
    obtain ⟨γ, hγ, h⟩ := hKc w
    rw [← hper γ hγ w]
    exact hC _ h
  have hcre : Continuous fun u => (I u).re := Complex.continuous_re.comp hI
  have hO : IsOpen (Function.support fun u => (I u).re) := hcre.isOpen_support
  have hpos : ν (Function.support fun u => (I u).re) ≠ 0 := hO.measure_ne_zero ν ⟨0, h0.ne'⟩
  intro hz
  have hre : ∫ u in 𝓕, (I u).re ∂ν = 0 := by
    have := integral_re (𝕜 := ℂ) hint
    rw [hz] at this
    simpa using this
  have hlt : 0 < ∫ u in 𝓕, (I u).re ∂ν := by
    rw [integral_pos_iff_support_of_nonneg_ae (Filter.Eventually.of_forall hnn) hint.re,
      Measure.restrict_apply hO.measurableSet, pos_iff_ne_zero]
    intro hm
    refine hpos (h𝓕.measure_zero_of_invariant _ (fun g => ?_) hm)
    ext u
    rw [Set.mem_vadd_set_iff_neg_vadd_mem]
    show (I (((-g : Γ) : G) + u)).re ≠ 0 ↔ (I u).re ≠ 0
    rw [hper _ (-g).2]
  exact hlt.ne' hre

theorem integral_ne_zero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (nS nT : ℕ)
    (I : WOF F E nS nT → ℂ), Continuous I → (∀ γ ∈ ratLF F E nS nT, ∀ u, I (γ + u) = I u) →
    (∀ u, 0 ≤ (I u).re) → 0 < (I 0).re →
    ∀ (ν : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT)), ν.IsAddHaarMeasure →
      IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 ν → ∫ u in 𝓕, I u ∂ν ≠ 0 := by
  intro F E _ _ _ _ _ nS nT I hI hper hnn h0 ν 𝓕 hν h𝓕
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := GlobalTheory.AdelicMatrixLatticeF.lattice F E nS nT
  haveI : BorelSpace (WOF F E nS nT) := ⟨rfl⟩
  haveI : Countable (ratLF F E nS nT) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  exact integral_ne_zero_of_cocompact (G := WOF F E nS nT) (ratLF F E nS nT) hK hKc I hI hper hnn h0 ν 𝓕 h𝓕
    (GlobalTheory.measure_addFundamentalDomain_lt_top_of_cocompact (G := WOF F E nS nT) (ratLF F E nS nT) hK hKc ν h𝓕)

end GlobalTheory.PeriodicPositiveIntegral
