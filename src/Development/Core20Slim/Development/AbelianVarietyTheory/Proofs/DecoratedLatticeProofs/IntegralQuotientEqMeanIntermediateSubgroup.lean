module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.KerBF
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.FlagMeasures.DiscreteSubgroupCountableAndExistsStrictFundamen
public import Init.Classical
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Actions
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Notation.Indicator
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Countable.Defs
public import Mathlib.Basic.ExistsUnique
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Dynamics.Ergodic.Action.Basic
public import Mathlib.Dynamics.Ergodic.Action.Regular
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Group.Arithmetic
public import Mathlib.MeasureTheory.Group.Defs
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.NullMeasurable
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Group.Subgroup
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Compactness.LocallyCompact
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Order
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.QuotFubini

theorem existsUnique_mul_mem {G : Type} [Group G] {Γ R : Subgroup G} (hΓ : Γ ≤ R) {S : Set G}
    (hS : ∀ g : G, ∃! γ : Γ, (γ : G) * g ∈ S) (h : G) (r : R) :
    ∃! γ : Γ.subgroupOf R, γ • r ∈ {r : R | (r : G) * h ∈ S} := by
  obtain ⟨γ, h1, h2⟩ := hS ((r : G) * h)
  refine ⟨⟨⟨γ, hΓ γ.2⟩, γ.2⟩, ?_, fun δ hδ => ?_⟩
  · change ((γ : G) * r) * h ∈ S
    rw [mul_assoc]; exact h1
  · have h3 : (⟨((δ : R) : G), δ.2⟩ : Γ) = γ := by
      refine h2 _ ?_
      have : (((δ : R) : G) * r) * h ∈ S := hδ
      rw [mul_assoc] at this
      exact this
    ext
    exact congrArg (fun x : Γ => (x : G)) h3

end GlobalTheory.QuotFubini

namespace GlobalTheory


open GlobalTheory.QuotFubini in
theorem quot_fubini_mean : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (R Γ : Subgroup G), Γ ≤ R → IsClosed (R : Set G) → Countable Γ → DiscreteTopology Γ → ∀ (μR : Measure R), μR.IsHaarMeasure → ∀ (𝓡 : Set R) (𝓑 : Set G), IsFundamentalDomain (Γ.subgroupOf R) 𝓡 μR → IsFundamentalDomain Γ 𝓑 μ → ∀ f : G → ℂ, Measurable f → (∀ γ ∈ Γ, ∀ g, f (γ * g) = f g) → IntegrableOn f 𝓑 μ → (∀ h, IntegrableOn (fun r : R => f (r * h)) 𝓡 μR) → IsQuotIntL1 μR μ (fun h => ∫ r in 𝓡, f ((r : G) * h) ∂μR) (∫ g in 𝓑, f g ∂μ) := by
  intro G _ _ _ _ _ _ _ _ μ _ R Γ hΓR hR hΓc hΓd μR hμR 𝓡 𝓑 h𝓡 h𝓑 f hf hfΓ hf𝓑 hf𝓡
  obtain ⟨-, S, hSm, hS⟩ := GlobalTheory.discreteSubgroup_countable_and_exists_strict_fundamentalDomain Γ
  have : Countable (Γ.subgroupOf R) :=
    (Subgroup.subgroupOfEquivOfLe hΓR).toEquiv.countable_iff.2 inferInstance
  have hSfd : IsFundamentalDomain Γ S μ := IsFundamentalDomain.mk' hSm.nullMeasurableSet hS
  have hfΓ' : ∀ (γ : Γ) (x : G), f (γ • x) = f x := fun γ x => hfΓ γ γ.2 x
  have hmh : ∀ h : G, Measurable (fun r : R => (r : G) * h) := fun h =>
    (continuous_subtype_val.mul continuous_const).measurable
  have hSh : ∀ h : G, MeasurableSet {r : R | (r : G) * h ∈ S} := fun h => hmh h hSm
  have hShfd : ∀ h : G, IsFundamentalDomain (Γ.subgroupOf R) {r : R | (r : G) * h ∈ S} μR := fun h =>
    IsFundamentalDomain.mk' (hSh h).nullMeasurableSet (existsUnique_mul_mem hΓR hS h)
  have hfR : ∀ h : G, ∀ (γ : Γ.subgroupOf R) (r : R), f (((γ • r : R) : G) * h) = f ((r : G) * h) := by
    intro h γ r
    change f ((((γ : R) : G) * r) * h) = _
    rw [mul_assoc]; exact hfΓ _ γ.2 _
  have hind : ∀ h : G, (fun r : R => S.indicator f ((r : G) * h)) =
      {r : R | (r : G) * h ∈ S}.indicator (fun r : R => f ((r : G) * h)) := by
    intro h; ext r
    by_cases hr : (r : G) * h ∈ S
    · rw [Set.indicator_of_mem hr, Set.indicator_of_mem (show r ∈ {r : R | (r : G) * h ∈ S} from hr)]
    · rw [Set.indicator_of_notMem hr, Set.indicator_of_notMem (show r ∉ {r : R | (r : G) * h ∈ S} from hr)]
  refine ⟨S.indicator f, ?_, fun h => ?_, fun h => ?_, ?_⟩
  · exact (integrable_indicator_iff hSm).2 ((hSfd.integrableOn_iff h𝓑 hfΓ').2 hf𝓑)
  · rw [hind h]
    exact (integrable_indicator_iff (hSh h)).2 (((hShfd h).integrableOn_iff h𝓡 (hfR h)).2 (hf𝓡 h))
  · rw [hind h, integral_indicator (hSh h)]
    exact (h𝓡.setIntegral_eq (hShfd h) (hfR h))
  · rw [integral_indicator hSm]
    exact h𝓑.setIntegral_eq hSfd hfΓ'

end GlobalTheory
