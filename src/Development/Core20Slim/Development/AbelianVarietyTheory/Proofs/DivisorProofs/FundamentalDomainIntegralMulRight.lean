module

public import Mathlib
public import Init.Core
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Actions
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
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
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.Logic.Function.Defs
public import Mathlib.MeasureTheory.Group.Arithmetic
public import Mathlib.MeasureTheory.Group.Defs
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Mathlib.MeasureTheory.Group.MeasurableEquiv
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.MeasurableSpace.Embedding
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open MeasureTheory

namespace GlobalTheory

theorem fundamentalDomain_integral_mul_right {G : Type} [Group G] [MeasurableSpace G]
    [MeasurableMul G] (μ : Measure G) [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant]
    (Γ : Subgroup G) [Countable Γ] (𝓕 : Set G) (f : G → ℂ) (a : G)
    (h : IsFundamentalDomain Γ 𝓕 μ) (hf : ∀ γ ∈ Γ, ∀ g, f (γ * g) = f g) :
    (IntegrableOn f 𝓕 μ ↔ IntegrableOn (fun g => f (g * a)) 𝓕 μ) ∧
      ∫ g in 𝓕, f (g * a) ∂μ = ∫ g in 𝓕, f g ∂μ := by
  have hmp : MeasurePreserving (fun g : G => g * a) μ μ := measurePreserving_mul_right μ a
  have hme : MeasurableEmbedding (fun g : G => g * a) := measurableEmbedding_mulRight a
  have h' : IsFundamentalDomain Γ ((fun g : G => g * a) ⁻¹' 𝓕) μ :=
    h.preimage_of_equiv (e := id) hmp.quasiMeasurePreserving Function.bijective_id
      (fun γ x => by simp [Subgroup.smul_def, mul_assoc])
  have hfa : ∀ (γ : Γ) (x : G), (fun g => f (g * a)) (γ • x) = (fun g => f (g * a)) x := by
    intro γ x
    simp only [Subgroup.smul_def, smul_eq_mul, mul_assoc]
    exact hf γ γ.2 _
  refine ⟨?_, ?_⟩
  · rw [h.integrableOn_iff h' (f := fun g => f (g * a)) hfa]
    exact (hmp.integrableOn_comp_preimage hme (f := f) (s := 𝓕)).symm
  · rw [h.setIntegral_eq h' (f := fun g => f (g * a)) hfa]
    exact hmp.setIntegral_preimage_emb hme f 𝓕

end GlobalTheory
