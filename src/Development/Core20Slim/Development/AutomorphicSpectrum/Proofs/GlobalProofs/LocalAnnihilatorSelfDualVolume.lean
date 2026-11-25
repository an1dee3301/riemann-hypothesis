module

public import Mathlib
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.GlobalProofs.CoefS
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.GlobalProofs.IntegralIndicatorCharOfTrivial
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.GlobalProofs.CharEqOneOfNear
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.SelfDualMap
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Subsemigroup.Defs
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Group.WithOne.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Set.CoeSort
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Set.Operations
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.Order.Filter.Cofinite
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.Filter.Pi
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Valuation
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Topology.Algebra.RestrictedProduct.Basic
public import Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace
public import Mathlib.Topology.Algebra.Valued.WithVal
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Maps.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Neighborhoods
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.Hypotheses₂.OneV GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test
open scoped TensorProduct ENNReal NNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test

theorem psiF_eq_one_of_int_of_vanish : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ),
    IsCharAF F ψ → ∃ T : Finset (HeightOneSpectrum (𝓞 F)), ∀ c : Af F,
      (∀ v, c v ∈ v.adicCompletionIntegers F) → (∀ v ∈ T, c v = 0) → psiF ψ c = 1 := by
  intro F _ _ ψ hψ
  classical
  have hcont : Continuous (psiF ψ) := by
    have h : Continuous (fun y : Af F => ψ ((0 : InfiniteAdeleRing F), y)) :=
      hψ.1.comp (continuous_const.prodMk continuous_id)
    exact h
  have hW : psiF ψ ⁻¹' Metric.ball (1 : ℂ) (1 / 2) ∈ nhds (0 : Af F) := by
    refine hcont.continuousAt.preimage_mem_nhds ?_
    rw [psiF_zero]
    exact Metric.ball_mem_nhds _ (by norm_num)
  let R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F
  let A := fun v : HeightOneSpectrum (𝓞 F) => (v.adicCompletionIntegers F : Set (v.adicCompletion F))
  have hc : Continuous (RestrictedProduct.structureMap R A Filter.cofinite) :=
    RestrictedProduct.isEmbedding_structureMap.continuous
  have hp : (RestrictedProduct.structureMap R A Filter.cofinite) ⁻¹' (psiF ψ ⁻¹' Metric.ball (1 : ℂ) (1 / 2)) ∈
      nhds (fun v => (0 : A v)) :=
    hc.continuousAt.preimage_mem_nhds hW
  rw [nhds_pi, Filter.mem_pi] at hp
  obtain ⟨I, hI, t, ht, hsub⟩ := hp
  refine ⟨hI.toFinset, fun c hint hT => ?_⟩
  let H : AddSubgroup (Af F) :=
    { carrier := {y | (∀ v, y v ∈ v.adicCompletionIntegers F) ∧ ∀ v ∈ hI.toFinset, y v = 0}
      add_mem' := by
        intro a b ha hb
        refine ⟨fun v => ?_, fun v hv => ?_⟩
        · change a v + b v ∈ v.adicCompletionIntegers F
          exact add_mem (ha.1 v) (hb.1 v)
        · change a v + b v = 0
          rw [ha.2 v hv, hb.2 v hv, add_zero]
      zero_mem' := ⟨fun v => zero_mem _, fun v _ => rfl⟩
      neg_mem' := by
        intro a ha
        refine ⟨fun v => ?_, fun v hv => ?_⟩
        · change -(a v) ∈ v.adicCompletionIntegers F
          exact neg_mem (ha.1 v)
        · change -(a v) = 0
          rw [ha.2 v hv, neg_zero] }
  have hs : ∀ y ∈ H, ‖psiF ψ y - 1‖ < 1 / 2 := by
    intro y hy
    have hmem : (fun v => (⟨y v, hy.1 v⟩ : A v)) ∈
        (RestrictedProduct.structureMap R A Filter.cofinite) ⁻¹' (psiF ψ ⁻¹' Metric.ball (1 : ℂ) (1 / 2)) := by
      refine hsub fun v hv => ?_
      have h0 : (⟨y v, hy.1 v⟩ : A v) = (0 : A v) :=
        Subtype.ext (hy.2 v (by simpa using hv))
      rw [h0]
      exact mem_of_mem_nhds (ht v)
    have he : RestrictedProduct.structureMap R A Filter.cofinite (fun v => (⟨y v, hy.1 v⟩ : A v)) = y :=
      by ext v; rfl
    have h2 : psiF ψ y ∈ Metric.ball (1 : ℂ) (1 / 2) := by
      rw [← he]
      exact hmem
    rw [Metric.mem_ball, dist_eq_norm] at h2
    exact h2
  exact char_eq_one_of_near H (psiF ψ) (psiF_zero ψ) (psiF_add ψ) hs (x := c) ⟨hint, hT⟩

end GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test
