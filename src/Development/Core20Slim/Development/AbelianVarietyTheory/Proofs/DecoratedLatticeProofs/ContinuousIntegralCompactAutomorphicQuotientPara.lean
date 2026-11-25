module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegrableOnFundamentalDomain
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Function
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.ZeroLEOne
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Analysis.Normed.Order.Lattice
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.Lattice
public import Mathlib.Order.Notation
public import Mathlib.Tactic.Linarith.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Positivity.Core
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.ContinuousOn
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Order.OrderClosed
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.CocompactParam

theorem eventually_close {G P : Type*} [TopologicalSpace G] [TopologicalSpace P] (K : G → P → ℂ)
    (hK : Continuous (Function.uncurry K)) {C : Set G} (hC : IsCompact C) (p₀ : P) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ p in nhds p₀, ∀ g ∈ C, ‖K g p - K g p₀‖ < ε := by
  refine hC.eventually_forall_of_forall_eventually (P := fun p g => ‖K g p - K g p₀‖ < ε) fun g _ => ?_
  have h1 : Continuous fun z : P × G => K z.2 z.1 := hK.comp (continuous_snd.prodMk continuous_fst)
  have h2 : Continuous fun z : P × G => K z.2 p₀ := hK.comp (continuous_snd.prodMk continuous_const)
  have hc : Continuous fun z : P × G => ‖K z.2 z.1 - K z.2 p₀‖ := (h1.sub h2).norm
  exact hc.continuousAt.eventually_lt continuousAt_const (by simpa using hε)

theorem continuous_setIntegral_of_unif {G P : Type*} [MeasurableSpace G] [TopologicalSpace P] (μ : Measure G)
    (𝓕 : Set G) (hfin : μ 𝓕 < ⊤) (K : G → P → ℂ) (hint : ∀ p, IntegrableOn (fun g => K g p) 𝓕 μ)
    (hcl : ∀ p₀, ∀ ε : ℝ, 0 < ε → ∀ᶠ p in nhds p₀, ∀ g, ‖K g p - K g p₀‖ < ε) :
    Continuous fun p => ∫ g in 𝓕, K g p ∂μ := by
  refine continuous_iff_continuousAt.2 fun p₀ => Metric.tendsto_nhds.2 fun ε hε => ?_
  have hm : 0 ≤ μ.real 𝓕 := measureReal_nonneg
  have hδ : 0 < ε / (μ.real 𝓕 + 1) := by positivity
  filter_upwards [hcl p₀ _ hδ] with p hp
  rw [dist_eq_norm, ← integral_sub (hint p) (hint p₀)]
  refine lt_of_le_of_lt (norm_setIntegral_le_of_norm_le_const hfin fun g _ => (hp g).le) ?_
  rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
  nlinarith

theorem continuous_integral_param : ∀ (D : D7) (V : HSp D), CoCpt V → ∀ (v : Vol V) (P : Type) [TopologicalSpace P] (K : GA D V → P → ℂ), Continuous (Function.uncurry K) → (∀ γ ∈ GQ V, ∀ g p, K (γ * g) p = K g p) → (∀ p, IntegrableOn (fun g => K g p) v.𝓕 v.μ) ∧ (Continuous fun p => ∫ g in v.𝓕, K g p ∂v.μ) ∧ ∀ p₀, ∃ C : ℝ, ∀ᶠ p in nhds p₀, ∀ g, ‖K g p‖ ≤ C := by
  intro D V hV v P _ K hK hinv
  obtain ⟨C, hC, hcov⟩ := hV
  have hcov' : ∀ h : GA D V, ∃ γ ∈ GQ V, ∃ c ∈ C, h = γ * c := fun h => by
    obtain ⟨γ, hγ, hc⟩ := hcov h
    exact ⟨γ⁻¹, inv_mem hγ, γ * h, hc, by rw [inv_mul_cancel_left]⟩
  have hcont : ∀ p, Continuous fun g => K g p := fun p => hK.comp (continuous_id.prodMk continuous_const)
  have hint : ∀ p, IntegrableOn (fun g => K g p) v.𝓕 v.μ := fun p =>
    GlobalTheory.CocompactIntegrable.integrableOn_fundamentalDomain V v.μ v.𝓕 C v.haar v.fund hC hcov' _ (hcont p)
      fun γ hγ h => hinv γ hγ h p
  have hfin : v.μ v.𝓕 < ⊤ := by
    have h1 := GlobalTheory.CocompactIntegrable.integrableOn_fundamentalDomain V v.μ v.𝓕 C v.haar v.fund hC hcov'
      (fun _ => (1 : ℂ)) continuous_const fun _ _ _ => rfl
    simpa using (integrableOn_const_iff (C := (1 : ℂ))).1 h1
  have hcl : ∀ p₀, ∀ ε : ℝ, 0 < ε → ∀ᶠ p in nhds p₀, ∀ g, ‖K g p - K g p₀‖ < ε := fun p₀ ε hε => by
    filter_upwards [eventually_close K hK hC p₀ hε] with p hp g
    obtain ⟨γ, hγ, hc⟩ := hcov g
    have := hp _ hc
    rwa [hinv γ hγ, hinv γ hγ] at this
  refine ⟨hint, continuous_setIntegral_of_unif v.μ v.𝓕 hfin K hint hcl, fun p₀ => ?_⟩
  obtain ⟨M, hM⟩ := hC.exists_bound_of_continuousOn (hcont p₀).continuousOn
  refine ⟨M + 1, ?_⟩
  filter_upwards [hcl p₀ 1 one_pos] with p hp g
  obtain ⟨γ, hγ, hc⟩ := hcov g
  have h0 := hM _ hc
  simp only [hinv γ hγ] at h0
  have := norm_sub_norm_le (K g p) (K g p₀)
  linarith [hp g]

end GlobalTheory.CocompactParam
