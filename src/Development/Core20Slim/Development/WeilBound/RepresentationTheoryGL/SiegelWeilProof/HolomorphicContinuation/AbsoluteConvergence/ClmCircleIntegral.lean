module

public import Mathlib
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.BanachHol
public import Init.Classical
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Torsor.Defs
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.CStarAlgebra.ContinuousMap
public import Mathlib.Analysis.Calculus.DSlope
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Congr
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Complex.RemovableSingularity
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SProd
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Set.BooleanAlgebra
public import Mathlib.Data.Set.CoeSort
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Data.Set.Restrict
public import Mathlib.Data.Subtype
public import Mathlib.LinearAlgebra.AffineSpace.Slope
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Integral.CircleIntegral
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.Order.Basic
public import Mathlib.Order.CompleteBooleanAlgebra
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Filter.Basic
public import Mathlib.Order.Filter.Defs
public import Mathlib.Tactic.Linarith.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.GroupWithZero
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.CompactOpen
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Compactness.CompactlyCoherentSpace
public import Mathlib.Topology.Compactness.LocallyCompact
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.ContinuousMap.Algebra
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.ContinuousMap.Defs
public import Mathlib.Topology.ContinuousOn
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Hom.ContinuousEval
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Neighborhoods
public import Mathlib.Topology.NhdsWithin
public import Mathlib.Topology.Separation.Basic
public import Mathlib.Topology.Separation.CompletelyRegular
public import Mathlib.Topology.Separation.Regular
public import Mathlib.Topology.UniformSpace.Cauchy
public import Mathlib.Topology.UniformSpace.CompactConvergence
public import Mathlib.Topology.UniformSpace.Defs
public import Mathlib.Topology.UniformSpace.Uniformizable

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology Metric Complex Real

namespace PositivityTheory.Rg.Sw.AbsSt

theorem clm_circleIntegral {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F] (L : E →L[ℂ] F) {f : ℂ → E} {c : ℂ} {R : ℝ}
    (hf : CircleIntegrable f c R) : L (∮ z in C(c, R), f z) = ∮ z in C(c, R), L (f z) := by
  unfold circleIntegral
  rw [← ContinuousLinearMap.intervalIntegral_comp_comm L hf.out]
  congr 1
  funext θ
  exact L.map_smul _ _

theorem banachHol : BanachHol := by
  intro X _ _ U F hU hF hd
  have hG : Continuous (fun p : U × X => F p.1.1 p.2) :=
    hF.comp_continuous ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
      (fun p => ⟨p.1.2, mem_univ _⟩)
  let K : C(U, C(X, ℂ)) := (⟨_, hG⟩ : C(U × X, ℂ)).curry
  classical
  let Φ : ℂ → C(X, ℂ) := fun z => if h : z ∈ U then K ⟨z, h⟩ else 0
  have hΦ : ∀ z ∈ U, ∀ x, Φ z x = F z x := by
    intro z hz x
    simp [Φ, K, hz]
  have hc : ContinuousOn Φ U := by
    rw [continuousOn_iff_continuous_restrict]
    convert K.continuous using 1
    funext z
    show Φ z = K z
    simp only [Φ, dif_pos z.2, Subtype.coe_eta]
  refine ⟨Φ, ?_, hΦ⟩
  intro w hw
  apply DifferentiableAt.differentiableWithinAt
  obtain ⟨R, hR0, hRU⟩ : ∃ R > 0, closedBall w R ⊆ U := by
    obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.mp hU w hw
    exact ⟨ε / 2, half_pos hε, (closedBall_subset_ball (half_lt_self hε)).trans hεU⟩
  let R' : NNReal := ⟨R, hR0.le⟩
  have hsph : sphere w R ⊆ U := sphere_subset_closedBall.trans hRU
  have hint : CircleIntegrable Φ w R' := (hc.mono hsph).circleIntegrable hR0.le
  have hps := hasFPowerSeriesOn_cauchy_integral hint (show (0 : NNReal) < R' from hR0)
  have heq : Φ =ᶠ[𝓝 w] (fun v => (2 * ↑π * I)⁻¹ • ∮ z in C(w, ↑R'), (z - v)⁻¹ • Φ z) := by
    filter_upwards [ball_mem_nhds w hR0] with v hv
    ext x
    show Φ v x = ((2 * ↑π * I)⁻¹ • ∮ z in C(w, R), (z - v)⁻¹ • Φ z) x
    have ha : ContinuousOn (fun z : ℂ => (z - v)⁻¹) (sphere w R) := by
      apply ContinuousOn.inv₀ (continuousOn_id.sub continuousOn_const)
      intro z hz h
      have hzv : z = v := sub_eq_zero.mp h
      subst hzv
      rw [mem_sphere] at hz
      rw [mem_ball] at hv
      linarith
    have hcv : ContinuousOn (fun z => (z - v)⁻¹ • Φ z) (sphere w R) :=
      ContinuousOn.smul (f := fun z : ℂ => (z - v)⁻¹) (g := Φ) ha (hc.mono hsph)
    have h1 := clm_circleIntegral (ContinuousMap.evalCLM ℂ x) (hcv.circleIntegrable hR0.le)
    simp only [ContinuousMap.evalCLM_apply, ContinuousMap.smul_apply] at h1
    have h2 : (∮ z in C(w, R), (z - v)⁻¹ • Φ z) x = ∮ z in C(w, R), (z - v)⁻¹ • F z x := by
      rw [h1]
      apply circleIntegral.integral_congr hR0.le
      intro z hz
      simp only
      rw [hΦ z (hsph hz) x]
    have h3 := ((hd x).mono hRU).circleIntegral_sub_inv_smul hv
    rw [ContinuousMap.smul_apply, h2, h3, smul_smul, inv_mul_cancel₀ two_pi_I_ne_zero, one_smul,
      hΦ v (hRU (ball_subset_closedBall hv))]
  exact hps.analyticAt.differentiableAt.congr_of_eventuallyEq heq

theorem dslopeFam : DslopeFam := by
  intro X _ _ U s₀ F hU hs hF hd h0
  have hU0 : U ∈ 𝓝 s₀ := hU.mem_nhds hs
  refine ⟨?_, fun x => (differentiableOn_dslope hU0).mpr (hd x)⟩
  rintro ⟨z₀, x₀⟩ hp
  have hz₀ : z₀ ∈ U := hp.1
  obtain ⟨K, hKc, hKn⟩ := exists_compact_mem_nhds x₀
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hKc
  have hF' : ContinuousOn (fun y : ℂ × K => F y.1 y.2) (U ×ˢ univ) :=
    hF.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)).continuousOn
      (fun y hy => ⟨hy.1, mem_univ _⟩)
  obtain ⟨Φ, hΦd, hΦ⟩ := banachHol (↥K) U (fun z (y : ↥K) => F z y) hU hF' (fun y => hd y)
  have hD : ContinuousOn (dslope Φ s₀) U := ((differentiableOn_dslope hU0).mpr hΦd).continuousOn
  have hval : ∀ z ∈ U, ∀ y : K, dslope Φ s₀ z y = dslope (fun z => F z y) s₀ z := by
    intro z hz y
    have heqon : EqOn (fun z => F z y) ((ContinuousMap.evalCLM ℂ y) ∘ Φ) U := by
      intro u hu
      simp [hΦ u hu y]
    rw [show dslope Φ s₀ z y = ContinuousMap.evalCLM ℂ y (dslope Φ s₀ z) from rfl,
      ← ContinuousLinearMap.dslope_comp _ _ _ _ (fun _ => (hΦd s₀ hs).differentiableAt hU0)]
    by_cases hzs : z = s₀
    · rw [hzs, dslope_same, dslope_same]
      exact (Filter.eventuallyEq_of_mem hU0 heqon).deriv_eq.symm
    · rw [dslope_of_ne _ hzs, dslope_of_ne _ hzs]
      simp [slope_def_field, hΦ z hz y, hΦ s₀ hs y]
  have hcont : ContinuousOn (fun y : ℂ × X => dslope (fun z => F z y.2) s₀ y.1) (U ×ˢ K) := by
    rw [continuousOn_iff_continuous_restrict]
    have hDr : Continuous (fun q : ↥(U ×ˢ K) => dslope Φ s₀ q.1.1) :=
      hD.comp_continuous (continuous_fst.comp continuous_subtype_val) (fun q => q.2.1)
    have hKr : Continuous (fun q : ↥(U ×ˢ K) => (⟨q.1.2, q.2.2⟩ : K)) :=
      (continuous_snd.comp continuous_subtype_val).subtype_mk _
    convert continuous_eval.comp (hDr.prodMk hKr) using 1
    funext q
    exact (hval q.1.1 q.2.1 ⟨q.1.2, q.2.2⟩).symm
  have hmem : U ×ˢ K ∈ 𝓝[U ×ˢ univ] (z₀, x₀) := by
    have hsub : (U ×ˢ univ) ∩ (univ ×ˢ K) ⊆ U ×ˢ K := fun q hq => ⟨hq.1.1, hq.2.2⟩
    exact mem_of_superset (inter_mem_nhdsWithin _ (prod_mem_nhds univ_mem hKn)) hsub
  exact (hcont (z₀, x₀) ⟨hz₀, mem_of_mem_nhds hKn⟩).mono_of_mem_nhdsWithin hmem

end PositivityTheory.Rg.Sw.AbsSt
