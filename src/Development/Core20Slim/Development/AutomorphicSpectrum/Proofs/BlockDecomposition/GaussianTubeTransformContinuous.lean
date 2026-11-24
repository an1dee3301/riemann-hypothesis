module

public import Mathlib
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.StripEntire
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GaussTubeOfTubeGood
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Monoid.NatCast
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.ZeroLEOne
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.MulAction
public import Mathlib.Analysis.Normed.Order.Lattice
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.OuterMeasure.AE
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Filter.Basic
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.Filter.Tendsto
public import Mathlib.Order.Lattice
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.EMetricSpace.Defs
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Metrizable.Basic
public import Mathlib.Topology.Metrizable.Uniformity
public import Mathlib.Topology.Order.OrderClosed
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open MeasureTheory Filter Topology PositivityTheory.RgEis GlobalTheory.CompanionTheory.TubeFourier

namespace GlobalTheory.CompanionTheory.TubeFourier

theorem re_dot_pt_eq_rdot (x y t : ℝ × ℝ) : (dot (pt x y) t).re = rdot x t := by
  simp [dot, pt, rdot]

theorem integrable_gaussian_plane :
    Integrable (fun y : ℝ × ℝ => Real.exp (-(y.1 ^ 2 + y.2 ^ 2))) (volume : Measure (ℝ × ℝ)) := by
  have h1 : Integrable (fun x : ℝ => Real.exp (-1 * x ^ 2)) := integrable_exp_neg_mul_sq one_pos
  have h := h1.mul_prod h1
  have e : (fun y : ℝ × ℝ => Real.exp (-(y.1 ^ 2 + y.2 ^ 2))) =
      fun z : ℝ × ℝ => Real.exp (-1 * z.1 ^ 2) * Real.exp (-1 * z.2 ^ 2) := by
    funext z
    rw [← Real.exp_add]
    ring_nf
  rw [e]
  exact h

theorem phi_joint_continuous (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] (T : Type) [TopologicalSpace T]
    [FirstCountableTopology T] (G : T → ℂ × ℂ → X) (x : ℝ × ℝ)
    (hG : Continuous (fun p : (ℝ × ℝ) × T => G p.2 (pt x p.1)))
    (hb : ∀ g : T, ∃ U ∈ 𝓝 g, ∃ M : ℝ, ∀ g' ∈ U, ∀ y : ℝ × ℝ,
      ‖G g' (pt x y)‖ ≤ M * Real.exp (-(y.1 ^ 2 + y.2 ^ 2))) :
    Continuous (fun p : (ℝ × ℝ) × T => phi (G p.2) x p.1) := by
  have hform : ∀ y t : ℝ × ℝ, dot (pt x y) t =
      ((x.1 * t.1 + x.2 * t.2 : ℝ) : ℂ) + ((y.1 * t.1 + y.2 * t.2 : ℝ) : ℂ) * Complex.I := by
    intro y t
    apply Complex.ext <;> simp [dot, pt]
  have hdt : ∀ y : ℝ × ℝ, Continuous (fun t : ℝ × ℝ => Complex.exp (-dot (pt x y) t)) := by
    intro y
    simp_rw [hform]
    fun_prop
  have hdy : ∀ t : ℝ × ℝ, Continuous (fun y : ℝ × ℝ => Complex.exp (-dot (pt x y) t)) := by
    intro t
    simp_rw [hform]
    fun_prop
  have hnorm : ∀ y t : ℝ × ℝ, ‖Complex.exp (-dot (pt x y) t)‖ = Real.exp (-rdot x t) := by
    intro y t
    rw [Complex.norm_exp, Complex.neg_re, re_dot_pt_eq_rdot]
  rw [continuous_iff_continuousAt]
  intro p₀
  obtain ⟨U, hU, M, hM⟩ := hb p₀.2
  have hr : Continuous (fun p : (ℝ × ℝ) × T => Real.exp (-rdot x p.1)) := by
    unfold rdot
    fun_prop
  have hV : ∀ᶠ p in 𝓝 p₀, Real.exp (-rdot x p.1) < Real.exp (-rdot x p₀.1) + 1 :=
    (hr.tendsto p₀).eventually (eventually_lt_nhds (lt_add_one _))
  have hU' : ∀ᶠ p in 𝓝 p₀, p.2 ∈ U := continuous_snd.continuousAt.preimage_mem_nhds hU
  unfold phi
  refine continuousAt_of_dominated
    (bound := fun y => (Real.exp (-rdot x p₀.1) + 1) * (|M| * Real.exp (-(y.1 ^ 2 + y.2 ^ 2)))) ?_ ?_ ?_ ?_
  · refine Filter.Eventually.of_forall fun p => ?_
    apply Continuous.aestronglyMeasurable
    exact (hdy p.1).smul (hG.comp (continuous_id.prodMk continuous_const))
  · filter_upwards [hV, hU'] with p hp1 hp2
    refine Filter.Eventually.of_forall fun y => ?_
    rw [norm_smul, hnorm]
    have hg := hM p.2 hp2 y
    have hg' : ‖G p.2 (pt x y)‖ ≤ |M| * Real.exp (-(y.1 ^ 2 + y.2 ^ 2)) :=
      hg.trans (mul_le_mul_of_nonneg_right (le_abs_self M) (Real.exp_pos _).le)
    calc Real.exp (-rdot x p.1) * ‖G p.2 (pt x y)‖
        ≤ Real.exp (-rdot x p.1) * (|M| * Real.exp (-(y.1 ^ 2 + y.2 ^ 2))) :=
          mul_le_mul_of_nonneg_left hg' (Real.exp_pos _).le
      _ ≤ (Real.exp (-rdot x p₀.1) + 1) * (|M| * Real.exp (-(y.1 ^ 2 + y.2 ^ 2))) :=
          mul_le_mul_of_nonneg_right hp1.le (mul_nonneg (abs_nonneg M) (Real.exp_pos _).le)
  · exact (integrable_gaussian_plane.const_mul _).const_mul _
  · refine Filter.Eventually.of_forall fun y => ?_
    exact (((hdt y).comp continuous_fst).smul (hG.comp (continuous_const.prodMk continuous_snd))).continuousAt

end GlobalTheory.CompanionTheory.TubeFourier
