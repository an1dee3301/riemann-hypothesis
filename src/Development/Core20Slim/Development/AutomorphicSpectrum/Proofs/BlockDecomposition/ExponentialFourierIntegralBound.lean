module

public import Mathlib
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.StripEntire
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GaussTubeOfTubeGood
public import Batteries.Logic
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Ring.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.MulAction
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.RCLike.Lemmas
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
public import Mathlib.MeasureTheory.OuterMeasure.AE
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Filter.Basic
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Tactic.FieldSimp.Lemmas
public import Mathlib.Tactic.Linarith.Lemmas
public import Mathlib.Tactic.LinearCombination.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Positivity.Core
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Compactness.LocallyCompact
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.EMetricSpace.Defs
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Metrizable.Uniformity
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology PositivityTheory.RgEis GlobalTheory.CompanionTheory.TubeFourier

namespace GlobalTheory.CompanionTheory.TubeFourier

theorem integral_exp_neg_mul_abs {ε : ℝ} (hε : 0 < ε) :
    ∫ u : ℝ, Real.exp (-ε * |u|) = 2 / ε := by
  have h := integral_comp_abs (f := fun x => Real.exp (-ε * x))
  rw [h, integral_exp_mul_Ioi (by linarith) 0, mul_zero, Real.exp_zero]
  field_simp

theorem integrable_exp_neg_mul_abs {ε : ℝ} (hε : 0 < ε) :
    Integrable fun u : ℝ => Real.exp (-ε * |u|) := by
  refine Integrable.of_integral_ne_zero ?_
  rw [integral_exp_neg_mul_abs hε]
  positivity

theorem integrable_and_norm_integral_le (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X]
    (φ : ℝ × ℝ → X) (l : ℂ × ℂ) (ε M : ℝ) (hε : 0 < ε) (hφ : Continuous φ)
    (hb : ∀ t : ℝ × ℝ, ‖φ t‖ ≤ M * Real.exp (-rdot (l.1.re, l.2.re) t) *
      Real.exp (-ε * (|t.1| + |t.2|))) :
    Integrable (fun t : ℝ × ℝ => Complex.exp (dot l t) • φ t) ∧
      ‖∫ t : ℝ × ℝ, Complex.exp (dot l t) • φ t‖ ≤ M * (2 / ε) ^ 2 := by
  have hg1 := integrable_exp_neg_mul_abs hε
  have hgi : Integrable (fun t : ℝ × ℝ => M * (Real.exp (-ε * |t.1|) * Real.exp (-ε * |t.2|))) :=
    (hg1.mul_prod hg1).const_mul M
  have hbound : ∀ t : ℝ × ℝ, ‖Complex.exp (dot l t) • φ t‖ ≤
      M * (Real.exp (-ε * |t.1|) * Real.exp (-ε * |t.2|)) := by
    intro t
    rw [norm_smul, Complex.norm_exp]
    have hre : (dot l t).re = rdot (l.1.re, l.2.re) t := by simp [dot, rdot]
    rw [hre]
    have h1 : Real.exp (rdot (l.1.re, l.2.re) t) * Real.exp (-rdot (l.1.re, l.2.re) t) = 1 := by
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    have h2 : Real.exp (-ε * (|t.1| + |t.2|)) = Real.exp (-ε * |t.1|) * Real.exp (-ε * |t.2|) := by
      rw [← Real.exp_add]; ring_nf
    calc Real.exp (rdot (l.1.re, l.2.re) t) * ‖φ t‖
        ≤ Real.exp (rdot (l.1.re, l.2.re) t) * (M * Real.exp (-rdot (l.1.re, l.2.re) t) *
          Real.exp (-ε * (|t.1| + |t.2|))) := mul_le_mul_of_nonneg_left (hb t) (Real.exp_pos _).le
      _ = M * (Real.exp (-ε * |t.1|) * Real.exp (-ε * |t.2|)) := by
        rw [h2]
        linear_combination (M * (Real.exp (-ε * |t.1|) * Real.exp (-ε * |t.2|))) * h1
  have hc : Continuous (fun t : ℝ × ℝ => Complex.exp (dot l t) • φ t) := by
    have hd : Continuous (fun t : ℝ × ℝ => dot l t) := by simp only [dot]; fun_prop
    exact (Complex.continuous_exp.comp hd).smul hφ
  refine ⟨hgi.mono' hc.aestronglyMeasurable (Filter.Eventually.of_forall hbound), ?_⟩
  calc ‖∫ t : ℝ × ℝ, Complex.exp (dot l t) • φ t‖
      ≤ ∫ t : ℝ × ℝ, M * (Real.exp (-ε * |t.1|) * Real.exp (-ε * |t.2|)) :=
        norm_integral_le_of_norm_le hgi (Filter.Eventually.of_forall hbound)
    _ = M * (2 / ε) ^ 2 := by
        rw [integral_const_mul, Measure.volume_eq_prod,
          integral_prod_mul (fun u : ℝ => Real.exp (-ε * |u|)) (fun u : ℝ => Real.exp (-ε * |u|)),
          integral_exp_neg_mul_abs hε]
        ring

end GlobalTheory.CompanionTheory.TubeFourier
