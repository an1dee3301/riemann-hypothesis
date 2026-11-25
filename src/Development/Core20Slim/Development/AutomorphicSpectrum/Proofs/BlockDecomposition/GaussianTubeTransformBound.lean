module

public import Mathlib
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.StripEntire
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GaussTubeOfTubeGood
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Init.Tactics
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.ZeroLEOne
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.MulAction
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.RCLike.Lemmas
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
public import Mathlib.MeasureTheory.OuterMeasure.AE
public import Mathlib.Order.Basic
public import Mathlib.Order.Filter.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Compactness.LocallyCompact
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open MeasureTheory Filter Topology PositivityTheory.RgEis GlobalTheory.CompanionTheory.TubeFourier

namespace GlobalTheory.CompanionTheory.TubeFourier

theorem integrable_gauss_one : Integrable (fun s : ℝ => Real.exp (-s ^ 2)) := by
  simpa using integrable_exp_neg_mul_sq (b := 1) one_pos

theorem integral_gauss_one : ∫ s : ℝ, Real.exp (-s ^ 2) = Real.sqrt Real.pi := by
  simpa using integral_gaussian 1

theorem integrable_gauss_prod :
    Integrable (fun y : ℝ × ℝ => Real.exp (-y.1 ^ 2) * Real.exp (-y.2 ^ 2)) :=
  Integrable.mul_prod integrable_gauss_one integrable_gauss_one

theorem integral_gauss_prod :
    ∫ y : ℝ × ℝ, Real.exp (-y.1 ^ 2) * Real.exp (-y.2 ^ 2) = Real.pi := by
  rw [Measure.volume_eq_prod, integral_prod_mul (fun s : ℝ => Real.exp (-s ^ 2)) (fun s : ℝ => Real.exp (-s ^ 2)),
    integral_gauss_one, Real.mul_self_sqrt Real.pi_pos.le]

theorem re_dot_pt (x y t : ℝ × ℝ) : (dot (pt x y) t).re = rdot x t := by
  simp [dot, pt, rdot, Complex.mul_re]

theorem norm_phi_le : ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] (G : ℂ × ℂ → X) (x : ℝ × ℝ) (M : ℝ),
    (∀ y : ℝ × ℝ, ‖G (pt x y)‖ ≤ M * Real.exp (-(y.1 ^ 2 + y.2 ^ 2))) →
    ∀ t : ℝ × ℝ, ‖phi G x t‖ ≤ M * Real.pi * Real.exp (-rdot x t) := by
  intro X _ _ G x M hG t
  have hb : ∀ y : ℝ × ℝ, ‖Complex.exp (-dot (pt x y) t) • G (pt x y)‖ ≤
      M * Real.exp (-rdot x t) * (Real.exp (-y.1 ^ 2) * Real.exp (-y.2 ^ 2)) := by
    intro y
    rw [norm_smul, Complex.norm_exp, Complex.neg_re, re_dot_pt]
    calc Real.exp (-rdot x t) * ‖G (pt x y)‖
        ≤ Real.exp (-rdot x t) * (M * Real.exp (-(y.1 ^ 2 + y.2 ^ 2))) :=
          mul_le_mul_of_nonneg_left (hG y) (Real.exp_pos _).le
      _ = M * Real.exp (-rdot x t) * (Real.exp (-y.1 ^ 2) * Real.exp (-y.2 ^ 2)) := by
          rw [neg_add, Real.exp_add]; ring
  unfold phi
  calc ‖∫ y : ℝ × ℝ, Complex.exp (-dot (pt x y) t) • G (pt x y)‖
      ≤ ∫ y : ℝ × ℝ, M * Real.exp (-rdot x t) * (Real.exp (-y.1 ^ 2) * Real.exp (-y.2 ^ 2)) :=
        norm_integral_le_of_norm_le (Integrable.const_mul integrable_gauss_prod _) (Eventually.of_forall hb)
    _ = M * Real.pi * Real.exp (-rdot x t) := by
        rw [integral_const_mul, integral_gauss_prod]; ring

end GlobalTheory.CompanionTheory.TubeFourier
