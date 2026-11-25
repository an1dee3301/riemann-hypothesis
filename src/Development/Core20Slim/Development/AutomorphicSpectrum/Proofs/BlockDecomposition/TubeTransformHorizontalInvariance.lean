module

public import Mathlib
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.StripEntire
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GaussTubeOfTubeGood
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContourShiftGaussianDecayStatement
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Ext
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Notation.Prod
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.Group.Abs
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.Ring.Unbundled.Basic
public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Algebra.Order.ZeroLEOne
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.MulAction
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.RCLike.Lemmas
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.Real.Star
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
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
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Filter.Basic
public import Mathlib.Order.Interval.Set.Basic
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Order.Lattice
public import Mathlib.Tactic.Linarith.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Compactness.LocallyCompact
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.ContinuousOn
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.EMetricSpace.Defs
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
public import Mathlib.Topology.Metrizable.Uniformity
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.UniformSpace.Cauchy
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology PositivityTheory.RgEis GlobalTheory.CompanionTheory.TubeFourier

namespace GlobalTheory.CompanionTheory.TubeFourier

variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X]

theorem shiftFst_bound {Ω : Set (ℝ × ℝ)} {G : ℂ × ℂ → X} (hG : GaussTube G Ω) {a b c : ℝ}
    (hs : ∀ s ∈ Set.Icc a b, (s, c) ∈ Ω) (t : ℝ × ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ l : ℂ × ℂ, l.1.re ∈ Set.Icc a b → l.2.re = c →
      ‖Complex.exp (-dot l t) • G l‖ ≤ M * Real.exp (-(l.1.im ^ 2 + l.2.im ^ 2)) := by
  have hC : IsCompact ((fun s : ℝ => (s, c)) '' Set.Icc a b) :=
    isCompact_Icc.image (Continuous.prodMk continuous_id continuous_const)
  have hCΩ : (fun s : ℝ => (s, c)) '' Set.Icc a b ⊆ Ω := by
    rintro _ ⟨s, hs', rfl⟩
    exact hs s hs'
  obtain ⟨M₀, hM₀⟩ := hG.3 _ hCΩ hC
  refine ⟨Real.exp ((|a| + |b|) * |t.1| + |c| * |t.2|) * |M₀|, by positivity, ?_⟩
  intro l hl hlc
  have hmem : l ∈ PositivityTheory.RgEis.tube ((fun s : ℝ => (s, c)) '' Set.Icc a b) := by
    show (l.1.re, l.2.re) ∈ (fun s : ℝ => (s, c)) '' Set.Icc a b
    exact ⟨l.1.re, hl, Prod.ext rfl hlc.symm⟩
  have hGl := hM₀ l hmem
  have hre : (-GlobalTheory.CompanionTheory.TubeFourier.dot l t).re = -(l.1.re * t.1 + l.2.re * t.2) := by
    simp [GlobalTheory.CompanionTheory.TubeFourier.dot]
  have hx : |l.1.re| ≤ |a| + |b| :=
    abs_le.2 ⟨by linarith [neg_abs_le a, abs_nonneg b, hl.1], by linarith [le_abs_self b, abs_nonneg a, hl.2]⟩
  have hexp : ‖Complex.exp (-GlobalTheory.CompanionTheory.TubeFourier.dot l t)‖ ≤
      Real.exp ((|a| + |b|) * |t.1| + |c| * |t.2|) := by
    rw [Complex.norm_exp, hre, hlc]
    apply Real.exp_le_exp.2
    have e1 : -(l.1.re * t.1) ≤ (|a| + |b|) * |t.1| := by
      calc -(l.1.re * t.1) ≤ |l.1.re * t.1| := neg_le_abs _
        _ = |l.1.re| * |t.1| := abs_mul _ _
        _ ≤ (|a| + |b|) * |t.1| := mul_le_mul_of_nonneg_right hx (abs_nonneg _)
    have e2 : -(c * t.2) ≤ |c| * |t.2| := by
      rw [← abs_mul]
      exact neg_le_abs _
    linarith
  rw [norm_smul]
  calc ‖Complex.exp (-GlobalTheory.CompanionTheory.TubeFourier.dot l t)‖ * ‖G l‖
      ≤ Real.exp ((|a| + |b|) * |t.1| + |c| * |t.2|) *
          (|M₀| * Real.exp (-(l.1.im ^ 2 + l.2.im ^ 2))) :=
        mul_le_mul hexp (hGl.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (Real.exp_pos _).le))
          (norm_nonneg _) (Real.exp_pos _).le
    _ = Real.exp ((|a| + |b|) * |t.1| + |c| * |t.2|) * |M₀| *
          Real.exp (-(l.1.im ^ 2 + l.2.im ^ 2)) := by ring

theorem integrable_exp_neg_sq_prod :
    Integrable (fun y : ℝ × ℝ => Real.exp (-y.1 ^ 2) * Real.exp (-y.2 ^ 2)) := by
  have h := (integrable_exp_neg_mul_sq one_pos).mul_prod (integrable_exp_neg_mul_sq one_pos)
  rw [← MeasureTheory.Measure.volume_eq_prod] at h
  refine h.congr (Filter.Eventually.of_forall fun y => ?_)
  simp only [neg_mul, one_mul]

theorem shiftFst_integrable {Ω : Set (ℝ × ℝ)} {G : ℂ × ℂ → X} (hG : GaussTube G Ω) {a b c : ℝ}
    (hs : ∀ s ∈ Set.Icc a b, (s, c) ∈ Ω) (t : ℝ × ℝ) {s : ℝ} (hsm : s ∈ Set.Icc a b) :
    Integrable (fun y : ℝ × ℝ => Complex.exp (-dot (pt (s, c) y) t) • G (pt (s, c) y)) := by
  obtain ⟨M, -, hM⟩ := GlobalTheory.CompanionTheory.TubeFourier.shiftFst_bound hG hs t
  have htp : Continuous (GlobalTheory.CompanionTheory.TubeFourier.pt (s, c)) := by
    have h : GlobalTheory.CompanionTheory.TubeFourier.pt (s, c) = fun y : ℝ × ℝ =>
        ((s : ℂ) + (y.1 : ℂ) * Complex.I, (c : ℂ) + (y.2 : ℂ) * Complex.I) := by
      funext y
      simp only [GlobalTheory.CompanionTheory.TubeFourier.pt, Complex.mk_eq_add_mul_I]
    rw [h]
    fun_prop
  have hmem : ∀ y, GlobalTheory.CompanionTheory.TubeFourier.pt (s, c) y ∈ PositivityTheory.RgEis.tube Ω := fun _ => hs s hsm
  have hGc : Continuous (fun y => G (GlobalTheory.CompanionTheory.TubeFourier.pt (s, c) y)) := hG.2.comp_continuous htp hmem
  have hpair : Continuous (fun l : ℂ × ℂ => GlobalTheory.CompanionTheory.TubeFourier.dot l t) := by
    simp only [GlobalTheory.CompanionTheory.TubeFourier.dot]
    fun_prop
  have hE : Continuous (fun y => Complex.exp (-GlobalTheory.CompanionTheory.TubeFourier.dot (GlobalTheory.CompanionTheory.TubeFourier.pt (s, c) y) t)) :=
    (hpair.comp htp).neg.cexp
  refine MeasureTheory.Integrable.mono'
    (GlobalTheory.CompanionTheory.TubeFourier.integrable_exp_neg_sq_prod.const_mul M)
    (hE.smul hGc).aestronglyMeasurable (Filter.Eventually.of_forall fun y => ?_)
  refine (hM (GlobalTheory.CompanionTheory.TubeFourier.pt (s, c) y) hsm rfl).trans (le_of_eq ?_)
  show M * Real.exp (-(y.1 ^ 2 + y.2 ^ 2)) = M * (Real.exp (-y.1 ^ 2) * Real.exp (-y.2 ^ 2))
  rw [← Real.exp_add]
  congr 2
  ring

theorem phi_eq_iterated {Ω : Set (ℝ × ℝ)} {G : ℂ × ℂ → X} (hG : GaussTube G Ω) {a b c : ℝ}
    (hs : ∀ s ∈ Set.Icc a b, (s, c) ∈ Ω) (t : ℝ × ℝ) {s : ℝ} (hsm : s ∈ Set.Icc a b) :
    phi G (s, c) t = ∫ y₂ : ℝ, ∫ y₁ : ℝ,
      Complex.exp (-dot (pt (s, c) (y₁, y₂)) t) • G (pt (s, c) (y₁, y₂)) := by
  have h := shiftFst_integrable hG hs t hsm
  unfold phi
  rw [Measure.volume_eq_prod] at h ⊢
  exact integral_prod_symm _ h

end GlobalTheory.CompanionTheory.TubeFourier

theorem GlobalTheory.CompanionTheory.TubeFourier.phi_shift_fst :
    ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X] (Ω : Set (ℝ × ℝ)) (G : ℂ × ℂ → X),
      GaussTube G Ω → ∀ a b c : ℝ, a ≤ b → (∀ s ∈ Set.Icc a b, (s, c) ∈ Ω) →
        ∀ t : ℝ × ℝ, phi G (a, c) t = phi G (b, c) t := by
  intro X _ _ _ Ω G hG a b c hab hs t
  rw [GlobalTheory.CompanionTheory.TubeFourier.phi_eq_iterated hG hs t (Set.left_mem_Icc.2 hab),
    GlobalTheory.CompanionTheory.TubeFourier.phi_eq_iterated hG hs t (Set.right_mem_Icc.2 hab)]
  obtain ⟨M, hM0, hM⟩ := GlobalTheory.CompanionTheory.TubeFourier.shiftFst_bound hG hs t
  refine integral_congr_ae (ae_of_all _ fun y₂ => ?_)
  have hline : DifferentiableOn ℂ (fun z : ℂ => G (z, ⟨c, y₂⟩)) {z : ℂ | z.re ∈ Set.Icc a b} := by
    have h1 := hG.1 ((0 : ℂ), (⟨c, y₂⟩ : ℂ)) ((1 : ℂ), (0 : ℂ))
    have heq : ∀ τ : ℂ, ((0 : ℂ), (⟨c, y₂⟩ : ℂ)) + τ • ((1 : ℂ), (0 : ℂ)) = (τ, ⟨c, y₂⟩) :=
      fun τ => Prod.ext (by simp) (by simp)
    simp only [heq] at h1
    refine h1.mono fun z hz => ?_
    exact hs z.re hz
  have hpair : Differentiable ℂ (fun z : ℂ => Complex.exp (-GlobalTheory.CompanionTheory.TubeFourier.dot (z, ⟨c, y₂⟩) t)) := by
    simp only [GlobalTheory.CompanionTheory.TubeFourier.dot]
    fun_prop
  have hdiff : DifferentiableOn ℂ
      (fun z : ℂ => Complex.exp (-GlobalTheory.CompanionTheory.TubeFourier.dot (z, ⟨c, y₂⟩) t) • G (z, ⟨c, y₂⟩))
      {z : ℂ | z.re ∈ Set.Icc a b} :=
    hpair.differentiableOn.smul hline
  have hbound : ∀ z : ℂ, z.re ∈ Set.Icc a b →
      ‖Complex.exp (-GlobalTheory.CompanionTheory.TubeFourier.dot (z, ⟨c, y₂⟩) t) • G (z, ⟨c, y₂⟩)‖ ≤
        M * Real.exp (-z.im ^ 2) := by
    intro z hz
    refine (hM (z, ⟨c, y₂⟩) hz rfl).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hM0)
    show -(z.im ^ 2 + y₂ ^ 2) ≤ -z.im ^ 2
    linarith [sq_nonneg y₂]
  exact GlobalTheory.T.contour_shift_gaussian_decay X
    (fun z : ℂ => Complex.exp (-GlobalTheory.CompanionTheory.TubeFourier.dot (z, ⟨c, y₂⟩) t) • G (z, ⟨c, y₂⟩))
    a b M hab hdiff hbound
