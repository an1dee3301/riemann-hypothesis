module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsScalarOfCommuteSchrodingerOperatorsStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.MultiplicativeHasDerivAtZeroStatement
public import Development.Core20Slim.GroundTheory.GlobalFields.TateThesis.GaussianSchwartz
public import Init.Classical
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.Analysis.Normed.Lp.WithLp
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.RCLike.Lemmas
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Countable.Defs
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.Order.Filter.Defs
public import Mathlib.Tactic.LinearCombination.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.GroupWithZero
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.EMetricSpace.Defs
public import Mathlib.Topology.GDelta.MetrizableSpace
public import Mathlib.Topology.MetricSpace.Algebra
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Metrizable.Uniformity
public import Mathlib.Topology.Separation.Basic
public import Mathlib.Topology.Separation.GDelta
public import Mathlib.Topology.Separation.Regular
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open GlobalTheory.RealWeil MeasureTheory
open scoped SchwartzMap Matrix

namespace GlobalTheory

theorem famChar_hasDerivAt : ∀ (l : Type) [Fintype l] (B : ℝ → (l ⊕ l → ℝ) → (l ⊕ l → ℝ)) (T U : ℝ → Sch l →ₗ[ℂ] Sch l) (Q : Sch l → EuclideanSpace ℝ l → ℂ), (∀ s t f, T (s + t) f = T s (T t f)) → (∀ f, T 0 f = f) → (∀ s t f, U (s + t) f = U s (U t f)) → (∀ f, U 0 f = f) → (∀ s t w, B (s + t) w = B s (B t w)) → (∀ w, B 0 w = w) → (∀ t w (f f₁ : Sch l), ⇑f₁ = rhoFun w ⇑f → ⇑(T t f₁) = rhoFun (B t w) ⇑(T t f)) → (∀ t w (f f₁ : Sch l), ⇑f₁ = rhoFun w ⇑f → ⇑(U t f₁) = rhoFun (B t w) ⇑(U t f)) → (∀ t f, ∫ x, ‖T t f x‖ ^ 2 = ∫ x, ‖f x‖ ^ 2) → (∀ t f, ∫ x, ‖U t f x‖ ^ 2 = ∫ x, ‖f x‖ ^ 2) → (∀ f y, Continuous fun t => T t f y) → (∀ f y, HasDerivAt (fun t => U t f y) (Q f y) 0) → ∃ c : ℂ, ∀ f y, HasDerivAt (fun t => T t f y) (Q f y + c * f y) 0 := by
  intro l _ B T U Q hT hT0 hU hU0 hB hB0 hTρ hUρ hTi hUi hTc hUd
  have hUinv : ∀ t f, U (-t) (U t f) = f := fun t f => by rw [← hU, neg_add_cancel, hU0]
  have hUinv' : ∀ t f, U t (U (-t) f) = f := fun t f => by rw [← hU, add_neg_cancel, hU0]

  have key : ∀ t, ∃ c : ℂ, ∀ f, T t f = c • U t f := by
    intro t
    obtain ⟨c, hc⟩ := GlobalTheory.T.exists_scalar_of_commute_schrodingerOperators l ((T t).comp (U (-t)))
      (fun f => by simp only [LinearMap.comp_apply]; rw [hTi, hUi])
      (fun w f f₁ h => by
        simp only [LinearMap.comp_apply]
        rw [hTρ t (B (-t) w) (U (-t) f) (U (-t) f₁) (hUρ (-t) w f f₁ h), ← hB, add_neg_cancel, hB0])
    refine ⟨c, fun f => ?_⟩
    have := hc (U t f)
    simp only [LinearMap.comp_apply, hUinv] at this
    exact this
  choose lam hlam using key
  set f₀ : Sch l := GroundTheory.Global.gaussianSchwartz (EuclideanSpace ℝ l)
  have hf₀ : f₀ 0 ≠ 0 := by simp [f₀]

  have hl0 : lam 0 = 1 := by
    have h := hlam 0 f₀
    rw [hT0, hU0] at h
    have h2 := congrArg (fun g : Sch l => g 0) h
    simp only [SchwartzMap.smul_apply, smul_eq_mul] at h2
    have : (lam 0 - 1) * f₀ 0 = 0 := by linear_combination -h2
    exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right hf₀)
  have hlmul : ∀ s t, lam (s + t) = lam s * lam t := by
    intro s t
    have h1 := hlam (s + t) (U (-(s + t)) f₀)
    rw [hUinv', hT, hlam t, map_smul, hlam s, ← hU, hUinv', smul_smul] at h1
    have h2 := congrArg (fun g : Sch l => g 0) h1
    simp only [SchwartzMap.smul_apply, smul_eq_mul] at h2
    have : (lam s * lam t - lam (s + t)) * f₀ 0 = 0 := by linear_combination h2
    exact (sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right hf₀)).symm

  have hd : ContinuousAt (fun t => U t f₀ 0) 0 := (hUd f₀ 0).continuousAt
  have hd0 : U 0 f₀ 0 ≠ 0 := by rw [hU0]; exact hf₀
  have hlc : ContinuousAt lam 0 := by
    have hq : ContinuousAt (fun t => T t f₀ 0 / U t f₀ 0) 0 :=
      ((hTc f₀ 0).continuousAt).div hd hd0
    refine hq.congr ?_
    filter_upwards [hd.eventually_ne hd0] with t ht
    rw [hlam t f₀, SchwartzMap.smul_apply, smul_eq_mul, mul_div_assoc, div_self ht, mul_one]

  obtain ⟨c, hc⟩ := GlobalTheory.T.exists_hasDerivAt_zero_of_continuousAt_of_map_add lam hl0 hlmul hlc
  refine ⟨c, fun f y => ?_⟩
  have hfun : (fun t => T t f y) = fun t => lam t * U t f y := by
    funext t; rw [hlam t f, SchwartzMap.smul_apply, smul_eq_mul]
  rw [hfun]
  have h := hc.mul (hUd f y)
  rw [hl0, hU0, one_mul, add_comm] at h
  exact h

end GlobalTheory
