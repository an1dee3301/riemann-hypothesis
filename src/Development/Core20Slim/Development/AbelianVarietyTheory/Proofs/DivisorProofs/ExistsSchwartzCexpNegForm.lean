module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormIteratedFDerivTruncExpICompLe
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.Group.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.CompCLM
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Calculus.FDeriv.Linear
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Module.Multilinear.Basic
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.ENat.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Cast.Order.Basic
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Nat.Init
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Notation
public import Mathlib.Order.TypeTags
public import Mathlib.Tactic.Linarith.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Positivity.Core
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.Algebra.Module.Multilinear.Basic
public import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.UniformMulAction
public import Mathlib.Topology.MetricSpace.Algebra
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open scoped Matrix Nat

namespace GlobalTheory.GaussComplexForm

theorem exists_schwartz_cexp_neg_form : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (Q : V →L[ℝ] V →L[ℝ] ℂ) (c : ℝ),
    0 < c → (∀ x, c * ‖x‖ ^ 2 ≤ (Q x x).re) →
    ∃ g : SchwartzMap V ℂ, (∀ x, g x = Complex.exp (-(Q x x))) ∧ ∀ x p, fderiv ℝ (⇑g) x p = -(Q x p + Q p x) * g x := by
  intro V _ _ _ Q c hc hQ
  set B : V →L[ℝ] V →L[ℝ] ℂ := -Q with hBdef
  have hBapp : ∀ x y, B x y = -(Q x y) := fun x y => rfl
  have hB : ∀ x, (B x x).re ≤ -(c * ‖x‖ ^ 2) := by
    intro x; rw [hBapp, Complex.neg_re]; linarith [hQ x]
  have hq : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y : V => B y y) := B.contDiff.clm_apply contDiff_id
  have hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y : V => Complex.exp (B y y)) :=
    Complex.contDiff_exp.comp hq
  refine ⟨⟨fun y => Complex.exp (B y y), hg, ?_⟩, fun x => ?_, fun x p => ?_⟩
  · intro k n
    obtain ⟨C, hC⟩ := GlobalTheory.GaussExpSeries.exists_bound_poly_mul_exp c hc (k + 2 * n)
    refine ⟨n ! * (2 * (‖B‖ + 1)) ^ n * C, fun x => ?_⟩
    have hx0 := norm_nonneg x
    have hB0 := norm_nonneg B
    have hfb := GlobalTheory.GaussExpSeries.norm_iteratedFDeriv_gauss_le B c hB n x
    calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun y : V => Complex.exp (B y y)) x‖
        ≤ (1 + ‖x‖) ^ k * (n ! * Real.exp (-(c * ‖x‖ ^ 2)) * (2 * (‖B‖ + 1) * (1 + ‖x‖) ^ 2) ^ n) := by
          gcongr
          linarith
      _ = n ! * (2 * (‖B‖ + 1)) ^ n * ((1 + ‖x‖) ^ (k + 2 * n) * Real.exp (-(c * ‖x‖ ^ 2))) := by
          rw [show (2 * (‖B‖ + 1) * (1 + ‖x‖) ^ 2) ^ n = (2 * (‖B‖ + 1)) ^ n * (1 + ‖x‖) ^ (2 * n) by
            rw [mul_pow, pow_mul], pow_add]; ring
      _ ≤ n ! * (2 * (‖B‖ + 1)) ^ n * C := by gcongr; exact hC ‖x‖ hx0
  · show Complex.exp (B x x) = _
    rw [hBapp]
  · have h1 := (B.hasFDerivAt (x := x)).clm_apply (hasFDerivAt_id x)
    have h2 : HasFDerivAt (fun y : V => Complex.exp (B y y)) _ x := h1.cexp
    show fderiv ℝ (fun y : V => Complex.exp (B y y)) x p = -(Q x p + Q p x) * Complex.exp (B x x)
    rw [h2.fderiv]
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.flip_apply, ContinuousLinearMap.id_apply, id, smul_eq_mul, hBapp]
    ring

end GlobalTheory.GaussComplexForm
