module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FderivCompress
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousFourierGau
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOscillatorActionOfGaussianPairings
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralGauTwistedConv
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowMulNormGauLe
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsQuadOfPlane
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Congr
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Calculus.FDeriv.Linear
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Operator.LinearIsometry
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.MetricSpace.Algebra
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Cauchy
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open MeasureTheory Complex Matrix GlobalTheory.RealWeil GlobalTheory.Mem.Lift
open scoped RealInnerProductSpace ContDiff Real ComplexOrder

namespace GlobalTheory.Mem.Lift.VacAnn

open MeasureTheory Complex Matrix in
open scoped RealInnerProductSpace ContDiff Real ComplexOrder in
private theorem hasFDerivAt_gau {V : Type} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] (w : V) :
    HasFDerivAt (_root_.GlobalTheory.RealWeil.gau : V → ℂ)
      ((-(Real.pi : ℂ) * _root_.GlobalTheory.RealWeil.gau w) • ((Complex.ofRealCLM).comp (innerSL ℝ w))) w := by
  have h1 : HasFDerivAt (fun u : V => ‖u‖ ^ 2) (2 • innerSL ℝ w) w := by
    simpa using (hasStrictFDerivAt_norm_sq w).hasFDerivAt
  have h2 := (Complex.ofRealCLM.hasFDerivAt).comp w h1
  have h3 := (h2.const_mul (-(Real.pi : ℂ) / 2)).cexp
  have hf : (_root_.GlobalTheory.RealWeil.gau : V → ℂ) =
      fun u => Complex.exp (-(Real.pi : ℂ) / 2 * ((‖u‖ ^ 2 : ℝ) : ℂ)) := by
    funext u; unfold _root_.GlobalTheory.RealWeil.gau; push_cast; ring_nf
  rw [hf]
  refine h3.congr_fderiv ?_
  ext y
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, Function.comp_apply,
    Complex.ofRealCLM_apply, innerSL_apply_apply, smul_eq_mul, nsmul_eq_mul,
    ContinuousLinearMap.coe_smul', Pi.smul_apply]
  push_cast
  ring


open MeasureTheory Complex Matrix in
open scoped RealInnerProductSpace ContDiff Real ComplexOrder in
theorem _root_.GlobalTheory.Mem.Lift.VacAnn.fderiv_gau_apply {V : Type} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] (w v : V) :
    fderiv ℝ (_root_.GlobalTheory.RealWeil.gau : V → ℂ) w v =
      -(Real.pi : ℂ) * ⟪w, v⟫ * _root_.GlobalTheory.RealWeil.gau w := by
  rw [(hasFDerivAt_gau w).fderiv]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    Complex.ofRealCLM_apply, innerSL_apply_apply, smul_eq_mul]
  ring


open MeasureTheory Complex Matrix in
open scoped RealInnerProductSpace ContDiff Real ComplexOrder in
theorem _root_.GlobalTheory.Mem.Lift.VacAnn.proj_annihilated : ∀ (V : Type) [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (B : Type)
    [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B] (J : V ≃ₗᵢ[ℝ] V)
    (ρ : V → B →L[ℂ] B), (∀ x, J (J x) = -x) →
    ∀ (h : _root_.GlobalTheory.RealWeil.IsHeis (_root_.GlobalTheory.RealWeil.omJ J) ρ) (x : B) (z : V),
      _root_.GlobalTheory.Mem.Lift.dH ρ z (_root_.GlobalTheory.RealWeil.proj h x) +
        I • _root_.GlobalTheory.Mem.Lift.dH ρ (J z) (_root_.GlobalTheory.RealWeil.proj h x) = 0 := by
  intro V _ _ _ _ _ B _ _ _ J ρ hJ h x z
  set P := _root_.GlobalTheory.RealWeil.proj h
  set f := P x with hf_def
  have hf : _root_.GlobalTheory.RealWeil.Sm ρ f :=
    _root_.GlobalTheory.RealWeil.Good.sm hJ
      (_root_.GlobalTheory.RealWeil.Osc.good_proj hJ h x)
  have hsand : ∀ w : V, P (ρ w f) = _root_.GlobalTheory.RealWeil.gau w • f := fun w =>
    _root_.GlobalTheory.RealWeil.proj_heis_proj hJ h w x
  have hcomp : ∀ w v : V, P (ρ w (_root_.GlobalTheory.Mem.Lift.dH ρ v f)) =
      ((Real.pi : ℂ) * I * (⟪w, J v⟫ : ℝ) * _root_.GlobalTheory.RealWeil.gau w
        - (Real.pi : ℂ) * (⟪w, v⟫ : ℝ) * _root_.GlobalTheory.RealWeil.gau w) • f := by
    intro w v
    rw [_root_.GlobalTheory.Mem.Lift.VacBd.heis_dH h hf v w, map_add (f := _), map_smul, hsand w,
      _root_.GlobalTheory.Mem.Lift.VacBd.fderiv_compress P hf _root_.GlobalTheory.RealWeil.contDiff_gau hsand w v,
      _root_.GlobalTheory.Mem.Lift.VacAnn.fderiv_gau_apply, smul_smul, ← add_smul]
    congr 1
    show (Real.pi : ℂ) * I * ((⟪w, J v⟫ : ℝ) : ℂ) * _root_.GlobalTheory.RealWeil.gau w
        + -(Real.pi : ℂ) * ((⟪w, v⟫ : ℝ) : ℂ) * _root_.GlobalTheory.RealWeil.gau w = _
    ring
  set G := _root_.GlobalTheory.Mem.Lift.dH ρ z f + I • _root_.GlobalTheory.Mem.Lift.dH ρ (J z) f
  have hG : _root_.GlobalTheory.RealWeil.Sm ρ G :=
    _root_.GlobalTheory.RealWeil.Osc.sm_add (_root_.GlobalTheory.Mem.Lift.VacBd.sm_dH h hf z)
      (_root_.GlobalTheory.RealWeil.Osc.sm_smul I (_root_.GlobalTheory.Mem.Lift.VacBd.sm_dH h hf (J z)))
  have hzero : ∀ w : V, P (ρ w G) = 0 := by
    intro w
    simp only [G, map_add (f := _), map_smul, hcomp, smul_smul, ← add_smul, hJ z, inner_neg_right]
    apply smul_eq_zero_of_left
    push_cast
    ring_nf
    rw [I_sq]
    ring
  rw [← (_root_.GlobalTheory.RealWeil.Osc.good_of_sm hJ h hG).inversion hJ]
  have hzero' : ∀ w : V, _root_.GlobalTheory.RealWeil.proj h (ρ (-w) G) = 0 := fun w => hzero (-w)
  simp only [hzero', map_zero, integral_zero]

end GlobalTheory.Mem.Lift.VacAnn
