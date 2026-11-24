module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairInfApply
public import Init.Core
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Distribution.DerivNotation
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
public import Mathlib.Analysis.Distribution.TemperateGrowth
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.Instances.RealVectorSpace
public import Mathlib.Topology.MetricSpace.Algebra
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Metrizable.Basic
public import Mathlib.Topology.Metrizable.Uniformity
public import Mathlib.Topology.UniformSpace.Defs
public import Mathlib.Topology.UniformSpace.Real

@[expose] public section

open MeasureTheory

namespace GlobalTheory

open LineDeriv

theorem dHeis_schwartz {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (β : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (w : V × V) (f : SchwartzMap V ℂ) :
    ∃ g : SchwartzMap V ℂ, ∀ x, g x = GlobalTheory.GaussLine.dHeis β w ⇑f x := by
  let L : V →L[ℝ] ℂ := Complex.ofRealCLM.comp (LinearMap.toContinuousLinearMap (β.flip w.2))
  have hL : Function.HasTemperateGrowth (fun x : V => (L x : ℂ)) := L.hasTemperateGrowth
  refine ⟨∂_{w.1} f - (2 * Real.pi * Complex.I) • SchwartzMap.smulLeftCLM ℂ (fun x : V => (L x : ℂ)) f, ?_⟩
  intro x
  rw [SchwartzMap.sub_apply, SchwartzMap.smul_apply, SchwartzMap.smulLeftCLM_apply_apply hL,
    SchwartzMap.lineDerivOp_apply_eq_fderiv]
  simp [GlobalTheory.GaussLine.dHeis, L, smul_eq_mul]
  ring

end GlobalTheory
