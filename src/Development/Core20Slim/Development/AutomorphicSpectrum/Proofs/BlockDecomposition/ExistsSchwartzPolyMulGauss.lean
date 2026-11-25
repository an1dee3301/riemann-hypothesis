module

public import Mathlib
public import Development.Core20Slim.GroundTheory.GlobalFields.TateThesis.GaussianSchwartz
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Basic
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.Distribution.TemperateGrowth
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.Analysis.Normed.Lp.WithLp
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.MulAction
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Complex.BigOperators
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Lattice
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Positivity.Core
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd
public import Mathlib.Topology.Algebra.Module.Equiv.Basic
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Instances.RealVectorSpace
public import Mathlib.Topology.MetricSpace.Algebra
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Metrizable.Basic
public import Mathlib.Topology.Metrizable.Uniformity
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.UniformSpace.Defs
public import Mathlib.Topology.UniformSpace.Real

@[expose] public section

noncomputable section

namespace GlobalTheory.CompanionTheory.PolyGaussSchwartz

variable {m n : ℕ}

def coord (k : Fin m × Fin n × Bool) (u : Fin m → Fin n → ℂ) : ℂ :=
  if k.2.2 then star (u k.1 k.2.1) else u k.1 k.2.1

def entryL (a : Fin m) (i : Fin n) : (Fin m → Fin n → ℂ) →L[ℝ] ℂ :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℂ) i).comp
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => Fin n → ℂ) a)

theorem coord_temperate (k : Fin m × Fin n × Bool) :
    Function.HasTemperateGrowth (coord k) := by
  obtain ⟨a, i, b⟩ := k
  cases b
  · exact (entryL a i).hasTemperateGrowth
  · exact ((Complex.conjCLE : ℂ →L[ℝ] ℂ).comp (entryL a i)).hasTemperateGrowth

theorem eval_temperate (P : MvPolynomial (Fin m × Fin n × Bool) ℂ) :
    Function.HasTemperateGrowth (fun u => MvPolynomial.eval (fun k => coord k u) P) := by
  induction P using MvPolynomial.induction_on with
  | C a =>
    have : (fun u : Fin m → Fin n → ℂ =>
        MvPolynomial.eval (fun k => coord k u) (MvPolynomial.C a)) = fun _ => a := by
      funext u; simp
    rw [this]; exact Function.HasTemperateGrowth.const a
  | add p q hp hq =>
    have : (fun u : Fin m → Fin n → ℂ => MvPolynomial.eval (fun k => coord k u) (p + q)) =
        fun u => MvPolynomial.eval (fun k => coord k u) p +
          MvPolynomial.eval (fun k => coord k u) q := by
      funext u; simp
    rw [this]; exact hp.add hq
  | mul_X p k hp =>
    have : (fun u : Fin m → Fin n → ℂ =>
        MvPolynomial.eval (fun k => coord k u) (p * MvPolynomial.X k)) =
        fun u => MvPolynomial.eval (fun k => coord k u) p * coord k u := by
      funext u; simp
    rw [this]; exact hp.mul (coord_temperate k)

def toEuclid (m n : ℕ) : (Fin m → Fin n → ℂ) ≃L[ℝ] PiLp 2 (fun _ : Fin m × Fin n => ℂ) :=
  LinearEquiv.toContinuousLinearEquiv
    (((LinearEquiv.curry ℝ ℂ (Fin m) (Fin n)).symm.trans
      (WithLp.linearEquiv 2 ℝ (Fin m × Fin n → ℂ)).symm).trans
      (LinearEquiv.smulOfNeZero ℝ _ (√2) (by positivity)))

theorem norm_toEuclid_sq (u : Fin m → Fin n → ℂ) :
    ‖toEuclid m n u‖ ^ 2 = 2 * ∑ a, ∑ i, ‖u a i‖ ^ 2 := by
  have h : toEuclid m n u = (√2 : ℝ) • (WithLp.toLp 2 (fun p : Fin m × Fin n => u p.1 p.2) :
      PiLp 2 (fun _ : Fin m × Fin n => ℂ)) := rfl
  rw [h, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, Real.sq_sqrt (by positivity),
    PiLp.norm_sq_eq_of_L2, Fintype.sum_prod_type]

theorem exists_gauss : ∃ g : SchwartzMap (Fin m → Fin n → ℂ) ℂ, ∀ u,
    g u = Complex.exp (-(2 * Real.pi * ∑ a, ∑ i, ‖u a i‖ ^ 2 : ℝ)) := by
  refine ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (toEuclid m n)
    (GroundTheory.Global.gaussianSchwartz (PiLp 2 (fun _ : Fin m × Fin n => ℂ))), fun u => ?_⟩
  rw [SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply,
    GroundTheory.Global.gaussianSchwartz_apply, norm_toEuclid_sq, Complex.ofReal_exp]
  congr 1
  push_cast
  ring


end GlobalTheory.CompanionTheory.PolyGaussSchwartz
