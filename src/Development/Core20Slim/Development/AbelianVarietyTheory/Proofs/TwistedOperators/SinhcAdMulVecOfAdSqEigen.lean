module

public import Mathlib
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousExptPY
public import Batteries.Logic
public import Formalism.LocalRingCardinality.DataTheta
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.InfiniteSum
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Normed.MulAction
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Cast.Order.Basic
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Nat.Init
public import Mathlib.FieldTheory.Perfect
public import Mathlib.FieldTheory.Separable
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Tactic.FieldSimp.Lemmas
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.Group
public import Mathlib.Topology.Algebra.InfiniteSum.Module
public import Mathlib.Topology.Algebra.InfiniteSum.Ring
public import Mathlib.Topology.Algebra.InfiniteSum.SummationFilter
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.UniformSpace.Defs
public import Mathlib.Topology.UniformSpace.Real

@[expose] public section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU Matrix MeasureTheory

namespace GlobalTheory.PolarU


open scoped Matrix.Norms.Operator in
theorem summable_sinhc_series_mat {n : Type} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) :
    Summable fun k : ℕ => (((2 * k + 1).factorial : ℂ)⁻¹) • A ^ (2 * k) := by
  have h0 : Summable fun m : ℕ => ‖((m.factorial : ℂ)⁻¹) • A ^ m‖ :=
    NormedSpace.norm_expSeries_summable' A
  have h1 : Summable fun k : ℕ => ‖(((2 * k).factorial : ℂ)⁻¹) • A ^ (2 * k)‖ :=
    h0.comp_injective (i := fun k : ℕ => 2 * k) (fun a b h => by simpa using h)
  refine Summable.of_norm_bounded h1 fun k => ?_
  rw [norm_smul, norm_smul]
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  rw [norm_inv, norm_inv, Complex.norm_natCast, Complex.norm_natCast]
  refine inv_anti₀ (by exact_mod_cast Nat.factorial_pos _) ?_
  exact_mod_cast Nat.factorial_le (Nat.le_succ _)

theorem hasSum_shc_series (x : ℝ) :
    HasSum (fun k : ℕ => (((2 * k + 1).factorial : ℝ)⁻¹) * x ^ (2 * k)) (shc x) := by
  unfold shc
  split_ifs with hx
  · subst hx
    have := hasSum_single (f := fun k : ℕ => (((2 * k + 1).factorial : ℝ)⁻¹) * (0 : ℝ) ^ (2 * k)) 0
      (fun k hk => by simp [hk])
    simpa using this
  · have h := (Real.hasSum_sinh x).div_const x
    have e : (fun k : ℕ => (((2 * k + 1).factorial : ℝ)⁻¹) * x ^ (2 * k))
        = fun k : ℕ => x ^ (2 * k + 1) / ((2 * k + 1).factorial : ℝ) / x := by
      funext k
      rw [pow_succ]
      field_simp
    rw [e]
    exact h

theorem sinhcAd_mulVec_of_sq_eigen : ∀ (p q : ℕ) (Y : Mat p q) (v : Ix p q × Ix p q → ℂ) (x : ℝ),
    (adMat Y ^ 2) *ᵥ v = ((x : ℂ) ^ 2) • v → sinhcAd Y *ᵥ v = ((shc x : ℝ) : ℂ) • v := by
  intro p q Y v x h
  have hk : ∀ k : ℕ, (adMat Y ^ (2 * k)) *ᵥ v = ((x : ℂ) ^ (2 * k)) • v := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [mul_add, mul_one, pow_add, pow_add, ← Matrix.mulVec_mulVec, h, Matrix.mulVec_smul, ih,
        smul_smul, mul_comm]
  let L : Matrix (Ix p q × Ix p q) (Ix p q × Ix p q) ℂ →+ (Ix p q × Ix p q → ℂ) :=
    { toFun := fun M => M *ᵥ v
      map_zero' := Matrix.zero_mulVec v
      map_add' := fun M N => Matrix.add_mulVec M N v }
  have hL : Continuous L := continuous_id.matrix_mulVec continuous_const
  have h1 := (summable_sinhc_series_mat (adMat Y)).hasSum.map L hL
  have h2 : HasSum (fun k : ℕ => (((((2 * k + 1).factorial : ℝ)⁻¹) * x ^ (2 * k) : ℝ) : ℂ) • v)
      (((shc x : ℝ) : ℂ) • v) := (Complex.hasSum_ofReal.2 (hasSum_shc_series x)).smul_const v
  refine h1.unique ?_
  convert h2 using 1
  funext k
  show (_ • _) *ᵥ v = _
  rw [Matrix.smul_mulVec, hk, smul_smul]
  push_cast
  rfl

end GlobalTheory.PolarU
