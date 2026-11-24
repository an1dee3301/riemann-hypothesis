module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsCompactDualHaar
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NonemptyCompactDualHaar
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousMatExp
public import ReciprocityTheory.GeometryOfNumbers.PluriharmonicAnalysis.LogDetSt
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Commute.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Linear
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Shift
public import Mathlib.Analysis.Calculus.FDeriv.Linear
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.FieldTheory.Perfect
public import Mathlib.FieldTheory.Separable
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Order.Filter.Basic
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.Algebra
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs
public import Mathlib.Topology.UniformSpace.Real

@[expose] public section

noncomputable section

namespace GlobalTheory.SUVol

open MeasureTheory Filter Topology Matrix Metric Set
open scoped ENNReal NNReal


section OneMatrix

variable {r : ℕ}

theorem det_exp (X : Matrix (Fin r) (Fin r) ℂ) : (NormedSpace.exp X).det = Complex.exp X.trace := by
  have hder : HasDerivAt (fun t : ℝ => (NormedSpace.exp (t • X)).det) X.trace 0 := by
    have h1 : ∀ a b, HasDerivAt (fun t : ℝ => NormedSpace.exp (t • X) a b) (X a b) 0 := by
      intro a b
      open scoped Matrix.Norms.Operator in
      have h2 := ((Matrix.entryLinearMap ℝ ℂ a b).toContinuousLinearMap.hasFDerivAt).comp_hasDerivAt 0
        (hasDerivAt_exp_smul_const (𝕂 := ℝ) X 0)
      rw [zero_smul, NormedSpace.exp_zero, one_mul] at h2
      exact h2
    have h3 := ReciprocityTheory.GeometryOfNumbersTheory.hasDerivAt_det (fun t : ℝ => NormedSpace.exp (t • X)) X 0 h1
    simpa only [zero_smul, NormedSpace.exp_zero, Matrix.adjugate_one, Matrix.one_mul] using h3
  have hadd : ∀ s t : ℝ,
      NormedSpace.exp ((s + t) • X) = NormedSpace.exp (s • X) * NormedSpace.exp (t • X) := by
    intro s t
    rw [add_smul]
    exact Matrix.exp_add_of_commute _ _ (((Commute.refl X).smul_left s).smul_right t)
  set f : ℝ → ℂ := fun t => (NormedSpace.exp (t • X)).det with hf
  have hd : ∀ t, HasDerivAt f (f t * X.trace) t := by
    intro t
    have h0 : HasDerivAt f X.trace (t - t) := by
      rw [sub_self]; exact hder
    have h1 := (h0.comp_sub_const t t).const_mul (f t)
    refine h1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
    simp only [hf]
    rw [← Matrix.det_mul, ← hadd, add_sub_cancel]
  have hg : ∀ t : ℝ, HasDerivAt (fun s : ℝ => f s * Complex.exp (-(s * X.trace))) 0 t := by
    intro t
    have h1 : HasDerivAt (fun s : ℝ => -((s : ℂ) * X.trace)) (-X.trace) t := by
      simpa using ((Complex.ofRealCLM.hasDerivAt (x := t)).mul_const X.trace).fun_neg
    exact ((hd t).fun_mul h1.cexp).congr_deriv (by ring)
  have h2 := is_const_of_deriv_eq_zero (fun t => (hg t).differentiableAt) (fun t => (hg t).deriv) 1 0
  simp only [hf, one_smul, zero_smul, NormedSpace.exp_zero, Matrix.det_one, Complex.ofReal_one, one_mul,
    Complex.ofReal_zero, zero_mul, neg_zero, Complex.exp_zero, Complex.exp_neg] at h2
  exact (mul_inv_eq_one₀ (Complex.exp_ne_zero _)).1 h2





variable {H : Matrix (Fin r) (Fin r) ℂ}





end OneMatrix

variable {ι : Type} {r : ℕ} {H : ι → Matrix (Fin r) (Fin r) ℂ}


end GlobalTheory.SUVol
