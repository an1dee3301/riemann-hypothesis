module

public import Mathlib
public import ReciprocityTheory.GeometryOfNumbers.PluriharmonicAnalysis.LogDetSt
public import Init.ByCases
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Notation.Pi.Basic
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.FDeriv.Congr
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.RowCol
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Order.Filter.Basic
public import Mathlib.Order.Filter.Defs
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.GDelta.MetrizableSpace
public import Mathlib.Topology.MetricSpace.Algebra
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Metrizable.Uniformity
public import Mathlib.Topology.Separation.Basic
public import Mathlib.Topology.Separation.GDelta
public import Mathlib.Topology.Separation.Regular
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open Matrix

namespace GlobalTheory.Mem.InvDer

theorem hasDerivAt_inv_det_and_inv (n : ℕ) (M : ℝ → Matrix (Fin n) (Fin n) ℂ)
    (M' : Matrix (Fin n) (Fin n) ℂ) (h0 : M 0 = 1)
    (hM : ∀ i j, HasDerivAt (fun t => M t i j) (M' i j) 0) :
    HasDerivAt (fun t => ((M t).det)⁻¹) (-M'.trace) 0 ∧
      ∀ i j, HasDerivAt (fun t => (M t)⁻¹ i j) (-M' i j) 0 := by
  have hd := ReciprocityTheory.GeometryOfNumbersTheory.hasDerivAt_det M M' 0 hM
  rw [h0, adjugate_one, Matrix.one_mul] at hd
  have hdet0 : (M 0).det = 1 := by rw [h0, det_one]
  have hne : (M 0).det ≠ 0 := by rw [hdet0]; exact one_ne_zero
  have hinv : HasDerivAt (fun t => ((M t).det)⁻¹) (-M'.trace) 0 := by
    have h1 : HasDerivAt (fun z : ℂ => z⁻¹) (-((M 0).det ^ 2)⁻¹) (M 0).det := hasDerivAt_inv hne
    have h2 := h1.comp_of_eq (0 : ℝ) hd rfl
    refine HasDerivAt.congr_deriv h2 ?_
    rw [hdet0]; simp
  refine ⟨hinv, ?_⟩
  have hdiff : ∀ i j, DifferentiableAt ℝ (fun t => (M t)⁻¹ i j) 0 := by
    intro i j
    have hadj : DifferentiableAt ℝ (fun t => (M t).adjugate i j) 0 := by
      have := ReciprocityTheory.GeometryOfNumbersTheory.hasDerivAt_det (fun t => (M t).updateRow j (Pi.single i 1))
        (M'.updateRow j 0) 0 (by
          intro a b
          by_cases h : a = j
          · simp only [updateRow_apply, h, if_true]
            exact hasDerivAt_const _ _
          · simp only [updateRow_apply, h, if_false]
            exact hM a b)
      simpa only [adjugate_apply] using this.differentiableAt
    have := hinv.differentiableAt.mul hadj
    refine this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
    simp [Matrix.inv_def, Ring.inverse_eq_inv']
  intro i j
  have hev : ∀ᶠ t in nhds (0 : ℝ), (M t).det ≠ 0 := hd.continuousAt.eventually_ne hne
  have hprod : HasDerivAt (fun t => ∑ k, (M t)⁻¹ i k * M t k j)
      (∑ k, (deriv (fun t => (M t)⁻¹ i k) 0 * M 0 k j + (M 0)⁻¹ i k * M' k j)) 0 :=
    HasDerivAt.fun_sum fun k _ => ((hdiff i k).hasDerivAt.fun_mul (hM k j))
  have hconst : HasDerivAt (fun t => ∑ k, (M t)⁻¹ i k * M t k j) 0 0 := by
    refine (hasDerivAt_const (0 : ℝ) ((1 : Matrix (Fin n) (Fin n) ℂ) i j)).congr_of_eventuallyEq ?_
    filter_upwards [hev] with t ht
    rw [← Matrix.mul_apply, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr ht)]
  have huniq := hprod.unique hconst
  rw [h0, inv_one, Finset.sum_add_distrib] at huniq
  simp [Matrix.one_apply] at huniq
  have hfin : deriv (fun t => (M t)⁻¹ i j) 0 = -M' i j := eq_neg_of_add_eq_zero_left huniq
  rw [← hfin]
  exact (hdiff i j).hasDerivAt

end GlobalTheory.Mem.InvDer
