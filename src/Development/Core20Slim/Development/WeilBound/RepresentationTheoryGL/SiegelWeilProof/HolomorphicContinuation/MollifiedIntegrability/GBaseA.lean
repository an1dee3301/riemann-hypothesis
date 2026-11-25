module

public import Mathlib
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.RCLike.Lemmas
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.MeasurableSpace.Embedding
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
public import Mathlib.Order.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Inv
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

noncomputable section

open MeasureTheory Complex

namespace PositivityTheory.Rg.Sw.WR.G.GB

theorem gauss_one (w : ℂ) (hw : 0 < w.re) :
    ∫ z : ℂ, cexp (-(w * ((‖z‖ ^ 2 : ℝ) : ℂ))) = (Real.pi : ℂ) / w := by
  have h := Complex.volume_preserving_equiv_real_prod.symm
  rw [← h.integral_comp' (g := fun z : ℂ => cexp (-(w * ((‖z‖ ^ 2 : ℝ) : ℂ))))]
  have e : ∀ p : ℝ × ℝ, cexp (-(w * ((‖measurableEquivRealProd.symm p‖ ^ 2 : ℝ) : ℂ))) =
      cexp (-w * (p.1 : ℂ) ^ 2) * cexp (-w * (p.2 : ℂ) ^ 2) := by
    intro p
    rw [← Complex.exp_add]
    congr 1
    rw [measurableEquivRealProd_symm_apply, Complex.sq_norm, Complex.normSq_apply]
    push_cast
    ring
  simp_rw [e]
  rw [show (volume : Measure (ℝ × ℝ)) = (volume : Measure ℝ).prod volume from rfl,
    integral_prod_mul (fun x : ℝ => cexp (-w * (x : ℂ) ^ 2)) (fun x : ℝ => cexp (-w * (x : ℂ) ^ 2)),
    integral_gaussian_complex hw]
  have hne : (Real.pi : ℂ) / w ≠ 0 := by
    have : w ≠ 0 := by intro h0; rw [h0] at hw; simp at hw
    exact div_ne_zero (by exact_mod_cast Real.pi_ne_zero) this
  rw [← Complex.cpow_add _ _ hne]
  norm_num

theorem gauss_diag {n : ℕ} (d : Fin n → ℂ) (hd : ∀ k, 0 < (d k).re) :
    ∫ r : Fin n → ℂ, cexp (-∑ k, d k * ((‖r k‖ ^ 2 : ℝ) : ℂ)) = ∏ k, (Real.pi : ℂ) / d k := by
  have e : ∀ r : Fin n → ℂ, cexp (-∑ k, d k * ((‖r k‖ ^ 2 : ℝ) : ℂ)) =
      ∏ k, cexp (-(d k * ((‖r k‖ ^ 2 : ℝ) : ℂ))) := by
    intro r
    rw [← Complex.exp_sum, Finset.sum_neg_distrib]
  simp_rw [e]
  rw [integral_fintype_prod_volume_eq_prod (fun k (z : ℂ) => cexp (-(d k * ((‖z‖ ^ 2 : ℝ) : ℂ))))]
  exact Finset.prod_congr rfl fun k _ => gauss_one (d k) (hd k)

end PositivityTheory.Rg.Sw.WR.G.GB
