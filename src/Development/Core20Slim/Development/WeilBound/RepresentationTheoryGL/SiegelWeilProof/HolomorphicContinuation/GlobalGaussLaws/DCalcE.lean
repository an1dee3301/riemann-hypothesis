module

public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DCalcD
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DCalcA
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DCalcB
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.FourierZeroN
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.NullSec
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.NeZero
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.Group.Abs
public import Mathlib.Algebra.Order.Group.Defs
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Algebra.Order.Monoid.Unbundled.ExistsOfLE
public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.Algebra.Order.Ring.Basic
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Cast.Order.Basic
public import Mathlib.Data.Nat.Cast.Order.Ring
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Order.Lattice
public import Mathlib.Tactic.Linarith.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Positivity.Core
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.MvPolynomial
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.Algebra.Star
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology MvPolynomial

namespace PositivityTheory.Rg.Sw.Glob

namespace DCalcEH

open DCalcH DCalcBH DCalcDH

variable {m n : ℕ}

theorem crd_cont (X : Fin n → ℝ) (s : ℝ) : Continuous fun u : Fin m → Fin n → ℂ => crd (vS u X s) := by
  refine continuous_pi fun k => ?_
  unfold crd vS
  split_ifs <;> fun_prop

theorem fF_cont (c : ℝ) (X : Fin n → ℝ) (Q : PX m n) (s : ℝ) : Continuous fun u : Fin m → Fin n → ℂ => fF c X Q u s := by
  unfold fF fP
  refine continuous_const.mul (Continuous.mul ?_ ?_)
  · simp only [evX_eq]
    exact (MvPolynomial.continuous_eval Q).comp (crd_cont X s)
  · simp only [gs, vS]
    fun_prop

theorem norm_gs (c : ℝ) (v : Fin m → Fin n → ℂ) : ‖gs c v‖ = Real.exp (-(c * sqN v)) := by
  simp only [gs, sqN]
  rw [← Complex.ofReal_neg, Complex.norm_exp_ofReal]

theorem sq_vS_le (u : Fin m → Fin n → ℂ) (X : Fin n → ℝ) (s R : ℝ) (hs : |s| ≤ R) :
    Real.exp (-(2 * R * ∑ j, |X j|)) * sqN u ≤ sqN (vS u X s) ∧ sqN (vS u X s) ≤ Real.exp (2 * R * ∑ j, |X j|) * sqN u := by
  have hR : 0 ≤ R := (abs_nonneg s).trans hs
  have hX : ∀ j, |2 * s * X j| ≤ 2 * R * ∑ j, |X j| := by
    intro j
    have h1 : |X j| ≤ ∑ j, |X j| := Finset.single_le_sum (f := fun j => |X j|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j)
    rw [abs_mul, abs_mul, abs_two]
    have := mul_le_mul hs h1 (abs_nonneg _) hR
    nlinarith
  have hterm : ∀ a j, ‖vS u X s a j‖ ^ 2 = ‖u a j‖ ^ 2 * Real.exp (2 * s * X j) := by
    intro a j
    rw [norm_vS, ← Real.exp_nat_mul]; push_cast; ring_nf
  unfold sqN
  simp only [hterm]
  constructor
  · rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun a _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [mul_comm]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by positivity)
    linarith [neg_abs_le (2 * s * X j), hX j]
  · rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun a _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by positivity) |>.trans_eq (mul_comm _ _)
    linarith [le_abs_self (2 * s * X j), hX j]

theorem fF_bound (c : ℝ) (hc : 0 < c) (X : Fin n → ℝ) (Q : PX m n) (s : ℝ) :
    ∃ K a, 0 ≤ K ∧ 0 < a ∧ ∀ u, ∀ s' ∈ Set.Icc (s - 1) (s + 1), ‖fF c X Q u s'‖ ≤ K * Real.exp (-(a * sqN u)) := by
  set R := |s| + 1
  set M := ∑ j, |X j|
  set κ := Real.exp (-(2 * R * M))
  set κ' := Real.exp (2 * R * M)
  have hκ : 0 < κ := Real.exp_pos _
  have hκ' : 1 ≤ κ' := Real.one_le_exp (by positivity)
  obtain ⟨C, N, hC, hev⟩ := evX_growth Q
  obtain ⟨C2, hC2, hpe⟩ := poly_exp N (c * κ) (by positivity)
  refine ⟨Real.exp (R * m * M) * (C * (κ' ^ N * C2)), c * κ / 2, by positivity, by positivity, fun u s' hs' => ?_⟩
  have hs'R : |s'| ≤ R := by
    rw [abs_le]; constructor <;> linarith [hs'.1, hs'.2, neg_abs_le s, le_abs_self s]
  obtain ⟨hlo, hhi⟩ := sq_vS_le u X s' R hs'R
  have hS := sqN_nonneg u
  have h1 : ‖((Real.exp (s' * (m : ℝ) * ∑ j, X j) : ℝ) : ℂ)‖ ≤ Real.exp (R * m * M) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    refine Real.exp_le_exp.2 ?_
    have : |∑ j, X j| ≤ M := Finset.abs_sum_le_sum_abs _ _
    have h2 : s' * (m : ℝ) * ∑ j, X j ≤ |s'| * m * |∑ j, X j| := by
      calc s' * (m : ℝ) * ∑ j, X j ≤ |s' * (m : ℝ) * ∑ j, X j| := le_abs_self _
        _ = |s'| * m * |∑ j, X j| := by rw [abs_mul, abs_mul, Nat.abs_cast]
    have h3 : |s'| * m * |∑ j, X j| ≤ R * m * M :=
      mul_le_mul (mul_le_mul_of_nonneg_right hs'R (by positivity)) this (abs_nonneg _) (by positivity)
    linarith
  have h2 : ‖evX Q (vS u X s')‖ ≤ C * (κ' ^ N * (1 + sqN u) ^ N) := by
    refine (hev _).trans (mul_le_mul_of_nonneg_left ?_ hC)
    rw [← mul_pow]
    refine pow_le_pow_left₀ (by linarith [sqN_nonneg (vS u X s')]) ?_ N
    nlinarith
  have h3 : ‖gs c (vS u X s')‖ ≤ Real.exp (-(c * κ * sqN u)) := by
    rw [norm_gs]; refine Real.exp_le_exp.2 ?_
    have := mul_le_mul_of_nonneg_left hlo hc.le
    linarith
  unfold fF fP
  rw [norm_mul, norm_mul]
  calc ‖((Real.exp (s' * (m : ℝ) * ∑ j, X j) : ℝ) : ℂ)‖ * (‖evX Q (vS u X s')‖ * ‖gs c (vS u X s')‖)
      ≤ Real.exp (R * m * M) * (C * (κ' ^ N * (1 + sqN u) ^ N) * Real.exp (-(c * κ * sqN u))) :=
        mul_le_mul h1 (mul_le_mul h2 h3 (norm_nonneg _)
          (mul_nonneg hC (mul_nonneg (pow_nonneg (by linarith) _) (pow_nonneg (by linarith) _))))
          (by positivity) (by positivity)
    _ = Real.exp (R * m * M) * (C * (κ' ^ N * ((1 + sqN u) ^ N * Real.exp (-(c * κ * sqN u))))) := by ring
    _ ≤ Real.exp (R * m * M) * (C * (κ' ^ N * (C2 * Real.exp (-(c * κ / 2 * sqN u))))) := by
        have := hpe (sqN u) hS
        gcongr
    _ = Real.exp (R * m * M) * (C * (κ' ^ N * C2)) * Real.exp (-(c * κ / 2 * sqN u)) := by ring

end DCalcEH

end PositivityTheory.Rg.Sw.Glob
