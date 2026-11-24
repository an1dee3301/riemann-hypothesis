module

public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GaussianPlaneIntegrals.AssemblyAlt
public import Development.Core20Slim.Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SchwartzBilinear.OneAddPowMulExpLe
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.NeZero
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.Group.Defs
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Algebra.Order.Monoid.Unbundled.ExistsOfLE
public import Mathlib.Algebra.Order.Ring.Basic
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.Ring.Unbundled.Basic
public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Countable.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.Real.Star
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
public import Mathlib.MeasureTheory.Group.Arithmetic
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.OuterMeasure.AE
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Filter.Basic
public import Mathlib.Order.Lattice
public import Mathlib.Tactic.Linarith.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Positivity.Core
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Compactness.LocallyCompact
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.EMetricSpace.Defs
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Metrizable.Uniformity
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

open MeasureTheory MvPolynomial Filter Topology

namespace PositivityTheory.Rg.Sw.FFTSteps.SecondLineEstimates

variable {m n : ℕ}

instance instHaarMat : (volume : Measure (Fin m → Fin n → ℂ)).IsAddHaarMeasure :=
  MeasureTheory.Measure.pi.isAddHaarMeasure _

def sq (x : Fin m → Fin n → ℂ) : ℝ := ∑ a, ∑ i, ‖x a i‖ ^ 2

lemma sq_nonneg' (x : Fin m → Fin n → ℂ) : 0 ≤ sq x := by
  unfold sq; positivity

lemma continuous_sq : Continuous (sq : (Fin m → Fin n → ℂ) → ℝ) := by
  unfold sq
  exact continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun i _ =>
    ((continuous_apply i).comp (continuous_apply a)).norm.pow 2

lemma col_sq_le (x : Fin m → Fin n → ℂ) (i : Fin n) : ∑ a, ‖x a i‖ ^ 2 ≤ sq x := by
  unfold sq
  exact Finset.sum_le_sum fun a _ =>
    Finset.single_le_sum (f := fun j => ‖x a j‖ ^ 2) (fun j _ => by positivity) (Finset.mem_univ i)

lemma coord_sq_le (x : Fin m → Fin n → ℂ) (a : Fin m) (i : Fin n) : ‖x a i‖ ^ 2 ≤ sq x :=
  (Finset.single_le_sum (f := fun b => ‖x b i‖ ^ 2) (fun b _ => by positivity) (Finset.mem_univ a)).trans
    (col_sq_le x i)

lemma coord_le (x : Fin m → Fin n → ℂ) (a : Fin m) (i : Fin n) : ‖x a i‖ ≤ 1 + sq x := by
  have h := coord_sq_le x a i
  nlinarith [sq_nonneg (‖x a i‖ - 1), norm_nonneg (x a i)]

lemma norm_sq_le (x : Fin m → Fin n → ℂ) : ‖x‖ ^ 2 ≤ sq x := by
  have h : ‖x‖ ≤ Real.sqrt (sq x) := by
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun a =>
      (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun i => ?_
    have := Real.abs_le_sqrt (coord_sq_le x a i)
    rwa [abs_of_nonneg (norm_nonneg _)] at this
  calc ‖x‖ ^ 2 ≤ (Real.sqrt (sq x)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
    _ = sq x := Real.sq_sqrt (sq_nonneg' x)

lemma pow_mul_exp_le (K : ℕ) {β : ℝ} (hβ : 0 < β) :
    ∃ M : ℝ, ∀ s : ℝ, 0 ≤ s → (1 + s) ^ K * Real.exp (-β * s) ≤ M :=
  _root_.UpperTheory.Reformulated.B.P6.r22b.PositivityTheory.Rg.Sw.FFTSteps.SecondLineEstimates.pow_mul_exp_le K hβ

lemma integrable_poly_gauss (N : ℕ) {β : ℝ} (hβ : 0 < β) :
    Integrable (fun x : Fin m → Fin n → ℂ => (1 + sq x) ^ N * Real.exp (-β * sq x)) := by
  set L : ℕ := Module.finrank ℝ (Fin m → Fin n → ℂ) + 1 with hL
  obtain ⟨M, hM⟩ := pow_mul_exp_le (N + L) hβ
  have hint : Integrable (fun x : Fin m → Fin n → ℂ => (1 + ‖x‖) ^ (-((2 * L : ℕ) : ℝ))) :=
    integrable_one_add_norm (by rw [hL]; push_cast; linarith)
  refine (hint.const_mul (2 ^ L * M)).mono' ?_ ?_
  · exact (((continuous_const.add continuous_sq).pow N).mul
      (Real.continuous_exp.comp (continuous_const.mul continuous_sq))).aestronglyMeasurable
  · refine Eventually.of_forall fun x => ?_
    have hs := sq_nonneg' x
    have hb : 0 < (1 + ‖x‖) ^ (2 * L) := by positivity
    rw [Real.norm_of_nonneg (by positivity), Real.rpow_neg (by positivity), Real.rpow_natCast]
    have hx2 : (1 + ‖x‖) ^ 2 ≤ 2 * (1 + sq x) := by
      nlinarith [norm_sq_le x, sq_nonneg (‖x‖ - 1)]
    have hxL : (1 + ‖x‖) ^ (2 * L) ≤ 2 ^ L * (1 + sq x) ^ L := by
      calc (1 + ‖x‖) ^ (2 * L) = ((1 + ‖x‖) ^ 2) ^ L := by rw [pow_mul]
        _ ≤ (2 * (1 + sq x)) ^ L := pow_le_pow_left₀ (by positivity) hx2 L
        _ = 2 ^ L * (1 + sq x) ^ L := mul_pow _ _ _
    have key : (1 + sq x) ^ N * Real.exp (-β * sq x) * (1 + ‖x‖) ^ (2 * L) ≤ 2 ^ L * M := by
      calc (1 + sq x) ^ N * Real.exp (-β * sq x) * (1 + ‖x‖) ^ (2 * L)
          ≤ (1 + sq x) ^ N * Real.exp (-β * sq x) * (2 ^ L * (1 + sq x) ^ L) :=
            mul_le_mul_of_nonneg_left hxL (by positivity)
        _ = 2 ^ L * ((1 + sq x) ^ (N + L) * Real.exp (-β * sq x)) := by ring
        _ ≤ 2 ^ L * M := mul_le_mul_of_nonneg_left (hM _ hs) (by positivity)
    rw [le_mul_inv_iff₀ hb]
    exact key

end PositivityTheory.Rg.Sw.FFTSteps.SecondLineEstimates
