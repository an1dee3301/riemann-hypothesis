module

public import Development.Core20Slim.Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.SecondLogDerivativeUnique
public import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.AnalyticTransOfAdd
public import Formalism.LocalToGlobal.TorsionIntegrality.CMGoodModels.Statement
public import Development.Core20Slim.Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.HomotheticLatticeIntegralS2
public import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.NonsingularJetNorms.CmIntegralityOfTorsionPoints
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Int.Order
public import Init.Data.Nat.Basic
public import Init.Data.Nat.Div.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
public import Mathlib.Algebra.Order.Ring.Cast
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.Ring.Int
public import Mathlib.Algebra.Order.Ring.Unbundled.Basic
public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Group.Completion
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.Analysis.Normed.Module.Completion
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.Normed.Ring.Ultra
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Logic.Basic
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.Real.Star
public import Mathlib.Data.Int.Basic
public import Mathlib.Data.Int.Cast.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.Logic.Function.Defs
public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Lattice
public import Mathlib.Tactic.Linarith.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.UniformRing
public import Mathlib.Topology.Algebra.Valued.ValuationTopology
public import Mathlib.Topology.Algebra.Valued.ValuedField
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.MetricSpace.Ultra.Basic
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.Top

open Formalism.L2.Th1.CM (HasCMBy omegaK)
open Formalism.L2.Th1.E (IntCurve curveL)
open Formalism.L2.Th1.A (logSer expSer wpReg shortW)
open Formalism.L2.Th1.D (normInt)
open Formalism.G (unitBall)

namespace OrthogonalGaussModelNormLemmas

theorem norm_le_one_of_quad {K : Type} [NormedField K] [IsUltrametricDist K] {a b c : K} {t : ℤ}
    (hs : a + b = (t : K)) (hp : a * b = c) (hc : ‖c‖ ≤ 1) : ‖a‖ ≤ 1 := by
  by_contra h
  rw [not_le] at h
  have e : a ^ 2 = (t : K) * a - c := by
    rw [← hs, ← hp]
    ring
  have h1 : ‖a ^ 2‖ ≤ max ‖(t : K) * a‖ ‖c‖ := by
    rw [e, sub_eq_add_neg, ← norm_neg c]
    exact IsUltrametricDist.norm_add_le_max _ _
  have h2 : ‖(t : K) * a‖ ≤ ‖a‖ := by
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (IsUltrametricDist.norm_intCast_le_one K t)
  have h3 : ‖c‖ ≤ ‖a‖ := hc.trans h.le
  have h4 : ‖a‖ ^ 2 ≤ ‖a‖ := by
    rw [← norm_pow]
    exact h1.trans (max_le h2 h3)
  nlinarith

theorem norm_eq_one_of_quad {K : Type} [NormedField K] [IsUltrametricDist K] {a b c : K} {t : ℤ}
    (hs : a + b = (t : K)) (hp : a * b = c) (hc : ‖c‖ = 1) : ‖a‖ = 1 := by
  have ha := norm_le_one_of_quad hs hp hc.le
  have hb := norm_le_one_of_quad (a := b) (b := a) (by rw [add_comm]; exact hs)
    (by rw [mul_comm]; exact hp) hc.le
  have h : ‖a‖ * ‖b‖ = 1 := by rw [← norm_mul, hp, hc]
  refine le_antisymm ha ?_
  calc (1 : ℝ) = ‖a‖ * ‖b‖ := h.symm
    _ ≤ ‖a‖ * 1 := mul_le_mul_of_nonneg_left hb (norm_nonneg a)
    _ = ‖a‖ := mul_one _

theorem norm_int (p : ℕ) [Fact p.Prime] {z : ℤ} (h : ¬ (p : ℤ) ∣ z) : ‖(z : ℂ_[p])‖ = 1 := by
  have h1 : ¬ p ∣ z.natAbs := fun h2 => h (Int.natCast_dvd.2 h2)
  have h3 := Formalism.L2.Th1.E.ScaledModelNorms.norm_nat p h1
  rcases Int.natAbs_eq z with e | e
  · rw [e]
    simpa using h3
  · rw [e]
    simpa using h3

theorem norm_two (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) : ‖(2 : ℂ_[p])‖ = 1 := by
  have h : ¬ p ∣ 2 := fun h => hp ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).1 h)
  simpa using Formalism.L2.Th1.E.ScaledModelNorms.norm_nat p h

theorem prod_bar {dK : ℕ} (hmod : dK % 4 = 3) (m n : ℤ) :
    ((m : ℂ) + (n : ℂ) * omegaK dK) * ((m : ℂ) + (n : ℂ) * (1 - omegaK dK)) =
      ((normInt dK m n : ℤ) : ℂ) := by
  rw [Formalism.L2.Th1.D.CurveNormEndomorphisms.mul_bar]
  have := congrArg (fun x : ℝ => (x : ℂ)) (Formalism.L2.Th1.D.CurveNormEndomorphisms.normInt_cast hmod m n)
  push_cast at this
  rw [this]


variable {p : ℕ} [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p])





end OrthogonalGaussModelNormLemmas




end Formalism.L2.Th1.Top
