module

public import Development.Core20Slim.Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdditiveIntegralGroups.CoeffPowMemS
public import Development.Core20Slim.Formalism.PeriodIntegrals.AddIntG
public import Development.Core20Slim.Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdditiveIntegralGroups.GuLine
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
public import Mathlib.Analysis.Normed.Field.Instances
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Logic.Basic
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.MvPowerSeries.Inverse
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.RingTheory.PowerSeries.Derivative
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.Tactic.LinearCombination.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.GroupCompletion
public import Mathlib.Topology.Algebra.UniformField
public import Mathlib.Topology.Algebra.UniformRing
public import Mathlib.Topology.Algebra.Valued.ValuationTopology
public import Mathlib.Topology.Algebra.Valued.ValuedField
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

open Classical

namespace PI.AddIntG.Wk

variable {p : ℕ} [Fact p.Prime]

theorem dX_eq_derivative (f : PowerSeries ℂ_[p]) : dX f = PowerSeries.derivative (R := ℂ_[p]) f := by
  ext n
  simp only [dX, PowerSeries.coeff_mk, PowerSeries.coeff_derivative]
  ring

theorem omega_mul_Gv {W : WeierstrassCurve ℂ_[p]} {wq : PowerSeries ℂ_[p]} (h : IsWq W wq) :
    omegaW W wq * Gv W (PowerSeries.X : PowerSeries ℂ_[p]) (wser wq) = -1 := by
  have hw1 := wq_const h
  have hder := dX_eq_derivative wq
  have h' : wq = 1 + algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₁ * (PowerSeries.X : PowerSeries ℂ_[p]) * wq + algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₂ * (PowerSeries.X : PowerSeries ℂ_[p]) ^ 2 * wq +
      algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₃ * (PowerSeries.X : PowerSeries ℂ_[p]) ^ 3 * wq ^ 2 + algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₄ * (PowerSeries.X : PowerSeries ℂ_[p]) ^ 4 * wq ^ 2 +
      algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₆ * (PowerSeries.X : PowerSeries ℂ_[p]) ^ 6 * wq ^ 3 := h
  have hD := congrArg (PowerSeries.derivative (R := ℂ_[p])) h'
  simp only [map_add (f := _), Derivation.leibniz, Derivation.leibniz_pow, Derivation.map_algebraMap,
    PowerSeries.derivative_X, Derivation.map_one_eq_zero, smul_eq_mul, nsmul_eq_mul] at hD
  have hQ : PowerSeries.constantCoeff
      (wq * (algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₁ * (PowerSeries.X : PowerSeries ℂ_[p]) + algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₃ * (PowerSeries.X : PowerSeries ℂ_[p]) ^ 3 * wq - 2)) ≠ 0 := by
    have h2 : PowerSeries.constantCoeff (2 : PowerSeries ℂ_[p]) = 2 := by
      rw [show (2 : PowerSeries ℂ_[p]) = 1 + 1 by norm_num, map_add (f := _), map_one]
      norm_num
    simp [hw1, h2]
  have key : (-(2 : PowerSeries ℂ_[p]) * wq - (PowerSeries.X : PowerSeries ℂ_[p]) * PowerSeries.derivative (R := ℂ_[p]) wq) *
      (algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₁ * (PowerSeries.X : PowerSeries ℂ_[p]) + algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₂ * (PowerSeries.X : PowerSeries ℂ_[p]) ^ 2 + 2 * algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₃ * ((PowerSeries.X : PowerSeries ℂ_[p]) ^ 3 * wq) +
        2 * algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₄ * (PowerSeries.X : PowerSeries ℂ_[p]) * ((PowerSeries.X : PowerSeries ℂ_[p]) ^ 3 * wq) + 3 * algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₆ * ((PowerSeries.X : PowerSeries ℂ_[p]) ^ 3 * wq) ^ 2 - 1) =
      -(wq * (algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₁ * (PowerSeries.X : PowerSeries ℂ_[p]) + algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₃ * (PowerSeries.X : PowerSeries ℂ_[p]) ^ 3 * wq - 2)) := by
    linear_combination (PowerSeries.X : PowerSeries ℂ_[p]) * hD
  calc omegaW W wq * Gv W (PowerSeries.X : PowerSeries ℂ_[p]) (wser wq)
      = ((-(2 : PowerSeries ℂ_[p]) * wq - (PowerSeries.X : PowerSeries ℂ_[p]) * PowerSeries.derivative (R := ℂ_[p]) wq) *
        (algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₁ * (PowerSeries.X : PowerSeries ℂ_[p]) + algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₂ * (PowerSeries.X : PowerSeries ℂ_[p]) ^ 2 + 2 * algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₃ * ((PowerSeries.X : PowerSeries ℂ_[p]) ^ 3 * wq) +
          2 * algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₄ * (PowerSeries.X : PowerSeries ℂ_[p]) * ((PowerSeries.X : PowerSeries ℂ_[p]) ^ 3 * wq) + 3 * algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₆ * ((PowerSeries.X : PowerSeries ℂ_[p]) ^ 3 * wq) ^ 2 - 1)) *
        (wq * (algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₁ * (PowerSeries.X : PowerSeries ℂ_[p]) + algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₃ * (PowerSeries.X : PowerSeries ℂ_[p]) ^ 3 * wq - 2))⁻¹ := by
        simp only [omegaW, Gv, wser, hder]
        ring
    _ = -1 := by
        rw [key, neg_mul, PowerSeries.mul_inv_cancel _ hQ]

end PI.AddIntG.Wk
