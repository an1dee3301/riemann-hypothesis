module

public import Development.Core20Slim.Formalism.PeriodIntegrals.UnitaryGroupMassFormula.JetIntegrality.TwoUnit
public import Development.Core20Slim.Formalism.PeriodIntegrals.UnitaryGroupMassFormula.JetIntegrality.ExpLog
public import Development.Core20Slim.Formalism.PeriodIntegrals.UnitaryGroupMassFormula.JetIntegrality.CoeffPowEqZeroOfDegreeLt
public import Development.Core20Slim.Formalism.PeriodIntegrals.JetsPhW
public import Init.Classical
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Order.ZeroLEOne
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Instances
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Group.Completion
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Module.Completion
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Logic.Basic
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Finsupp.Single
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.Logic.Function.Iterate
public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.MvPowerSeries.Derivative
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.RingTheory.PowerSeries.Derivative
public import Mathlib.RingTheory.PowerSeries.Substitution
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

namespace PI.JetsPhW.W

open PI.JetsPhW

theorem pderiv_subst_self : PdSelf := fun _ _ _ i g => Ch.pderiv_subst_X_self i g

theorem pderiv_subst_ne : PdNe := fun _ _ _ _ _ g h => Ch.pderiv_subst_X_ne h g

theorem derivative_chain_rule : DChain := by
  intro p _ σ i l v g s c hv hs hpd
  unfold Dv
  rw [Ch.pderiv_subst i hs, hpd]
  linear_combination (MvPowerSeries.C c * PowerSeries.subst s (dX g)) * Ch.subst_v_mul hv i

theorem derivative_self : DSelf := by
  intro p _ σ i v g
  unfold Dv
  rw [Ch.pderiv_subst_X_self, ← PowerSeries.subst_mul
    (PowerSeries.HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X i)) v (dX g)]

theorem evaluation_at_zero : Ev0 := by
  intro p _ σ s g hs
  have hsub : PowerSeries.HasSubst s := PowerSeries.HasSubst.of_constantCoeff_zero hs
  have h2 : MvPowerSeries.constantCoeff
      (PowerSeries.subst s (g - PowerSeries.C (PowerSeries.constantCoeff g))) = 0 :=
    PowerSeries.constantCoeff_subst_eq_zero hs _ (by simp)
  have h4 : PowerSeries.subst s g = PowerSeries.subst s (g - PowerSeries.C (PowerSeries.constantCoeff g)) +
      MvPowerSeries.C (PowerSeries.constantCoeff g) := by
    rw [← PowerSeries.subst_C (a := s) (PowerSeries.constantCoeff g), ← PowerSeries.subst_add hsub,
      sub_add_cancel]
  rw [h4, map_add (f := _), h2, zero_add, MvPowerSeries.constantCoeff_C]

theorem jet_derivative_integrality : JetD := by
  intro p _ ex ph n
  have h : (dX (A := ℂ_[p])) = ⇑(PowerSeries.derivative (R := ℂ_[p])) := funext Ch.dX_eq
  rw [h, PowerSeries.constantCoeff_iterate_derivative]
  rfl

theorem intMv_subst_X {p : ℕ} [Fact p.Prime] {σ : Type*} {v : PowerSeries ℂ_[p]} (hv : IntP v) (i : σ) :
    IntegralMv (PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries σ ℂ_[p]) v) := by
  classical
  intro e
  rw [PowerSeries.coeff_subst_single]
  split_ifs
  · exact hv _
  · show ‖(0 : ℂ_[p])‖ ≤ 1
    simp

theorem derivative_integral : Dint := fun _ _ _ i _ _ hv hf => intMv_mul (intMv_subst_X hv i) (intMv_pderiv i hf)

theorem log_derivative_integral_jet_integrality : LogDer := fun _ _ _ i _ _ hv hf hE => L0 i hf hE (intMv_subst_X hv i)

end PI.JetsPhW.W
