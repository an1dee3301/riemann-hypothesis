module

public import Mathlib
public import Development.Core20Slim.Formalism.PeriodIntegrals.JetsPhW
public import Development.Core20Slim.Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.InverseOmegaHolds
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.Normed.Field.Instances
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Logic.Basic
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.RingTheory.PowerSeries.Derivative
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.UniformField
public import Mathlib.Topology.Algebra.UniformRing
public import Mathlib.Topology.Algebra.Valued.ValuationTopology
public import Mathlib.Topology.Algebra.Valued.ValuedField
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

open Classical

namespace PI.JetsPhW.Inv

variable {p : ℕ} [Fact p.Prime]

theorem dX_eq_derivative (f : PowerSeries ℂ_[p]) : dX f = PowerSeries.derivative f := by
  ext n
  rw [PowerSeries.coeff_derivative, dX, PowerSeries.coeff_mk, mul_comm]

theorem inverse_omega_holds : InvOmega := by
  simpa only [InvOmega, IsIntP, IsWq, dX, flog, omegaW,
    UpperTheory.Reformulated.B.Gwa1.InvOmega, UpperTheory.Reformulated.B.Gwa1.IsIntP,
    UpperTheory.Reformulated.B.Gwa1.IsWq, UpperTheory.Reformulated.B.Gwa1.dX,
    UpperTheory.Reformulated.B.Gwa1.flog, UpperTheory.Reformulated.B.Gwa1.omegaW] using
    _root_.UpperTheory.Reformulated.B.Gwa1.inverse_omega_holds

end PI.JetsPhW.Inv
