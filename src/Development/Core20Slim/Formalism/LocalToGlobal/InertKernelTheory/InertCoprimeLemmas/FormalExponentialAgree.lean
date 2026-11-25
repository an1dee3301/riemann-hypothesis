module

public import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
public import Formalism.LocalToGlobal.TorsionIntegrality.CMGoodModels.Statement
public import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.CyclicPowerClassOfExpEquiv
public import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.FlowTwoTorsionWp
public import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.TwoTorsionU
public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.ConstantCoeffSeriesAtVariable
public import Development.Core20Slim.Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PowerSeriesNormUnits.NormUnitsSubstitution
public import Development.Core20Slim.Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FormalGroupCommon.ExpLog
public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.OneAddMulDerivLogSubst
public import Formalism.GaussJetBounds.Statement
public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.CurveHyp
public import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.CompInv
public import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.StatementJ
public import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.WeierstrassSubstitution.CurveSer
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
public import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.IsLawOfLog
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
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange
public import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Instances
public import Mathlib.Analysis.Normed.Group.Completion
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Module.Completion
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Logic.Basic
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.MvPowerSeries.Inverse
public import Mathlib.RingTheory.MvPowerSeries.Substitution
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.RingTheory.PowerSeries.Derivative
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
public import Mathlib.RingTheory.PowerSeries.Substitution
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Tactic.LinearCombination.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.GroupCompletion
public import Mathlib.Topology.Algebra.IsUniformGroup.Defs
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.UniformField
public import Mathlib.Topology.Algebra.UniformRing
public import Mathlib.Topology.Algebra.Valued.ValuationTopology
public import Mathlib.Topology.Algebra.Valued.ValuedField
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

namespace Formalism.L2.KerInert.Dict

open Formalism.BasicNotions Formalism.MainNotions.GL3Theta Formalism.MainNotions.TaylorLogMetric NumberField


def LogAgree : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]), IsWq W wq →
    flog W wq = Formalism.L2.Th1.A.logSer W

def ExAgree : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (g : G1 p), g.Ok → g.ex = Formalism.L2.Th1.A.expSer g.W

def AddAgree : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (g : G1 p), g.Ok → ∀ (σ : Type) (a b : MvPowerSeries σ ℂ_[p]),
    MvPowerSeries.constantCoeff a = 0 → MvPowerSeries.constantCoeff b = 0 →
    g.add a b = MvPowerSeries.subst ![a, b] (Formalism.L2.Th1.A.fgl g.W)



open PowerSeries

section
variable {p : ℕ} [Fact p.Prime]



theorem dX_eq (f : PowerSeries ℂ_[p]) : dX f = PowerSeries.derivative f := by
  ext n
  simp [dX, PowerSeries.coeff_derivative, mul_comm]

theorem isWq_C {W : WeierstrassCurve ℂ_[p]} {wq : PowerSeries ℂ_[p]} (h : IsWq W wq) :
    wq = 1 + C W.a₁ * X * wq + C W.a₂ * X ^ 2 * wq + C W.a₃ * X ^ 3 * wq ^ 2 +
      C W.a₄ * X ^ 4 * wq ^ 2 + C W.a₆ * X ^ 6 * wq ^ 3 := by
  exact h

theorem wSer_of_isWq {W : WeierstrassCurve ℂ_[p]} {wq : PowerSeries ℂ_[p]} (h : IsWq W wq) :
    Formalism.L2.Th1.A.wSer W = X ^ 3 * wq := by
  symm
  apply Formalism.L2.Th1.A.CurveSer.wSer_unique
  refine ⟨by simp, ?_⟩
  linear_combination (X ^ 3 : PowerSeries ℂ_[p]) * isWq_C h

theorem cc_wq {W : WeierstrassCurve ℂ_[p]} {wq : PowerSeries ℂ_[p]} (h : IsWq W wq) :
    constantCoeff wq = 1 := by
  have h1 := congrArg constantCoeff (isWq_C h)
  simpa using h1

theorem omegaW_eq {W : WeierstrassCurve ℂ_[p]} {wq : PowerSeries ℂ_[p]} (h : IsWq W wq) :
    omegaW W wq = Formalism.L2.Th1.A.om W := by
  have hw := wSer_of_isWq h
  have hE := (Formalism.L2.Th1.A.CurveSer.wSer_fixed W).2
  have hd := Formalism.L2.Th1.A.CurveSer.deriv_wSer_mul_fw W
  have hfo := Formalism.L2.Th1.A.CurveSer.fw_mul_om W
  have key : Formalism.L2.Th1.A.fw W * (-(2 : PowerSeries ℂ_[p]) * wq - X * dX wq) =
      wq * (C W.a₁ * X + C W.a₃ * X ^ 3 * wq - 2) := by
    apply mul_left_cancel₀ (pow_ne_zero 3 (X_ne_zero (R := ℂ_[p])))
    have hder : PowerSeries.derivative (X ^ 3 * wq) =
        3 * X ^ 2 * wq + X ^ 3 * PowerSeries.derivative wq := by
      rw [Derivation.leibniz, Derivation.leibniz_pow, derivative_X]
      simp only [smul_eq_mul, nsmul_eq_mul]
      push_cast
      ring
    simp only [Formalism.L2.Th1.A.fw, Formalism.L2.Th1.A.fu] at hd ⊢
    rw [hw] at hd hE ⊢
    rw [hder] at hd
    rw [dX_eq]
    linear_combination (-X : PowerSeries ℂ_[p]) * hd + 3 * hE
  have hD : constantCoeff (wq * (C W.a₁ * X + C W.a₃ * X ^ 3 * wq - 2)) ≠ 0 := by
    have h2 : constantCoeff (2 : PowerSeries ℂ_[p]) = 2 := map_ofNat _ 2
    simp [cc_wq h, h2]
  have e1 : (-(2 : PowerSeries ℂ_[p]) * wq - X * dX wq) =
      Formalism.L2.Th1.A.om W * (wq * (C W.a₁ * X + C W.a₃ * X ^ 3 * wq - 2)) := by
    rw [← key, ← mul_assoc, mul_comm (Formalism.L2.Th1.A.om W), hfo, one_mul]
  unfold omegaW
  simp only [PowerSeries.algebraMap_eq]
  rw [e1, mul_assoc, PowerSeries.mul_inv_cancel _ hD, mul_one]

theorem formal_logarithm_agree : LogAgree := by
  intro p _ W wq h
  unfold flog Formalism.L2.Th1.A.logSer Formalism.L2.Th1.A.integ
  rw [omegaW_eq h]

theorem formal_exponential_agree : ExAgree := by
  intro p _ g hOk
  have hl : flog g.W g.wq = Formalism.L2.Th1.A.logSer g.W := formal_logarithm_agree p g.W g.wq hOk.2.1
  obtain ⟨h0, h1, -, -⟩ := Formalism.L2.Th1.A.logSpec ℂ_[p] g.W
  have hu : IsUnit (coeff 1 (Formalism.L2.Th1.A.logSer g.W)) := by rw [h1]; exact isUnit_one
  have hs := Formalism.L2.Th1.A.compInvSpec ℂ_[p] _ h0 hu
  unfold Formalism.L2.Th1.A.expSer
  apply hs.2.2.2.2.1 g.ex hOk.2.2.1
  rw [← hl]
  exact hOk.2.2.2

theorem intModel_of_ok {g : G1 p} (hOk : g.Ok) : Formalism.L2.Th1.A.IntModel g.W := by
  obtain ⟨⟨h1, h2, h3, h4, h6, -⟩, -⟩ := hOk
  exact ⟨h1, h2, h3, h4, h6⟩

theorem formal_addition_agree : AddAgree := by
  intro p _ g hOk σ a b ha hb
  have hl : flog g.W g.wq = Formalism.L2.Th1.A.logSer g.W := formal_logarithm_agree p g.W g.wq hOk.2.1
  have he : g.ex = Formalism.L2.Th1.A.expSer g.W := formal_exponential_agree p g hOk
  have hL := (Formalism.L2.Th1.A.bridgeLaw ℂ_[p] g.W (intModel_of_ok hOk)).1
  have hF : MvPowerSeries.constantCoeff (Formalism.L2.Th1.A.fgl g.W) = 0 := hL.1
  have hc := Formalism.L2.Th1.B.law_constantCoeff_subst2 (Formalism.L2.Th1.A.fgl g.W) hF a b ha hb
  have hsum := Formalism.L2.Th1.B.law_subst hL a b ha hb
  obtain ⟨hl0, -, -, -⟩ := Formalism.L2.Th1.A.logSpec ℂ_[p] g.W
  obtain ⟨-, -, -, hEL, -⟩ := Formalism.L2.Th1.A.expSpec ℂ_[p] g.W
  show PowerSeries.subst (PowerSeries.subst a (flog g.W g.wq) + PowerSeries.subst b (flog g.W g.wq)) g.ex = _
  rw [hl, he, ← hsum, ← PowerSeries.subst_comp_subst_apply (HasSubst.of_constantCoeff_zero' hl0)
    (HasSubst.of_constantCoeff_zero hc), hEL, PowerSeries.subst_X (HasSubst.of_constantCoeff_zero hc)]



end

end Formalism.L2.KerInert.Dict
