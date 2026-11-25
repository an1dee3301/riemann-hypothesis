module

public import Development.Core20Slim.Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.CurveEndoAll
public import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.PhNormFromDatum
public import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.BinomialSeriesCoefficients.ConstantCoeffVecConsPairEqZero
public import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.BinomialSeriesCoefficients.Points
public import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.FlowTwoTorsionWp
public import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.FglInvariant
public import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.CubeThreeR
public import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.TwoTorsionU
public import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.ChordEquation
public import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.FirstLevelFromUniversal
public import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.HasSecondLogDeriv
public import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.CompInv
public import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.StatementG
public import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.StatementI
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Fin.Basic
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Units
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Formula
public import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.RingTheory.PowerSeries.Derivative
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.RingTheory.PowerSeries.Substitution
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.C

open Formalism.L2.Th1.A (logSer expSer wpReg xS xPlus)

namespace WeierstrassCurveSeries

variable {K : Type} [Field K] [CharZero K]

theorem logPair (W : WeierstrassCurve K) : IsLogPair (logSer W) (expSer W) := by
  obtain ⟨h0, h1, -, -⟩ := Formalism.L2.Th1.A.logSpec.{0} K W
  obtain ⟨e0, -, e2, e3, -⟩ := Formalism.L2.Th1.A.expSpec.{0} K W
  exact ⟨h0, h1, e0, e3, e2⟩

theorem xIsWp (W : WeierstrassCurve K) : XIsWp (wpReg W) (logSer W) (xS W) (W.b₂ / 12) := by
  have h := Formalism.L2.Th1.A.wpInU.{0} K W
  have hl : PowerSeries.HasSubst (logSer W) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' (logPair W).1
  unfold XIsWp wpShift
  rw [map_zero, sub_zero, PowerSeries.subst_add hl, PowerSeries.subst_mul hl,
    PowerSeries.subst_pow hl, PowerSeries.subst_X hl, ← PowerSeries.coe_substAlgHom hl, map_one,
    PowerSeries.coe_substAlgHom hl, h]
  ring

theorem subst_wTr (W : WeierstrassCurve K) (xP yP : K) :
    PowerSeries.subst (logSer W) (wTr W xP yP) = xPlus W xP yP + PowerSeries.C (W.b₂ / 12) := by
  have h := logPair W
  have hl : PowerSeries.HasSubst (logSer W) := PowerSeries.HasSubst.of_constantCoeff_zero' h.1
  unfold wTr
  rw [PowerSeries.subst_add hl, Pts.subst_subst h.2.2.1 h.1, h.2.2.2.1, PowerSeries.X_subst,
    PowerSeries.subst_C]
  rfl

end WeierstrassCurveSeries

open WeierstrassCurveSeries

theorem curve_formal_frame : CurveFrame := by
  intro K _ _ R W hW
  obtain ⟨h1, h2, h3, h4, h6⟩ := hW
  obtain ⟨-, hx, -, -, hom, -, hF, -⟩ := Formalism.L2.Th1.A.coeffMem.{0} K W R h1 h2 h3 h4 h6
  refine ⟨logPair W, xIsWp W, ⟨(Formalism.L2.Th1.A.wSerFactor.{0} K W).2.2.2.1, hx⟩, ?_, ?_⟩
  · intro n
    have := (Formalism.L2.Th1.A.fglLog.{0} K W).2
    unfold fadd
    rw [← this]
    exact hF n
  · rw [(Formalism.L2.Th1.A.logSpec.{0} K W).2.2.1]
    exact ⟨(Formalism.L2.Th1.A.unitSpec.{0} K W).2.2.1, hom⟩

theorem curveEndoZ_of (hD : CurveSecondLogDerivative) : CurveEndoZ := by
  intro K _ _ W ι _ neg xP yP al h
  obtain ⟨hE, hn, hxy, hsum⟩ := h
  refine ⟨hn, ?_, hsum⟩
  intro P
  have := hD K W (xP P) (yP P) (hE P)
  show HasSecondLogDeriv (wpShift (wpReg W) (xP P + W.b₂ / 12))
    (2 * wpReg W - wTr W (xP P) (yP P) - wTr W (xP (neg P)) (yP (neg P)))
  rw [(hxy P).1, (hxy P).2]
  exact this

theorem curveEndoR_of (hD : CurveSecondLogDerivative) : CurveEndoR := by
  intro K _ _ R W hW ι _ neg xP yP al albar h hx hy hN ha ha' hc
  obtain ⟨h1, h2, h3, h4, h6⟩ := hW
  have hM := Formalism.L2.Th1.A.coeffMem.{0} K W R h1 h2 h3 h4 h6
  refine ⟨curveEndoZ_of hD K W ι neg xP yP al h, hN, fun P => subst_wTr W _ _, ?_, hx, ha, ha', hc⟩
  intro P n
  exact (hM.2.2.2.2.2.2.2.2.2.2 (xP P) (hx P) (yP P) (hy P) n).1


theorem curve_second_log_derivative_holds : CurveSecondLogDerivative := by
  intro K _ _ W xP yP hP
  exact Formalism.L2.Th1.A.plusZCleared.{0} K W xP yP hP

theorem curve_real_multiplication_series : CurveEndoR := curveEndoR_of curve_second_log_derivative_holds


end Formalism.L2.Th1.C
