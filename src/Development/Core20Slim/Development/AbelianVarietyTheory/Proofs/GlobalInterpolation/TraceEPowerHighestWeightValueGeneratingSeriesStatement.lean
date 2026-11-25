module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TraceEPowerHighestWeightValueGeneratingSeries
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.GlobalTwisting.GoodTopBot
public import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.WeylDualWeylLatticesAgreeOfLowestAlcove
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.PowerSeries.Basic

@[expose] public section

open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BasicNotions GlobalTheory.Alc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.traceEPowerHighestWeightValue_generating_series : ∀ (R : Type) [CommRing R] (N : ℕ) (μ : Fin N → R), (1 - PowerSeries.X * PowerSeries.mk (hcVal R μ)) * ∏ i, (1 - PowerSeries.C (shift R μ i) * PowerSeries.X) = ∏ i, (1 - PowerSeries.C (shift R μ i + 1) * PowerSeries.X) := by
  first | exact @GlobalTheory.Alc.hcVal_generating | exact GlobalTheory.Alc.hcVal_generating | (intros; apply GlobalTheory.Alc.hcVal_generating <;> assumption)
