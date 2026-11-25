module

public import Development.Core20Slim.Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.CurveSecondLogDerivative
public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.FinalB
public import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.TwoTorsionU
public import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.HasSecondLogDeriv
public import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.IsotropicVanish
public import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.PhNormFromDatum
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
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
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Data.Int.Cast.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Int.Init
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.PowerSeries.Basic

@[expose] public section

noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.G

open Formalism.L2.Th1.C
open Formalism.L2.Th1.A (logSer expSer wpReg xS xPlus)
open Formalism.G (unitBall)

namespace WeierstrassCurveSeries




theorem endInt_int {K : Type} [Field K] (R : Subring K) (l linv : PowerSeries K)
    (hl : IsLogPair l linv) (hF : FGInt R l linv) (n : ℤ) : EndInt R l linv (n : K) := by
  obtain ⟨-, -, h0, h1, hm, hadd, -⟩ := ptClosure K R l linv hl hF
  induction n using Int.induction_on with
  | zero => simpa using h0
  | succ i ih =>
    have := hadd _ _ ih h1
    simpa using this
  | pred i ih =>
    have := hadd _ _ ih hm
    simpa [sub_eq_add_neg] using this

end WeierstrassCurveSeries

open WeierstrassCurveSeries





end Formalism.L2.Th1.G
