module

public import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.JetExpShape
public import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.FirstLevelFromUniversal
public import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.StatementI
public import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.HasSecondLogDeriv
public import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.CompInv
public import Init.Data.Cast
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Formula
public import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.RingTheory.PowerSeries.Derivative
public import Mathlib.RingTheory.PowerSeries.Substitution

@[expose] public section

noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.C

open Formalism.L2.Th1.A (logSer expSer wpReg xS xPlus)

section Defs8

variable {K : Type} [Field K]

def CoeffIn (R : Subring K) (W : WeierstrassCurve K) : Prop :=
  W.a₁ ∈ R ∧ W.a₂ ∈ R ∧ W.a₃ ∈ R ∧ W.a₄ ∈ R ∧ W.a₆ ∈ R

def wTr (W : WeierstrassCurve K) (xP yP : K) : PowerSeries K :=
  PowerSeries.subst (expSer W) (xPlus W xP yP) + PowerSeries.C (W.b₂ / 12)

def IsEndoCurve (W : WeierstrassCurve K) {ι : Type} [Fintype ι] (neg : ι → ι) (xP yP : ι → K)
    (al : K) : Prop :=
  (∀ P, W.toAffine.Equation (xP P) (yP P)) ∧ (∀ P, neg (neg P) = P) ∧
  (∀ P, xP (neg P) = xP P ∧ yP (neg P) = W.toAffine.negY (xP P) (yP P)) ∧
  PowerSeries.C (al ^ 2) * PowerSeries.rescale al (wpReg W) =
    wpReg W + ∑ P, (wTr W (xP P) (yP P) - PowerSeries.C (xP P + W.b₂ / 12))

end Defs8

def CurveFrame : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (R : Subring K) (W : WeierstrassCurve K), CoeffIn R W →
    IsLogPair (logSer W) (expSer W) ∧ XIsWp (wpReg W) (logSer W) (xS W) (W.b₂ / 12) ∧
    IsOneUnit R (xS W) ∧ FGInt R (logSer W) (expSer W) ∧
    IsOneUnit R (PowerSeries.derivative (R := K) (logSer W))

def CurveSecondLogDerivative : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (W : WeierstrassCurve K) (xP yP : K),
    W.toAffine.Equation xP yP →
    HasSecondLogDeriv (wpShift (wpReg W) (xP + W.b₂ / 12))
      (2 * wpReg W - wTr W xP yP - wTr W xP (W.toAffine.negY xP yP))

def CurveEndoZ : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (W : WeierstrassCurve K) (ι : Type) [Fintype ι]
    (neg : ι → ι) (xP yP : ι → K) (al : K), IsEndoCurve W neg xP yP al →
    IsEndoZ (wpReg W) neg (fun P => xP P + W.b₂ / 12) (fun P => wTr W (xP P) (yP P)) al

def CurveEndoR : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (R : Subring K) (W : WeierstrassCurve K), CoeffIn R W →
    ∀ (ι : Type) [Fintype ι] (neg : ι → ι) (xP yP : ι → K) (al albar : K),
    IsEndoCurve W neg xP yP al → (∀ P, xP P ∈ R) → (∀ P, yP P ∈ R) →
    al * albar = (Fintype.card ι : K) + 1 → al ∈ R → al⁻¹ ∈ R → (al ^ 2 - 1) * (W.b₂ / 12) ∈ R →
    IsEndoR R (wpReg W) (logSer W) (W.b₂ / 12) neg xP (fun P => wTr W (xP P) (yP P))
      (fun P => xPlus W (xP P) (yP P)) al albar


end Formalism.L2.Th1.C
