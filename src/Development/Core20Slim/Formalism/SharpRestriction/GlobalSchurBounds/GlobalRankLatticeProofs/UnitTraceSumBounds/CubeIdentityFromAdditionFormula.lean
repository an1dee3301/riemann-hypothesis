module

public import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
public import Init.Core
public import Init.Data.Fin.Basic
public import Init.Data.Nat.Basic
public import Init.Data.NeZero
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Instances
public import Mathlib.Analysis.Normed.Ring.Basic
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
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.MvPowerSeries.Inverse
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.RingTheory.PowerSeries.Substitution
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

open Formalism.MainNotions.GL3Theta Formalism.MainNotions.TaylorLogMetric

namespace Formalism.MainNotions.Ext.CutA

def UnitTraceSumSecondBound : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (g : G1 p), g.Ok → IntegralMv (g.add (Xv 0) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p]) →
    ∃ n : MvPowerSeries (Fin 2) ℂ_[p], IntegralMv n ∧ MvPowerSeries.constantCoeff n = 1 ∧
      (Xv 0) ^ 2 * (PowerSeries.subst (Xv 1 : MvPowerSeries (Fin 2) ℂ_[p]) g.wq)⁻¹ -
          (Xv 1) ^ 2 * (PowerSeries.subst (Xv 0 : MvPowerSeries (Fin 2) ℂ_[p]) g.wq)⁻¹ =
        g.add (Xv 0) (Xv 1) * g.sub (Xv 0) (Xv 1) * n

def CubeIdentityFromAdditionFormula : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (g : G1 p), g.Ok →
    PowerSeries.constantCoeff (ePhi1 g.lam g.abelian₂ g.C g.wq) = 1 →
    g.add (Xv 0) (Xv 1) * g.sub (Xv 0) (Xv 1) *
        PowerSeries.subst (g.add (Xv 0) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p]) (ePhi1 g.lam g.abelian₂ g.C g.wq) *
        PowerSeries.subst (g.sub (Xv 0) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p]) (ePhi1 g.lam g.abelian₂ g.C g.wq) =
      ((Xv 0) ^ 2 * (PowerSeries.subst (Xv 1 : MvPowerSeries (Fin 2) ℂ_[p]) g.wq)⁻¹ -
          (Xv 1) ^ 2 * (PowerSeries.subst (Xv 0 : MvPowerSeries (Fin 2) ℂ_[p]) g.wq)⁻¹) *
        PowerSeries.subst (Xv 0 : MvPowerSeries (Fin 2) ℂ_[p]) (ePhi1 g.lam g.abelian₂ g.C g.wq) ^ 2 *
        PowerSeries.subst (Xv 1 : MvPowerSeries (Fin 2) ℂ_[p]) (ePhi1 g.lam g.abelian₂ g.C g.wq) ^ 2 →
    (∃ n : MvPowerSeries (Fin 2) ℂ_[p], IntegralMv n ∧ MvPowerSeries.constantCoeff n = 1 ∧
      (Xv 0) ^ 2 * (PowerSeries.subst (Xv 1 : MvPowerSeries (Fin 2) ℂ_[p]) g.wq)⁻¹ -
          (Xv 1) ^ 2 * (PowerSeries.subst (Xv 0 : MvPowerSeries (Fin 2) ℂ_[p]) g.wq)⁻¹ =
        g.add (Xv 0) (Xv 1) * g.sub (Xv 0) (Xv 1) * n) →
    Simeq (g.phAt (g.add (Xv 0) (Xv 1)) + g.phAt (g.sub (Xv 0) (Xv 1)) : MvPowerSeries (Fin 2) ℂ_[p])
      (2 * g.phAt (Xv 0) + 2 * g.phAt (Xv 1))

end Formalism.MainNotions.Ext.CutA
