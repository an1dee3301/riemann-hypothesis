module

public import Development.Core20Slim.Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.CubeIdentityFromAdditionFormula
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Data.Fin.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Nat.Coprime
public import Init.Data.NeZero
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Order.Kleene
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Instances
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Logic.Basic
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
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

namespace Formalism.MainNotions.Ext.CutA

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3Theta NumberField

def EPhiOne (D : D7) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (g : G1 p), At D cc δ g →
    PowerSeries.constantCoeff (ePhi1 g.lam g.abelian₂ g.C g.wq) = 1

def PAdicSigmaAdditionFormula (D : D7) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (g : G1 p), At D cc δ g →
    g.add (Xv 0) (Xv 1) * g.sub (Xv 0) (Xv 1) *
        PowerSeries.subst (g.add (Xv 0) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p]) (ePhi1 g.lam g.abelian₂ g.C g.wq) *
        PowerSeries.subst (g.sub (Xv 0) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p]) (ePhi1 g.lam g.abelian₂ g.C g.wq) =
      ((Xv 0) ^ 2 * (PowerSeries.subst (Xv 1 : MvPowerSeries (Fin 2) ℂ_[p]) g.wq)⁻¹ -
          (Xv 1) ^ 2 * (PowerSeries.subst (Xv 0 : MvPowerSeries (Fin 2) ℂ_[p]) g.wq)⁻¹) *
        PowerSeries.subst (Xv 0 : MvPowerSeries (Fin 2) ℂ_[p]) (ePhi1 g.lam g.abelian₂ g.C g.wq) ^ 2 *
        PowerSeries.subst (Xv 1 : MvPowerSeries (Fin 2) ℂ_[p]) (ePhi1 g.lam g.abelian₂ g.C g.wq) ^ 2

theorem addition_identity_of_sigma_formula (H31 : UnitTraceSumSecondBound) (HC : CubeIdentityFromAdditionFormula) (D : D7) (hQ : PAdicSigmaAdditionFormula D) (hE : EPhiOne D) (ha : addInt D) :
    cube2 D := by
  intro p _ cc δ g hA
  have ok : g.Ok := hA.2.2.2.2
  exact HC p g ok (hE p cc δ g hA) (hQ p cc δ g hA) (H31 p g ok (ha p cc δ g hA).1)

end Formalism.MainNotions.Ext.CutA
