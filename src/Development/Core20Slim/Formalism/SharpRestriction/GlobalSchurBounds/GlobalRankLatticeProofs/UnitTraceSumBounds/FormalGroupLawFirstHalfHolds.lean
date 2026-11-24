module

public import Development.Core20Slim.Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.ModelShortOf
public import Development.Core20Slim.Formalism.PeriodIntegrals.OrbitalBoundsConclusion.BiaddOfCube
public import Development.Core20Slim.Formalism.PeriodIntegrals.OrbitalBoundsConclusion.AddIntG
public import Mathlib
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Data.Fin.Basic
public import Init.Data.Nat.Coprime
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Order.Kleene
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange
public import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Completion
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Logic.Basic
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Basic.Real.Basic
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
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.RingTheory.PowerSeries.Substitution
public import Mathlib.Topology.Algebra.GroupCompletion
public import Mathlib.Topology.Algebra.UniformField
public import Mathlib.Topology.Algebra.UniformRing
public import Mathlib.Topology.Algebra.Valued.ValuationTopology

@[expose] public section

namespace Formalism.MainNotions.Ext

theorem biaddOfCube_holds : BiaddOfCube :=
  fun p _ g hOk hc => biadditiveOfCube_holds p g.l g.ex g.ph hOk.2.2.1 hOk.2.2.2 hc

theorem beBiadd_of_cube (D : Formalism.BasicNotions.D7) (h : Formalism.MainNotions.GL3Theta.cube D) : Formalism.MainNotions.GL3Theta.beBiadd D := by
  intro p _ cc δ g hA
  exact biaddOfCube_holds p g hA.2.2.2.2 (h p cc δ g hA)

theorem addIntG_holds : AddIntG := fun p _ g hOk =>
  additive_integral_generation p g.W g.wq g.ex hOk.1.1 hOk.1.2.1 hOk.1.2.2.1 hOk.1.2.2.2.1 hOk.1.2.2.2.2.1 hOk.2.1 hOk.2.2.1 hOk.2.2.2

theorem addInt_holds (D : Formalism.BasicNotions.D7) : Formalism.MainNotions.GL3Theta.addInt D := by
  intro p _ cc δ g hA
  exact addIntG_holds p g hA.2.2.2.2

end Formalism.MainNotions.Ext
