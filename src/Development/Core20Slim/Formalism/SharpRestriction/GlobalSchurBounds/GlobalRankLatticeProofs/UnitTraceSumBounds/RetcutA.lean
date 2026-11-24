module

public import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
public import Development.Core20Slim.Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.PhNormOfUnits
public import Development.Core20Slim.Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.CubeOfTwoIdentities
public import Mathlib
public import Development.Core20Slim.Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CubeFormalIdentities.CoeffPowMulPowEqZero
public import Development.Core20Slim.Formalism.PeriodIntegrals.OrbitalBoundsConclusion.PhNormUnits
public import Development.Core20Slim.Formalism.PeriodIntegrals.OrbitalBoundsConclusion.PhNormLimit
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Logic.Basic
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.RingTheory.PowerSeries.Substitution
public import Mathlib.Topology.Algebra.GroupCompletion
public import Mathlib.Topology.Algebra.UniformField
public import Mathlib.Topology.Algebra.UniformRing
public import Mathlib.Topology.Algebra.Valued.ValuationTopology

@[expose] public section

namespace Formalism.MainNotions.Ext.CutA

theorem phNormOfUnits_holds : PhNormOfUnits := by
  intro p _ g S hok
  exact phase_norm_units p g.l g.ex g.ph S hok.2.2.1 hok.2.2.2

theorem phNormClosed_holds : PhNormClosed := by
  intro p _ g S hok
  exact phase_norm_limit_target p g.l g.ex g.ph S hok.2.2.1 hok.2.2.2

end Formalism.MainNotions.Ext.CutA
