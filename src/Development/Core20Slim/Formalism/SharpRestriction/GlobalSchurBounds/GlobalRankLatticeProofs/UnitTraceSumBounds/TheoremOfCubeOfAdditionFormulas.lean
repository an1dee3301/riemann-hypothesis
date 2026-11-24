module

public import Development.Core20Slim.Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.BeConjOfNormHolds
public import Development.Core20Slim.Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.AdditionIdentityOfSigmaFormulaUnit
public import Development.Core20Slim.Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.FormalGroupLawFirstHalfHolds
public import Mathlib
public import Development.Core20Slim.Formalism.PeriodIntegrals.OrbitalBoundsConclusion.FglTriFactor
public import Development.Core20Slim.Formalism.PeriodIntegrals.OrbitalBoundsConclusion.FglChordFactor
public import Development.Core20Slim.Formalism.PeriodIntegrals.OrbitalBoundsConclusion.CubicExponentialFactor
public import Development.Core20Slim.Formalism.PeriodIntegrals.OrbitalBoundsConclusion.PhiCubeOfFactor
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
public import Development.Core20Slim.Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.AdditionIdentityOfSigmaFormula
public import Development.Core20Slim.Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.CubeIdentityFromAdditionFormula
public import Development.Core20Slim.Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.LevelRestrictionOfGroupLawHolds
public import Development.Core20Slim.Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.PhIsotropicOf
public import Init.Core
public import Init.Data.Fin.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange
public import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Completion
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Logic.Basic
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.MvPowerSeries.Inverse
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.RingTheory.PowerSeries.Substitution
public import Mathlib.Topology.Algebra.GroupCompletion
public import Mathlib.Topology.Algebra.UniformField
public import Mathlib.Topology.Algebra.UniformRing
public import Mathlib.Topology.Algebra.Valued.ValuationTopology

@[expose] public section

namespace Formalism.MainNotions.Ext.CutA

open Formalism.MainNotions.GL3Theta Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3r7

theorem lemma_three_one_third_holds : LemmaThreeOneThird := by
  intro p hp g hOk hI
  obtain ⟨⟨h1, h2, h3, h4, h6, hΔ⟩, hW, he0, hel⟩ := hOk
  exact formal_group_tri_factor p g.W g.wq g.ex h1 h2 h3 h4 h6 hΔ hW he0 hel hI

theorem lemma_three_one_second_holds : UnitTraceSumSecondBound := by
  intro p hp g hOk hI
  obtain ⟨⟨h1, h2, h3, h4, h6, hΔ⟩, hW, he0, hel⟩ := hOk
  exact fglChordFactor p g.W g.wq g.ex h1 h2 h3 h4 h6 hΔ hW he0 hel hI

theorem cube3OfDet_holds : Cube3OfDet := by
  intro p hp g hOk hE hQ hn
  obtain ⟨⟨h1, h2, h3, h4, h6, hΔ⟩, hW, he0, hel⟩ := hOk
  exact thetaCube_triple_relation p g.W g.wq g.l g.ex (ePhi1 g.lam g.abelian₂ g.C g.wq) _ h1 h2 h3 h4 h6 hW he0 hel hE hQ hn

theorem cube_second_of_determinant_formula (D : Formalism.BasicNotions.D7) (hQ : PAdicFrobeniusStickelberger D) : cube3 D :=
  cube_second_identity_of_determinant lemma_three_one_third_holds cube3OfDet_holds D hQ (addInt_holds D)

theorem cube_first_of_addition_holds : CubeIdentityFromAdditionFormula := by
  intro p hp g hOk hE hId hn
  obtain ⟨_, hW, he0, hel⟩ := hOk
  exact phiCubeOfFactor p _ g.ex _ _ he0 hel hE hId hn

theorem cube_first_of_addition_formula (D : Formalism.BasicNotions.D7) (hQ : PAdicSigmaAdditionFormula D) : cube2 D :=
  addition_identity_of_sigma_formula lemma_three_one_second_holds cube_first_of_addition_holds D hQ (ePhiOne_holds D) (addInt_holds D)

theorem theorem_of_cube_of_addition_formulas (D : Formalism.BasicNotions.D7) (hQ : PAdicSigmaAdditionFormula D) (hQd : PAdicFrobeniusStickelberger D) : cube D :=
  cube_of cube_of_two_identities_holds D (cube_first_of_addition_formula D hQ) (cube_second_of_determinant_formula D hQd)

end Formalism.MainNotions.Ext.CutA
