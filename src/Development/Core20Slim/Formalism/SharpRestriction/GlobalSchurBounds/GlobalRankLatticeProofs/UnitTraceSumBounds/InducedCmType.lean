module

public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Formalism.SharpRestriction.GlobalSchurBounds.Joints
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.CMFieldLemmas
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.EqOfLeOfAbsNormEq
public import Formalism.FrobeniusOrbits.Statement
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.GlobalSchurBounds.CMFieldLemmas
public import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.FiltrationBoundaryCriterion
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.SecondPropositionEveryLocalisation
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ZsmulGeneratorEqZeroOfProjection
public import Init.Classical
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Group.TypeTags.Finite
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Units.Fintype
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Filter
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.FunLike.Fintype
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.Logic.Equiv.Defs

@[expose] public section

namespace Formalism.MainNotions.GL3Theta

open Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric

theorem induced_cm_type (D : D7) : InducedCMType D := by
  intro τ a

  have hmem : embT D τ ∈ Formalism.MainNotions.GlobalTheoryTheory.PhiEmb D := ⟨((D.eTau τ : D.R.Psi) : D.R.GG), (D.eTau τ).2, rfl⟩
  exact (Formalism.MainNotions.UnusedSlot33.second_proposition_every_localisation D).2.1 _ hmem _ a.2


end Formalism.MainNotions.GL3Theta
