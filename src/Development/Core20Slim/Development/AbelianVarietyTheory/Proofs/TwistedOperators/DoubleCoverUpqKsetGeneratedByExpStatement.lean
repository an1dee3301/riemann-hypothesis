module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.DoubleCoverUpqKsetGeneratedByExp
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalRingCardinality.DataTheta
public import Init.Prelude
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Set.Defs

@[expose] public section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubleCoverUpq_Kset_generated_by_exp : ∀ (p q : ℕ), 1 ≤ p + q → ∀ (T : GrpData p q), ∀ k ∈ T.Kset, k ∈ Subgroup.closure (T.expt '' {Y | Y ∈ upq p q ∧ IsKC Y}) := by
  first | exact @GlobalTheory.CoverKGen.kset_gen | exact GlobalTheory.CoverKGen.kset_gen | (intros; apply GlobalTheory.CoverKGen.kset_gen <;> assumption)
