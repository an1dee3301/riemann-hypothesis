module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoverUpqClosureExpTopAndCartan
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.Foundations.IsFockIPOfFockData
public import Formalism.LocalRingCardinality.DataTheta
public import Init.Core
public import Init.Prelude
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Notation

@[expose] public section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coverUpq_closure_exp_top_and_cartan : ∀ (p q : ℕ), 1 ≤ p + q → ∀ T : GrpData p q, Subgroup.closure (T.expt '' upq p q) = ⊤ ∧ ∀ g : T.G, ∃ k ∈ T.Kset, ∃ Y ∈ pR p q, g = k * T.expt Y := by
  first | exact @GlobalTheory.CoverExp.closure_expt_eq_top_and_cartan | exact GlobalTheory.CoverExp.closure_expt_eq_top_and_cartan | (intros; apply GlobalTheory.CoverExp.closure_expt_eq_top_and_cartan <;> assumption)
