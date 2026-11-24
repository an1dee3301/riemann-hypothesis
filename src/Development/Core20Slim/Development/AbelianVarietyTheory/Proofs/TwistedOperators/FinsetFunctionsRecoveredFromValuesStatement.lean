module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.FinsetFunctionsRecoveredFromValues
public import Init.Core
public import Init.Prelude
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finset_eq_sum_smul_of_mem_submodule : ∀ {X : Type} (V : Submodule ℂ (X → ℂ)) (F : Finset (X → ℂ)), (∀ u ∈ F, u ∈ V) →
    ∃ (s : Finset X) (E : X → X → ℂ), (∀ x, E x ∈ V) ∧ ∀ u ∈ F, u = ∑ x ∈ s, u x • E x := by
  first | exact @GlobalTheory.finset_functions_recovered_from_values | exact GlobalTheory.finset_functions_recovered_from_values | (intros; apply GlobalTheory.finset_functions_recovered_from_values <;> assumption)
