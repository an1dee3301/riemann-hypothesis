module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.SubmodulePowSimpleEqSumEquivValues
public import Init.Core
public import Init.Prelude
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Order.Notation

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_sum_intertwined_of_mem_invariant_submodule : ∀ {P : Type} [AddCommGroup P] [Module ℂ P] {ι : Type} (a : ι → Module.End ℂ P),
    (∀ B : Submodule ℂ P, (∀ i, ∀ p ∈ B, a i p ∈ B) → B ≠ ⊥ → B = ⊤) →
    ∀ (m : ℕ) (N : Submodule ℂ (Fin m → P)), (∀ i, ∀ y ∈ N, (fun j => a i (y j)) ∈ N) →
    ∀ y ∈ N, ∃ (n : ℕ) (Sm : Fin n → (P →ₗ[ℂ] (Fin m → P))) (q : Fin n → P),
      (∀ l i p, Sm l (a i p) = fun j => a i (Sm l p j)) ∧ (∀ l p, Sm l p ∈ N) ∧ y = ∑ l, Sm l (q l) := by
  first | exact @GlobalTheory.submodule_pow_simple_eq_sum_equiv_values | exact GlobalTheory.submodule_pow_simple_eq_sum_equiv_values | (intros; apply GlobalTheory.submodule_pow_simple_eq_sum_equiv_values <;> assumption)
