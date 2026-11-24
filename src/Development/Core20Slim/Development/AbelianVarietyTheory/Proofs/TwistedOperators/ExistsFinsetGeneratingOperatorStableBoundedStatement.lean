module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFinsetGeneratingOperatorStableBounded
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.SimpleOver
public import Init.Core
public import Init.Prelude
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Fin.Basic
public import Mathlib.Order.Monotone.Defs
public import Mathlib.Order.Notation

@[expose] public section

open scoped TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finset_generating_operator_stable_bounded : ∀ {M : Type} [AddCommGroup M] [Module ℂ M] (Op : Set (Module.End ℂ M)) (Rel : Submodule ℂ M),
    (∃ L : ℕ, ∀ (m : ℕ) (N : Fin m → Submodule ℂ M), StrictMono N →
        (∀ j, Rel ≤ N j ∧ ∀ g ∈ Op, ∀ x ∈ N j, g x ∈ N j) → m ≤ L) →
    ∃ F : Finset M, ∀ N : Submodule ℂ M, Rel ≤ N → GlobalTheory.TensHead.Stab Op N → (↑F : Set M) ⊆ ↑N → N = ⊤ := by
  first | exact @GlobalTheory.StabGen.exists_finset_generating | exact GlobalTheory.StabGen.exists_finset_generating | (intros; apply GlobalTheory.StabGen.exists_finset_generating <;> assumption)
