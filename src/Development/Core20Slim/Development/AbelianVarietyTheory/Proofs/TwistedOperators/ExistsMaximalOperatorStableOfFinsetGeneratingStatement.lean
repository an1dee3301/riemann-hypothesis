module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsMaximalOperatorStableOfFinsetGenerating
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.SimpleOver
public import Init.Core
public import Init.Prelude
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Notation

@[expose] public section

open scoped TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_maximal_operatorStable_of_finset_generating : ∀ {V : Type} [AddCommGroup V] [Module ℂ V] (G : Set (Module.End ℂ V)) (R : Submodule ℂ V)
    (F : Finset V),
    (∀ N : Submodule ℂ V, R ≤ N → GlobalTheory.TensHead.Stab G N → (↑F : Set V) ⊆ ↑N → N = ⊤) →
    ∀ N : Submodule ℂ V, R ≤ N → GlobalTheory.TensHead.Stab G N → N ≠ ⊤ →
      ∃ N' : Submodule ℂ V, N ≤ N' ∧ GlobalTheory.TensHead.Stab G N' ∧ N' ≠ ⊤ ∧
        ∀ U : Submodule ℂ V, GlobalTheory.TensHead.Stab G U → N' ≤ U → U = N' ∨ U = ⊤ := by
  first | exact @GlobalTheory.TensHead.exists_maximal_stab_of_finset | exact GlobalTheory.TensHead.exists_maximal_stab_of_finset | (intros; apply GlobalTheory.TensHead.exists_maximal_stab_of_finset <;> assumption)
