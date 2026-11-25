module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeKerOfLocalFiniteLengthToSimple
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.SimpleOver
public import Init.Core
public import Init.Prelude
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Ker
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Fin.Basic
public import Mathlib.Order.Monotone.Defs
public import Mathlib.Order.Notation

@[expose] public section

open scoped TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.le_ker_of_local_finite_length_to_simple : ∀ {M W : Type} [AddCommGroup M] [Module ℂ M] [AddCommGroup W] [Module ℂ W]
    (Op : Set (Module.End ℂ M)) (Rel K : Submodule ℂ M) (φ : M →ₗ[ℂ] W)
    (act : Module.End ℂ M → Module.End ℂ W) (B : Set (Module.End ℂ W)),
    (∃ L : ℕ, ∀ (m : ℕ) (N : Fin m → Submodule ℂ M), StrictMono N →
        (∀ j, Rel ≤ N j ∧ ∀ g ∈ Op, ∀ x ∈ N j, g x ∈ N j) → m ≤ L) →
    (∀ N : Submodule ℂ M, Rel ≤ N → GlobalTheory.TensHead.Stab Op N → N ≠ ⊤ → N ≤ K) →
    K ≠ ⊤ → GlobalTheory.TensHead.Stab Op K → Rel ≤ LinearMap.ker φ →
    (∀ g ∈ Op, φ ∘ₗ g = act g ∘ₗ φ) →
    (∀ g ∈ Op, ∀ b ∈ B, act g * b = b * act g) →
    (∀ U : Submodule ℂ W, GlobalTheory.TensHead.Stab (act '' Op ∪ B) U → U = ⊥ ∨ U = ⊤) →
    K ≤ LinearMap.ker φ := by
  first | exact @GlobalTheory.TensHead.le_ker_of_simple_commuting | exact GlobalTheory.TensHead.le_ker_of_simple_commuting | (intros; apply GlobalTheory.TensHead.le_ker_of_simple_commuting <;> assumption)
