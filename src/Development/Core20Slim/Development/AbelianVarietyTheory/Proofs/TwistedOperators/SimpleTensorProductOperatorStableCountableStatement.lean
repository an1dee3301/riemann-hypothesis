module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.SimpleTensorProductOperatorStableCountable
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.SimpleOver
public import Init.Prelude
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Dimension.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.Order.Notation
public import Mathlib.SetTheory.Cardinal.Defs
public import Mathlib.SetTheory.Cardinal.Order

@[expose] public section

open scoped TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.simple_tensor_product_operatorStable_countable : ∀ {S₀ S₁ : Type} [AddCommGroup S₀] [Module ℂ S₀] [AddCommGroup S₁] [Module ℂ S₁]
    (A : Set (Module.End ℂ S₀)) (B : Set (Module.End ℂ S₁)),
    Module.rank ℂ S₀ ≤ Cardinal.aleph0 →
    (∀ U : Submodule ℂ S₀, GlobalTheory.TensHead.Stab A U → U = ⊥ ∨ U = ⊤) →
    (∀ U : Submodule ℂ S₁, GlobalTheory.TensHead.Stab B U → U = ⊥ ∨ U = ⊤) →
    ∀ U : Submodule ℂ (S₀ ⊗[ℂ] S₁), GlobalTheory.TensHead.Stab (GlobalTheory.TensHead.tensOps A B) U → U = ⊥ ∨ U = ⊤ := by
  first | exact @GlobalTheory.TensHead.simple_tensor | exact GlobalTheory.TensHead.simple_tensor | (intros; apply GlobalTheory.TensHead.simple_tensor <;> assumption)
