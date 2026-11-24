module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.SimpleOverStableSubmoduleTensorPureKernelSpan
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.SimpleTensorProductOperatorStableCountableStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.SimpleOver
public import Init.Prelude
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Dimension.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.SetTheory.Cardinal.Defs
public import Mathlib.SetTheory.Cardinal.Order

@[expose] public section

open scoped TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.simpleOverStableSubmodule_tensorPureKernelSpan : ∀ {V₀ V₁ : Type} [AddCommGroup V₀] [Module ℂ V₀] [AddCommGroup V₁] [Module ℂ V₁]
    (A : Set (Module.End ℂ V₀)) (B : Set (Module.End ℂ V₁)) (K₀ : Submodule ℂ V₀) (K₁ : Submodule ℂ V₁),
    Module.rank ℂ V₀ ≤ Cardinal.aleph0 → GlobalTheory.TensHead.Stab A K₀ → GlobalTheory.TensHead.Stab B K₁ →
    GlobalTheory.TensHead.SimpleOver A K₀ → GlobalTheory.TensHead.SimpleOver B K₁ →
    GlobalTheory.TensHead.SimpleOver (GlobalTheory.TensHead.tensOps A B) (GlobalTheory.TensHead.tensKer K₀ K₁) := by
  first | exact @GlobalTheory.TensHead.simpleOver_tensKer | exact GlobalTheory.TensHead.simpleOver_tensKer | (intros; apply GlobalTheory.TensHead.simpleOver_tensKer <;> assumption)
