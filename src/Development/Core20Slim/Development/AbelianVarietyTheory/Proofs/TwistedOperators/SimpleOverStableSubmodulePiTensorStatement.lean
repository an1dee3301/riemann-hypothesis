module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.SimpleOverStableSubmodulePiTensor
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.SimpleOverStableSubmoduleTensorPureKernelSpanStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.OperatorStablePiTensorPureKernelSpanStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.SimpleOver
public import Init.Prelude
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Dimension.Basic
public import Mathlib.LinearAlgebra.PiTensorProduct.Basic
public import Mathlib.SetTheory.Cardinal.Defs
public import Mathlib.SetTheory.Cardinal.Order

@[expose] public section

open scoped TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.simpleOverStableSubmodule_piTensor : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] {M : ι → Type} [∀ i, AddCommGroup (M i)]
    [∀ i, Module ℂ (M i)] (Op : ∀ i, Set (Module.End ℂ (M i))) (K : ∀ i, Submodule ℂ (M i)),
    (∀ i, Module.rank ℂ (M i) ≤ Cardinal.aleph0) → (∀ i, GlobalTheory.TensHead.Stab (Op i) (K i)) →
    (∀ i, GlobalTheory.TensHead.SimpleOver (Op i) (K i)) →
    GlobalTheory.TensHead.SimpleOver (GlobalTheory.TensHead.piOps Op) (GlobalTheory.TensHead.piKer K) := by
  first | exact @GlobalTheory.PiSimple.simpleOver_piKer | exact GlobalTheory.PiSimple.simpleOver_piKer | (intros; apply GlobalTheory.PiSimple.simpleOver_piKer <;> assumption)
