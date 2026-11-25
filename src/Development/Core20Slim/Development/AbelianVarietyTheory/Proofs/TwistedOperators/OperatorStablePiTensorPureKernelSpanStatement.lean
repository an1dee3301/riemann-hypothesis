module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.OperatorStablePiTensorPureKernelSpan
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.SimpleOver
public import Init.Prelude
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.PiTensorProduct.Basic

@[expose] public section

open scoped TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.operatorStable_piTensorPureKernelSpan : ∀ {ι : Type} [DecidableEq ι] {M : ι → Type} [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)]
    (Op : ∀ i, Set (Module.End ℂ (M i))) (K : ∀ i, Submodule ℂ (M i)),
    (∀ i, GlobalTheory.TensHead.Stab (Op i) (K i)) →
    GlobalTheory.TensHead.Stab (GlobalTheory.TensHead.piOps Op) (GlobalTheory.TensHead.piKer K) := by
  first | exact @GlobalTheory.TensHead.stab_piOps_piKer | exact GlobalTheory.TensHead.stab_piOps_piKer | (intros; apply GlobalTheory.TensHead.stab_piOps_piKer <;> assumption)
