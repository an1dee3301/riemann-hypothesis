module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.LinearMapChainCompositeUpdateSmul
public import Development.AbelianVarietyTheory.Definitions.Divisors.InvVolConjLevelOne
public import Init.Prelude
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Logic.Function.Basic

@[expose] public section

open GlobalTheory.FunObj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linearMapChainComposite_update_smul : ∀ {V : ℕ → Type} [∀ j, AddCommGroup (V j)] [∀ j, Module ℂ (V j)] (k : ∀ j, V j →ₗ[ℂ] V (j + 1)) (j₀ : ℕ)
    (c : ℂ) (A : V j₀ →ₗ[ℂ] V (j₀ + 1)) (n : ℕ), j₀ < n →
    chainTo (Function.update k j₀ (c • A)) n = c • chainTo (Function.update k j₀ A) n := by
  first | exact @GlobalTheory.ChainSmul.chainTo_update_smul | exact GlobalTheory.ChainSmul.chainTo_update_smul | (intros; apply GlobalTheory.ChainSmul.chainTo_update_smul <;> assumption)
