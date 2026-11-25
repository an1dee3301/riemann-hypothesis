module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormCreationAnnihilationWordLeNumberOperatorPow
public import Init.Core
public import Init.Data.List.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Mathlib.Analysis.CStarAlgebra.Module.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.LinearAlgebra.Span.Defs

@[expose] public section

open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_creationAnnihilation_word_le_numberOperator_pow : ∀ (T H κ : Type) [AddCommGroup T] [Module ℂ T] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [Fintype κ] (Φ : T →ₗ[ℂ] H) (a c : κ → Module.End ℂ T) (M : Module.End ℂ T) (r r' : ℝ), 1 ≤ r → r' ≤ r → (∀ j x y, inner ℂ (Φ (c j x)) (Φ y) = inner ℂ (Φ x) (Φ (a j y))) → (∀ j, a j * c j - c j * a j = (r' : ℂ) • 1) → M = ∑ j, c j * a j + (r : ℂ) • 1 → (∀ j, M * a j = a j * (M - (r : ℂ) • 1)) → (∀ j, M * c j = c j * (M + (r : ℂ) • 1)) → ∀ (l : List (Module.End ℂ T)) (d : ℕ), (∀ X ∈ l, X ∈ Submodule.span ℂ (Set.range a ∪ Set.range c)) → l.length ≤ d → ∃ C : ℝ, ∀ x, ‖Φ (l.prod x)‖ ≤ C * ‖Φ ((M ^ d) x)‖ := by
  first | exact @GlobalTheory.norm_word_le_number_pow | exact GlobalTheory.norm_word_le_number_pow | (intros; apply GlobalTheory.norm_word_le_number_pow <;> assumption)
