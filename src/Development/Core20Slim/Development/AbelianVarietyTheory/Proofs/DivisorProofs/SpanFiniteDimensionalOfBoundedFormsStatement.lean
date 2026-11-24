module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpanFiniteDimensionalOfBoundedForms
public import Init.Core
public import Init.Prelude
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.Span.Defs

@[expose] public section

open Topology Filter
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteDimensional_span_of_forall_linear_bounded : ∀ {V : Type} [AddCommGroup V] [Module ℂ V] (s : Set V),
    (∀ l : V →ₗ[ℂ] ℂ, ∃ C : ℝ, ∀ x ∈ s, ‖l x‖ ≤ C) → FiniteDimensional ℂ (Submodule.span ℂ s) := by
  first | exact @GlobalTheory.span_finiteDimensional_of_bounded_forms | exact GlobalTheory.span_finiteDimensional_of_bounded_forms | (intros; apply GlobalTheory.span_finiteDimensional_of_bounded_forms <;> assumption)
