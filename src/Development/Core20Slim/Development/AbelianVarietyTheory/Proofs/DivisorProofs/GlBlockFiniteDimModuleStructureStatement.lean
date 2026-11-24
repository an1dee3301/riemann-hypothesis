module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlBlockFiniteDimModuleStructure
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.Foundations.IsFockIPOfFockData
public import Formalism.LocalRingCardinality.DataTheta
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Rat.Basic
public import Init.Prelude
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.Order.Bounds.Defs
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Defs
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Notation
public import Mathlib.Order.SetNotation

@[expose] public section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.glBlock_finiteDim_module_structure : ∀ (p q : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (act : Mat p q →ₗ[ℂ] Module.End ℂ V), IsKLieAct act → ∀ W : Submodule ℂ V, FiniteDimensional ℂ W → KStable act W → (∀ v ∈ W, v ∈ ⨆ μ : Ix p q → ℚ, wtSub act μ) → (∀ U : Submodule ℂ V, U ≤ W → KStable act U → ∃ U' : Submodule ℂ V, KStable act U' ∧ U ⊓ U' = ⊥ ∧ U ⊔ U' = W) ∧ (W ≠ ⊥ → ∃ μ v, v ∈ W ∧ IsHW act μ v) ∧ (∀ v ∈ W, v ∈ ⨆ μ : Ix p q → ℚ, Submodule.span ℂ {w | w ∈ W ∧ OfType act μ w}) ∧ (∀ μ v, v ∈ W → IsHW act μ v → (∀ a b, posC a b → ∃ k : ℕ, μ a - μ b = k) ∧ OfType act μ v ∧ ∀ U : Submodule ℂ V, KStable act U → U ≤ sInf {N | v ∈ N ∧ KStable act N} → U = ⊥ ∨ v ∈ U) := by
  first | exact @GlobalTheory.BlockReps.finite_module_structure | exact GlobalTheory.BlockReps.finite_module_structure | (intros; apply GlobalTheory.BlockReps.finite_module_structure <;> assumption)
