module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.EquivariantHomMultiplicityFreeIrreducible
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.LatticeFrames.EvalAtOneExtremalMul
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.DirectSum.Basic
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.Order.Notation
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.RepresentationTheory.Intertwining
public import Mathlib.RepresentationTheory.Irreducible

@[expose] public section

open MvPolynomial Formalism.BasicNotions Formalism.L2.Forms Formalism.L2.Ker GlobalTheory.KJInf MeasureTheory
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.equivariantHom_multiplicityFree_irreducible : ∀ (G H J : Type) [Group G] [Group H] [DecidableEq J] (A B : J → Type) [∀ j, AddCommGroup (A j)] [∀ j, Module ℂ (A j)] [∀ j, AddCommGroup (B j)] [∀ j, Module ℂ (B j)] [∀ j, FiniteDimensional ℂ (A j)] [∀ j, FiniteDimensional ℂ (B j)] (α : ∀ j, Representation ℂ G (A j)) (β : ∀ j, Representation ℂ H (B j)), (∀ j, (α j).IsIrreducible) → (∀ j, (β j).IsIrreducible) → (∀ j j', Nonempty ((α j).Equiv (α j')) → j = j') → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (ω : Representation ℂ (G × H) W), Nonempty ((Representation.directSum fun j => Representation.tprod ((α j).comp (MonoidHom.fst G H)) ((β j).comp (MonoidHom.snd G H))).Equiv ω) → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (ρ : Representation ℂ G V), ρ.IsIrreducible → ∀ S : Submodule ℂ (V →ₗ[ℂ] W), (∀ T ∈ S, ∀ g v, T (ρ g v) = ω (g, 1) (T v)) → (∀ T ∈ S, ∀ h, ω (1, h) ∘ₗ T ∈ S) → S ≠ ⊥ → ∀ Q : V →ₗ[ℂ] W, (∀ g v, Q (ρ g v) = ω (g, 1) (Q v)) → Q ∈ S := by
  first | exact @GlobalTheory.EquivHomIrr.equivariantHom_mem_of_stable | exact GlobalTheory.EquivHomIrr.equivariantHom_mem_of_stable | (intros; apply GlobalTheory.EquivHomIrr.equivariantHom_mem_of_stable <;> assumption)
