module

public import Mathlib
public import Init.Core
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Module.Submodule.Map
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Multilinear.Basic
public import Mathlib.LinearAlgebra.PiTensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Map
public import Mathlib.Logic.Function.Basic
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Notation
public import Mathlib.Order.SetNotation

@[expose] public section

open scoped TensorProduct

noncomputable section

namespace UpperTheory.Lit.HoweDuality

section One

variable {M : Type} [AddCommGroup M] [Module ℂ M]

def Stable (Op : Set (Module.End ℂ M)) (P : Submodule ℂ M) : Prop := ∀ g ∈ Op, ∀ x ∈ P, g x ∈ P

def Gen (Op : Set (Module.End ℂ M)) (Rel : Submodule ℂ M) (s : M) : Prop :=
  ∀ P : Submodule ℂ M, Rel ≤ P → Stable Op P → s ∈ P → P = ⊤

def Rad (Op : Set (Module.End ℂ M)) (Rel K : Submodule ℂ M) : Prop :=
  ∃ s, Gen Op Rel s ∧ ∀ k ∈ K, ∃ e ∈ Algebra.adjoin ℂ Op, e s = s ∧ e k ∈ Rel

def RadFin (Op : Set (Module.End ℂ M)) (Rel K : Submodule ℂ M) : Prop :=
  ∃ s, Gen Op Rel s ∧ ∀ S : Finset M, (∀ k ∈ S, k ∈ K) → ∃ e ∈ Algebra.adjoin ℂ Op, e s = s ∧ ∀ k ∈ S, e k ∈ Rel

end One

section Tensor

variable {ι : Type} [Fintype ι] [DecidableEq ι] {M₀ : Type} [AddCommGroup M₀] [Module ℂ M₀]
  {M : ι → Type} [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)]

def intersection_update_fsHerm_neg_one (i : ι) (r : M₀ × ∀ j, M j) : M i →ₗ[ℂ] M₀ ⊗[ℂ] (⨂[ℂ] j, M j) :=
  TensorProduct.mk ℂ M₀ _ r.1 ∘ₗ (PiTensorProduct.tprod ℂ (s := M)).toLinearMap r.2 i

omit [Fintype ι] in
theorem position_apply (i : ι) (r : M₀ × ∀ j, M j) (x : M i) :
    intersection_update_fsHerm_neg_one i r x = r.1 ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ (Function.update r.2 i x) := rfl

def factorOp (i : ι) (g : Module.End ℂ (M i)) : Module.End ℂ (M₀ ⊗[ℂ] (⨂[ℂ] j, M j)) :=
  TensorProduct.map LinearMap.id
    (PiTensorProduct.map (Function.update (fun j => (LinearMap.id : M j →ₗ[ℂ] M j)) i g))


variable (M₀) in
def part (i : ι) (K : Submodule ℂ (M i)) : Submodule ℂ (M₀ ⊗[ℂ] (⨂[ℂ] j, M j)) :=
  ⨆ r : M₀ × ∀ j, M j, K.map (intersection_update_fsHerm_neg_one i r)

end Tensor

end UpperTheory.Lit.HoweDuality

end
