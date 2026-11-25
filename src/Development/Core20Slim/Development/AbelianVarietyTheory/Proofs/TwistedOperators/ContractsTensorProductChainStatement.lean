module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContractsTensorProductChain
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NonemptyInvFunEquiv
public import Init.Core
public import Init.Data.Fin.Basic
public import Init.Data.Function
public import Init.Data.Nat.Basic
public import Init.Data.NeZero
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.PiTensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.RepresentationTheory.Basic

@[expose] public section

open MvPolynomial GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries GlobalTheory.OneFunctional Formalism.BasicNotions GlobalTheory.Branching
open scoped TensorProduct DirectSum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.contracts_tensorProduct_chain : ∀ (m : ℕ) (G : Fin (m + 1) → Type) [∀ j, Monoid (G j)] (F : Fin m → Type) [∀ j, AddCommGroup (F j)] [∀ j, Module ℂ (F j)] (V : Fin (m + 1) → Type) [∀ j, AddCommGroup (V j)] [∀ j, Module ℂ (V j)] (φ : ∀ j : Fin m, Representation ℂ (G j.castSucc × G j.succ) (F j)) (σ : ∀ j, Representation ℂ (G j) (V j)), (∀ j : Fin m, Contracts (φ j) (σ j.castSucc) (σ j.succ)) → ∃ π : ((⨂[ℂ] j, F j) ⊗[ℂ] V 0) →ₗ[ℂ] V (Fin.last m), Function.Surjective π ∧ (∀ (g : ∀ j, G j) (f : ⨂[ℂ] j, F j) (v : V 0), π (PiTensorProduct.map (fun j => φ j (g j.castSucc, g j.succ)) f ⊗ₜ[ℂ] σ 0 (g 0) v) = σ (Fin.last m) (g (Fin.last m)) (π (f ⊗ₜ[ℂ] v))) ∧ ∀ l : Module.Dual ℂ ((⨂[ℂ] j, F j) ⊗[ℂ] V 0), (∀ g : ∀ j, G j, g (Fin.last m) = 1 → ∀ (f : ⨂[ℂ] j, F j) (v : V 0), l (PiTensorProduct.map (fun j => φ j (g j.castSucc, g j.succ)) f ⊗ₜ[ℂ] σ 0 (g 0) v) = l (f ⊗ₜ[ℂ] v)) → ∀ x, π x = 0 → l x = 0 := by
  first | exact @GlobalTheory.OneFunctional.contracts_chain | exact GlobalTheory.OneFunctional.contracts_chain | (intros; apply GlobalTheory.OneFunctional.contracts_chain <;> assumption)
