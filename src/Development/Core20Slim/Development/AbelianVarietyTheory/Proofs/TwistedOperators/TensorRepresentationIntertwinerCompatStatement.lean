module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.TensorRepresentationIntertwinerCompat
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NonemptyInvFunEquiv
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.MinorOrderedEntries
public import Init.Data.Function
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.RepresentationTheory.Basic

@[expose] public section

open MvPolynomial GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries GlobalTheory.OneFunctional Formalism.BasicNotions GlobalTheory.Branching
open scoped TensorProduct DirectSum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensor_representation_intertwiner_compat : ∀ (Γ A B C D X Y : Type) [Monoid Γ] [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B] [AddCommGroup C] [Module ℂ C] [AddCommGroup D] [Module ℂ D] [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y] (a : Representation ℂ Γ A) (b : Representation ℂ Γ B) (c : Representation ℂ Γ C) (d : Representation ℂ Γ D) (x : Representation ℂ Γ X) (y : Representation ℂ Γ Y) (p : A ⊗[ℂ] C →ₗ[ℂ] X) (q : B ⊗[ℂ] D →ₗ[ℂ] Y), Function.Surjective p → Function.Surjective q → (∀ g u w, p (a g u ⊗ₜ[ℂ] c g w) = x g (p (u ⊗ₜ[ℂ] w))) → (∀ g u w, q (b g u ⊗ₜ[ℂ] d g w) = y g (q (u ⊗ₜ[ℂ] w))) → (∀ l : Module.Dual ℂ (A ⊗[ℂ] C), (∀ g, b g = 1 → d g = 1 → ∀ u w, l (a g u ⊗ₜ[ℂ] c g w) = l (u ⊗ₜ[ℂ] w)) → ∀ z, p z = 0 → l z = 0) → (∀ l : Module.Dual ℂ (B ⊗[ℂ] D), (∀ g, a g = 1 → c g = 1 → ∀ u w, l (b g u ⊗ₜ[ℂ] d g w) = l (u ⊗ₜ[ℂ] w)) → ∀ z, q z = 0 → l z = 0) → Module.finrank ℂ (invFun (a.tprod (b.tprod (c.tprod d)))) = Module.finrank ℂ (invFun (x.tprod y)) := by
  first | exact @GlobalTheory.OneFunctional.finrank_invFun_two_contractions | exact GlobalTheory.OneFunctional.finrank_invFun_two_contractions | (intros; apply GlobalTheory.OneFunctional.finrank_invFun_two_contractions <;> assumption)
