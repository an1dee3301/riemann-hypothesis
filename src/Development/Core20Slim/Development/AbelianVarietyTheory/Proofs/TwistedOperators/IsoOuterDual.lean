module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NonemptyInvFunEquiv
public import Init.Core
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.Multilinear.Basic
public import Mathlib.LinearAlgebra.PiTensorProduct.Basic
public import Mathlib.LinearAlgebra.PiTensorProduct.Dual
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal

@[expose] public section

open MvPolynomial GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries GlobalTheory.OneFunctional Formalism.BasicNotions GlobalTheory.Branching
open scoped TensorProduct DirectSum

namespace GlobalTheory.OneFunctional

theorem iso_outer_dual (ι G : Type) [Fintype ι] [Group G] (V : ι → Type) [∀ τ, AddCommGroup (V τ)]
    [∀ τ, Module ℂ (V τ)] [∀ τ, FiniteDimensional ℂ (V τ)] (ρ : ∀ τ, Representation ℂ G (V τ)) :
    Iso (outer ρ).dual (outer fun τ => (ρ τ).dual) := by
  classical
  refine Iso.symm ⟨PiTensorProduct.dualDistribEquiv, fun g t => ?_⟩
  have hD : ∀ s, (PiTensorProduct.dualDistribEquiv (R := ℂ) (M := V)) s = PiTensorProduct.dualDistrib s :=
    fun _ => rfl
  rw [hD, hD]

  suffices h : PiTensorProduct.dualDistrib ∘ₗ (outer fun τ => (ρ τ).dual) g =
      (outer ρ).dual g ∘ₗ (PiTensorProduct.dualDistrib (R := ℂ) (M := V)) by
    exact LinearMap.congr_fun h t
  refine PiTensorProduct.ext (MultilinearMap.ext fun f => ?_)
  refine PiTensorProduct.ext (MultilinearMap.ext fun m => ?_)
  simp [outer_apply, Representation.dual_apply, PiTensorProduct.map_tprod, Pi.inv_apply,
    Module.Dual.transpose_apply, LinearMap.comp_apply]

end GlobalTheory.OneFunctional
