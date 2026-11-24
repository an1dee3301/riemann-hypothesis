module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.NonemptyInvFunDualTprodEquiv
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NonemptyInvFunEquiv
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.MinorOrderedEntries
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.RepresentationTheory.Intertwining

@[expose] public section

open MvPolynomial GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries GlobalTheory.OneFunctional Formalism.BasicNotions GlobalTheory.Branching
open scoped TensorProduct DirectSum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_invFun_dual_tprod_equiv_intertwiningMap : ∀ (G V W : Type) [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) (σ : Representation ℂ G W), Nonempty (invFun (ρ.dual.tprod σ) ≃ₗ[ℂ] σ.IntertwiningMap ρ) := by
  first | exact @GlobalTheory.OneFunctional.nonempty_invFun_dual_tprod_equiv | exact GlobalTheory.OneFunctional.nonempty_invFun_dual_tprod_equiv | (intros; apply GlobalTheory.OneFunctional.nonempty_invFun_dual_tprod_equiv <;> assumption)
