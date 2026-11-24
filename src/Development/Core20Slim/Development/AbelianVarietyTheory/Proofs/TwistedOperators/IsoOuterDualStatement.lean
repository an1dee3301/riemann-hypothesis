module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsoOuterDual
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NonemptyInvFunEquiv
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.PiTensorProduct.Basic
public import Mathlib.RepresentationTheory.Basic

@[expose] public section

open MvPolynomial GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries GlobalTheory.OneFunctional Formalism.BasicNotions GlobalTheory.Branching
open scoped TensorProduct DirectSum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iso_dual_outer_outer_dual : ∀ (ι G : Type) [Fintype ι] [Group G] (V : ι → Type) [∀ τ, AddCommGroup (V τ)] [∀ τ, Module ℂ (V τ)] [∀ τ, FiniteDimensional ℂ (V τ)] (ρ : ∀ τ, Representation ℂ G (V τ)), Iso (outer ρ).dual (outer fun τ => (ρ τ).dual) := by
  first | exact @GlobalTheory.OneFunctional.iso_outer_dual | exact GlobalTheory.OneFunctional.iso_outer_dual | (intros; apply GlobalTheory.OneFunctional.iso_outer_dual <;> assumption)
