module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContractsOfIsoDirectSum
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NonemptyInvFunEquiv
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.MinorOrderedEntries
public import Init.Core
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.DirectSum.Basic
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.Order.Notation
public import Mathlib.RepresentationTheory.Basic

@[expose] public section

open MvPolynomial GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries GlobalTheory.OneFunctional Formalism.BasicNotions GlobalTheory.Branching
open scoped TensorProduct DirectSum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.contracts_of_iso_directSum' : ∀ (H G I F V : Type) [Monoid H] [Monoid G] [AddCommGroup F] [Module ℂ F] [AddCommGroup V] [Module ℂ V] (A B : I → Type) [∀ i, AddCommGroup (A i)] [∀ i, Module ℂ (A i)] [∀ i, AddCommGroup (B i)] [∀ i, Module ℂ (B i)] (a : ∀ i, Representation ℂ H (A i)) (b : ∀ i, Representation ℂ G (B i)) (φ : Representation ℂ (H × G) F) (σ : Representation ℂ H V) (i₀ : I), Iso (Representation.directSum fun i => Representation.tprod ((a i).comp (MonoidHom.fst H G)) ((b i).comp (MonoidHom.snd H G))) φ → (∀ i, i ≠ i₀ → invFun ((a i).tprod σ) = ⊥) → Module.finrank ℂ (invFun ((a i₀).tprod σ)) = 1 → Contracts φ σ (b i₀) := by
  first | exact @GlobalTheory.OneFunctional.contracts_of_iso_directSum | exact GlobalTheory.OneFunctional.contracts_of_iso_directSum | (intros; apply GlobalTheory.OneFunctional.contracts_of_iso_directSum <;> assumption)
