module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrictedTensorProductIrreducibleCountableDimen
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRtensOp
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NotForallNonemptyLocP
public import Formalism.SharpRestriction.Divisibility.KudlaSiegelWeil
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Nontrivial.Defs
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Dimension.Basic
public import Mathlib.Logic.Function.Basic
public import Mathlib.Order.Notation
public import Mathlib.SetTheory.Cardinal.Defs
public import Mathlib.SetTheory.Cardinal.Order

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.restrictedTensorProduct_irreducible_countable_dimension : ∀ {ι : Type} [DecidableEq ι] (N : ι → Type) [∀ i, AddCommGroup (N i)] [∀ i, Module ℂ (N i)] (s : ∀ i, N i),
    {i | s i = 0}.Finite → (∀ i, Module.rank ℂ (N i) ≤ Cardinal.aleph0) → (∀ i, Nontrivial (N i)) →
    ∀ Sv : ∀ i, Set (Module.End ℂ (N i)),
    (∀ i, ∀ Q : Submodule ℂ (N i), (∀ a ∈ Sv i, ∀ x ∈ Q, a x ∈ Q) → Q = ⊥ ∨ Q = ⊤) →
    ∀ Op : ∀ i, Module.End ℂ (N i) → Module.End ℂ (GlobalTheory.SmallThetaModules.RTens s),
    (∀ i, ∀ a ∈ Sv i, ∀ ξ, Formalism.MainNotions.KudlaSiegelWeil.Restr s ξ →
      Op i a (GlobalTheory.SmallThetaModules.pureT s ξ) = GlobalTheory.SmallThetaModules.pureT s (Function.update ξ i (a (ξ i)))) →
    ∀ Q : Submodule ℂ (GlobalTheory.SmallThetaModules.RTens s), (∀ i, ∀ a ∈ Sv i, ∀ x ∈ Q, Op i a x ∈ Q) → Q = ⊥ ∨ Q = ⊤ := by
  first | exact @GlobalTheory.rtens_irreducible | exact GlobalTheory.rtens_irreducible | (intros; apply GlobalTheory.rtens_irreducible <;> assumption)
