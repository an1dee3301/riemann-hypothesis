module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRtensOp
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaTransformDarbouxModelLinearInjective
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.DarbouxModelAlgebraicVectorsLeAdelicSchwartz
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawWeilFactorization
public import Init.Core
public import Init.Data.Function
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Equiv
public import Mathlib.Algebra.Module.Submodule.Ker
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Module.Submodule.LinearMap
public import Mathlib.Algebra.Module.Submodule.Range
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.Order.Notation

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.TripleAssembly.Transport

theorem exists_factor {V Q P : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup Q] [Module ℂ Q]
    [AddCommGroup P] [Module ℂ P] (T : V →ₗ[ℂ] Q) (S : Submodule ℂ V) (hT : ∀ Φ ∈ S, T Φ = 0 → Φ = 0)
    (pD : V →ₗ[ℂ] P) : ∃ q : Q →ₗ[ℂ] P, ∀ Ψ ∈ S, q (T Ψ) = pD Ψ := by
  have hinj : Function.Injective (T ∘ₗ S.subtype) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    exact Subtype.ext (hT x.1 x.2 hx)
  let eq := LinearEquiv.ofInjective (T ∘ₗ S.subtype) hinj
  obtain ⟨g, hg⟩ := LinearMap.exists_extend ((pD ∘ₗ S.subtype) ∘ₗ eq.symm.toLinearMap)
  refine ⟨g, fun Ψ hΨ => ?_⟩
  have h1 : g (T Ψ) = (g ∘ₗ (LinearMap.range (T ∘ₗ S.subtype)).subtype) (eq ⟨Ψ, hΨ⟩) := rfl
  rw [h1, hg]
  simp

end GlobalTheory.TripleAssembly.Transport

