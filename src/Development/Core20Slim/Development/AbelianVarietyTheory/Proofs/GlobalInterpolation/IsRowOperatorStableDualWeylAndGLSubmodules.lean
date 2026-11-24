module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.GlobalTwisting.GoodTopBot
public import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.WeylDualWeylLatticesAgreeOfLowestAlcove
public import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RowPolarizationOperatorsRelationsDivPowBaseChangStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RowPolarizationOperatorsActionOnRowWeightStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RowPolarizationMemOfIsGLSchemeSubmoduleStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.WeightedHomogeneousComponentMemOfGLSchemeSubmoduStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.GLSchemeSubmoduleStableUnderRowPermStatement
public import Formalism.GradedWeylDivisibility.StatementA
public import Formalism.LocalRingCardinality.DataCoeff
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Submodule.Basic
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MonoidAlgebra.Module
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.MvPolynomial.Monad
public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Notation.Pi.Basic
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Notation.Support
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

@[expose] public section

open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BasicNotions GlobalTheory.Alc

noncomputable section

namespace GlobalTheory.Alc

theorem rename_rowPerm_eq_rowAct (R : Type) [CommRing R] (r n : ℕ) (σ : Equiv.Perm (Fin r)) :
    (rename (fun v : Fin r × Fin n => (σ v.1, v.2)) : MvPolynomial (Fin r × Fin n) R →ₐ[R] _) =
      rowAct R (n := n) (Matrix.of fun a b : Fin r => if b = σ a then (1 : R) else 0) := by
  apply MvPolynomial.algHom_ext
  intro v
  simp [rowAct]

theorem good_nablaSq (k : Type) [Field k] (N : ℕ) (lam : DomWeight N) : Good (nablaSq k N lam) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a b f hf
    rw [(GlobalTheory.T.rowPolarizationOperators_relations_divPow_baseChange k N N).2.1 a b f]
    exact rowDivStable k N N _ a b 1 f hf
  · intro μ f hf
    exact dualWeylRowGraded k N N _ μ f hf
  · intro σ f hf
    rw [rename_rowPerm_eq_rowAct]
    exact dualWeylRowStable k N N _ _ f hf

theorem good_of_isGLSubmodule (k : Type) [Field k] (N : ℕ) (lam : DomWeight N)
    (M : Submodule k (MvPolynomial (Fin N × Fin N) k)) (hM : GlobalTheory.Published.IsGLSubmodule k N lam M) : Good M := by
  have hw : ∀ μ : Fin N → ℕ, ∀ f ∈ M, weightedHomogeneousComponent (rowW N N) μ f ∈ M :=
    GlobalTheory.T.weightedHomogeneousComponent_mem_of_GLSchemeSubmodule k N lam M hM
  refine ⟨?_, hw, GlobalTheory.T.GLSchemeSubmodule_stable_under_row_perm k N lam M hM⟩
  intro a b f hf
  by_cases hab : a = b
  · subst hab
    classical
    have hsum := sum_weightedHomogeneousComponent (rowW N N) f
    rw [finsum_eq_sum _ (weightedHomogeneousComponent_finsupp f)] at hsum
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← hsum, map_sum]
    refine Submodule.sum_mem _ fun μ _ => ?_
    rw [((GlobalTheory.T.rowPolarizationOperators_action_on_rowWeight k N N μ _ (weightedHomogeneousComponent_isWeightedHomogeneous μ f)).1 a)]
    exact Submodule.smul_mem _ _ (hw μ f hf)
  · exact GlobalTheory.T.rowPolarization_mem_of_isGLSchemeSubmodule k N lam M hM a b hab f hf


end GlobalTheory.Alc
