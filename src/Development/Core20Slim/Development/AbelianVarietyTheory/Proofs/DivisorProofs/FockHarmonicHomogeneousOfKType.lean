module

public import Mathlib
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.Foundations.IsFockIPOfFockData
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousOfDense
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.AbsSubOfDisjoint
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.PderivEqZeroOfColOp
public import Formalism.LocalRingCardinality.DataTheta
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Prod
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Prod.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.Logic.Function.Defs
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic

@[expose] public section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial

namespace GlobalTheory.FockAlg


open GlobalTheory.JointHarm GlobalTheory.FockSeq in
theorem harmonic_homog_of_type : ∀ (p q r s : ℕ),
    (∀ (μ : Ix p q → ℚ) (P : Pol p q r s), P ≠ 0 → OfType (fockAct1 p q r s) μ P →
      P ∈ harm1 p q r s →
      ∃ d : ℕ, (d : ℚ) = degW (cPair r s) μ ∧ P ∈ homog (Ix p q × Ix r s) d) ∧
    (∀ (μ : Ix r s → ℚ) (P : Pol p q r s), P ≠ 0 → OfType (fockAct2 p q r s) μ P →
      P ∈ harm2 p q r s →
      ∃ d : ℕ, (d : ℚ) = degW (cPair p q) μ ∧ P ∈ homog (Ix p q × Ix r s) d) :=
  fun _ _ _ _ =>
    ⟨fun _ P h0 ht hh => isSide_one.homog_of_type isFockIsometry_embedding emb_injective
        Function.bijective_id h0 ht ((mem_harm1 P).1 hh),
      fun _ P h0 ht hh => isSide_two.homog_of_type isFockIsometry_embedding emb_injective
        Prod.swap_bijective h0 ht ((mem_harm2 P).1 hh)⟩

end GlobalTheory.FockAlg
