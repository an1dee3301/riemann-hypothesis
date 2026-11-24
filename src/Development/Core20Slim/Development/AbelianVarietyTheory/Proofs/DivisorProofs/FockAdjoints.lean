module

public import Mathlib
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.Foundations.IsFockIPOfFockData
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.LineMatrixKroneckerLeftFactorEqZeroOfIsPC
public import Formalism.LocalRingCardinality.DataTheta
public import Init.ByCases
public import Init.Core
public import Init.Data.Bool
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.IsApply
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.GroupWithZero.Units.Lemmas
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Submodule.LinearMap
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MonoidAlgebra.Module
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Mathlib.Analysis.CStarAlgebra.Module.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

noncomputable section
namespace GlobalTheory.FockAdj
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg GlobalTheory.FockDeg MvPolynomial Matrix

variable {p q r s : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem inner_pderiv {σ : Type} [DecidableEq σ] {ι : MvPolynomial σ ℂ →ₗ[ℂ] H} (hι : IsFockIP ι)
    (i : σ) (P Q : MvPolynomial σ ℂ) :
    inner ℂ (ι (pderiv i P)) (ι Q) = inner ℂ (ι P) (ι (X i * Q)) := by
  rw [← inner_conj_symm, ← inner_X_mul hι, inner_conj_symm]

theorem inner_raiB {ι : Pol p q r s →ₗ[ℂ] H} (hι : IsFockIP ι) (l : Ln p q r s)
    (P Q : Pol p q r s) :
    inner ℂ (ι (raiB l P)) (ι Q) = (if linePos l then 1 else -1) * inner ℂ (ι P) (ι (lowB l Q)) := by
  cases hl : linePos l
  · simp only [raiB, lowB, hl, Bool.false_eq_true, if_false]
    show inner ℂ (ι (-pderiv l P)) (ι Q) = -1 * inner ℂ (ι P) (ι (X l * Q))
    rw [map_neg, inner_neg_left, inner_pderiv hι, neg_one_mul]
  · simp only [raiB, lowB, hl, if_true]
    show inner ℂ (ι (X l * P)) (ι Q) = 1 * inner ℂ (ι P) (ι (pderiv l Q))
    rw [inner_X_mul hι, one_mul]

theorem inner_lowB {ι : Pol p q r s →ₗ[ℂ] H} (hι : IsFockIP ι) (l : Ln p q r s)
    (P Q : Pol p q r s) :
    inner ℂ (ι (lowB l P)) (ι Q) = (if linePos l then 1 else -1) * inner ℂ (ι P) (ι (raiB l Q)) := by
  cases hl : linePos l
  · simp only [raiB, lowB, hl, Bool.false_eq_true, if_false]
    show inner ℂ (ι (X l * P)) (ι Q) = -1 * inner ℂ (ι P) (ι (-pderiv l Q))
    rw [map_neg, inner_neg_right, inner_X_mul hι, neg_one_mul, neg_neg]
  · simp only [raiB, lowB, hl, if_true]
    show inner ℂ (ι (pderiv l P)) (ι Q) = 1 * inner ℂ (ι P) (ι (X l * Q))
    rw [inner_pderiv hι, one_mul]

theorem inner_omE {ι : Pol p q r s →ₗ[ℂ] H} (hι : IsFockIP ι) (l l' : Ln p q r s)
    (P Q : Pol p q r s) :
    inner ℂ (ι (omE l l' P)) (ι Q) =
      (if linePos l = linePos l' then 1 else -1) * inner ℂ (ι P) (ι (omE l' l Q)) := by
  have h1 : inner ℂ (ι (raiB l (lowB l' P))) (ι Q) =
      (if linePos l = linePos l' then 1 else -1) * inner ℂ (ι P) (ι (raiB l' (lowB l Q))) := by
    rw [inner_raiB hι, inner_lowB hι, ← mul_assoc]
    congr 1
    cases linePos l <;> cases linePos l' <;> simp
  unfold omE
  simp only [LinearMap.add_apply, Module.End.mul_apply, map_add (f := _), inner_add_left, inner_add_right,
    mul_add, h1]
  congr 1
  by_cases h : l = l'
  · subst h
    simp [inner_smul_left, inner_smul_right, map_ofNat]
  · simp [h, Ne.symm h]

theorem inner_omAct {ι : Pol p q r s →ₗ[ℂ] H} (hι : IsFockIP ι)
    (M N : Matrix (Ln p q r s) (Ln p q r s) ℂ)
    (h : ∀ l l', N l' l = (if linePos l = linePos l' then 1 else -1) * star (M l l'))
    (P Q : Pol p q r s) :
    inner ℂ (ι (omAct p q r s M P)) (ι Q) = inner ℂ (ι P) (ι (omAct p q r s N Q)) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [omAct_apply, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, sum_inner,
    inner_sum, inner_smul_left, inner_smul_right]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun l' _ => ?_
  rw [inner_omE hι, h, starRingEnd_apply]
  ring



end GlobalTheory.FockAdj
