module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IrreducibleDistinctUnitary
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.FoundationProofs.GenericDetPowMulHw
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.FoundationProofs.NonemptyDirectSumEquivOfFinrankLe
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSemisimpleRepresentationTprodOfIsIrreducibleAl
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LFocksLemmas
public import Formalism.RealPlaceAnalysis.FockPairGl
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.NonUnitalHom
public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.LinearMap
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MonoidAlgebra.Module
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Finsupp.SMul
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

open MvPolynomial Formalism.BasicNotions Formalism.GradedWeylDivisibility GlobalTheory.Branching GlobalTheory.GLDuality
open Formalism.REAL (fockF)
open scoped DirectSum TensorProduct Kronecker Matrix

namespace GlobalTheory.Proof.GenericSubmoduleMonomials

noncomputable def genSub (n n' k : ℕ) : MvPolynomial (Fin n' × Fin k) ℂ →ₐ[ℂ]
    MvPolynomial (Fin n × Fin k) (MvPolynomial (Fin n' × Fin n) ℂ) :=
  aeval (fun v : Fin n' × Fin k => ∑ t : Fin n, C (X (v.1, t)) * X (t, v.2))

theorem map_eval_genSub (n n' k : ℕ) (x : Matrix (Fin n') (Fin n) ℂ) (f : MvPolynomial (Fin n' × Fin k) ℂ) :
    map (eval (fun v : Fin n' × Fin n => x v.1 v.2)) (genSub n n' k f) =
      aeval (fun v : Fin n' × Fin k => ∑ t : Fin n, C (x v.1 t) * (X (t, v.2) : MvPolynomial (Fin n × Fin k) ℂ)) f := by
  induction f using MvPolynomial.induction_on with
  | C a =>
    rw [genSub, aeval_C, aeval_C]
    simp [MvPolynomial.algebraMap_apply]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p v hp =>
    have hv : map (eval (fun v : Fin n' × Fin n => x v.1 v.2)) (genSub n n' k (X v)) =
        ∑ t : Fin n, C (x v.1 t) * (X (t, v.2) : MvPolynomial (Fin n × Fin k) ℂ) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [genSub, aeval_X, map_sum]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [map_mul, map_C, map_X, eval_X]
    rw [map_mul, map_mul, hp, map_mul, hv, aeval_X]

theorem repr_basisMonomials {σ : Type} (φ : MvPolynomial σ ℂ) (m : σ →₀ ℕ) :
    (basisMonomials σ ℂ).repr φ m = AddMonoidAlgebra.coeff φ m := rfl

theorem exists_pairing : ∀ (n n' k : ℕ), ∃ T : MvPolynomial (Fin n × Fin k) ℂ →ₗ[ℂ] MvPolynomial (Fin n' × Fin k) ℂ →ₗ[ℂ] MvPolynomial (Fin n' × Fin n) ℂ, ∀ (φ : MvPolynomial (Fin n × Fin k) ℂ) (f : MvPolynomial (Fin n' × Fin k) ℂ) (x : Matrix (Fin n') (Fin n) ℂ), eval (fun v => x v.1 v.2) (T φ f) = fockF φ (map (starRingEnd ℂ) (aeval (fun v : Fin n' × Fin k => ∑ t : Fin n, C (x v.1 t) * (X (t, v.2) : MvPolynomial (Fin n × Fin k) ℂ)) f)) := by
  intro n n' k
  refine ⟨(basisMonomials (Fin n × Fin k) ℂ).constr ℂ (fun m => ((∏ j ∈ m.support, (m j).factorial : ℕ) : ℂ) •
    (((lcoeff (MvPolynomial (Fin n' × Fin n) ℂ) m).restrictScalars ℂ) ∘ₗ (genSub n n' k).toLinearMap)), ?_⟩
  intro φ f x
  have hs : ((basisMonomials (Fin n × Fin k) ℂ).repr φ).support = φ.support := by
    ext m
    rw [Finsupp.mem_support_iff, repr_basisMonomials, mem_support_iff]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Module.Basis.constr_apply, Finsupp.sum, hs, fockF, LinearMap.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [repr_basisMonomials, ← map_eval_genSub, coeff_map, coeff_map]
  simp only [LinearMap.smul_apply, smul_eval, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
    LinearMap.restrictScalars_apply, lcoeff_apply, starRingEnd_apply, star_star]
  ring

end GlobalTheory.Proof.GenericSubmoduleMonomials
