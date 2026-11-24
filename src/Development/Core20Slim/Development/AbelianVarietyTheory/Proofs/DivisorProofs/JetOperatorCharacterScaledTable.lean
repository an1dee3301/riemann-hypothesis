module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SubDSharpInDeg
public import Formalism.LocalToGlobal.KernelLattices.ThDistC
public import Formalism.LocalRingCardinality.DataCoeff
public import Formalism.LocalToGlobal.Divisibility.CoefMod
public import Init.Classical
public import Init.Core
public import Init.Data.Prod
public import Init.Data.Sum.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.PropLemmas
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.NonUnitalHom
public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.GroupWithZero.Action
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Nat.Units
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MonoidAlgebra.Module
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.IsEmpty.Defs
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Basic.Unique
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finsupp.Basic
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Finsupp.Weight
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Function
public import Mathlib.Data.Set.Operations
public import Mathlib.Data.Sum.Basic
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

open MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Ker

noncomputable section

namespace GlobalTheory.JetCharScale

variable {K : Type} [Field K]

def scaleVar {σ : Type} (u : σ → K) : MvPolynomial σ K →ₐ[K] MvPolynomial σ K := aeval fun v => C (u v) * X v

theorem scaleVar_monomial {σ : Type} (u : σ → K) (m : σ →₀ ℕ) (c : K) :
    scaleVar u (monomial m c) = (m.prod fun v e => u v ^ e) • monomial m c := by
  rw [scaleVar, aeval_monomial, smul_eq_C_mul, monomial_eq]
  simp only [mul_pow, Finsupp.prod, Finset.prod_mul_distrib, map_prod, map_pow, algebraMap_eq]
  ring

variable {ι : Type} {a b : ℕ}

theorem jetLin_monomial (J : (DVar ι a b →₀ ℕ) → K) (m : (ι × Fin b × Fin b) ⊕ DVar ι a b →₀ ℕ) :
    jetLin J (monomial m 1) = monomial (m.comapDomain Sum.inl Sum.inl_injective.injOn)
      (J (m.comapDomain Sum.inr Sum.inr_injective.injOn)) := by
  have := (basisMonomials ((ι × Fin b × Fin b) ⊕ DVar ι a b) K).constr_basis K (fun m =>
    (monomial (m.comapDomain Sum.inl Sum.inl_injective.injOn) (J (m.comapDomain Sum.inr Sum.inr_injective.injOn)) : Pol K ι b)) m
  rw [coe_basisMonomials] at this
  exact this

theorem subD_scale (w : ι → K) (P : Pol K ι a) :
    scaleVar (Sum.elim (fun _ => 1) fun k => w k.1) (subD K ι a b P) =
      scaleVar (Sum.elim (fun v => w v.1) fun _ => 1) (subD K ι a b P) := by
  refine AlgHom.congr_fun (φ₁ := (scaleVar _).comp (subD K ι a b)) (φ₂ := (scaleVar _).comp (subD K ι a b))
    (MvPolynomial.algHom_ext fun v => ?_) P
  simp only [AlgHom.comp_apply, subD, aeval_X]
  split_ifs with h
  · set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_mul, scaleVar, aeval_X, Sum.elim_inl, Sum.elim_inr, map_one]
    refine Finset.sum_congr rfl fun β _ => ?_
    ring
  · simp

variable [Fintype ι]

theorem jetLin_right (J : (DVar ι a b →₀ ℕ) → K) (w : ι → K) (c : K)
    (Q : MvPolynomial ((ι × Fin b × Fin b) ⊕ DVar ι a b) K) :
    jetLin (fun m => c * ((m.prod fun v e => w v.1 ^ e) * J m)) Q =
      c • jetLin J (scaleVar (Sum.elim (fun _ => 1) fun k => w k.1) Q) := by
  refine LinearMap.congr_fun (g := c • (jetLin J ∘ₗ (scaleVar (Sum.elim (fun _ => 1) fun k => w k.1)).toLinearMap))
    ((basisMonomials _ K).ext fun m => ?_) Q
  rw [coe_basisMonomials]
  simp only [LinearMap.smul_apply, LinearMap.comp_apply, AlgHom.toLinearMap_apply]
  rw [scaleVar_monomial, map_smul, jetLin_monomial, jetLin_monomial, smul_monomial, smul_monomial, smul_eq_mul, smul_eq_mul,
    Finsupp.prod_fintype _ _ (by simp), Finsupp.prod_fintype _ _ (by simp), Fintype.prod_sum_type]
  simp

theorem jetLin_left (J : (DVar ι a b →₀ ℕ) → K) (w : ι → K)
    (Q : MvPolynomial ((ι × Fin b × Fin b) ⊕ DVar ι a b) K) :
    jetLin J (scaleVar (Sum.elim (fun v => w v.1) fun _ => 1) Q) = scaleVar (fun v => w v.1) (jetLin J Q) := by
  induction Q using MvPolynomial.induction_on' with
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | monomial m c =>
    have e : (monomial m c : MvPolynomial _ K) = c • monomial m 1 := by rw [smul_monomial, smul_eq_mul, mul_one]
    rw [e, map_smul, map_smul, map_smul, map_smul, scaleVar_monomial, map_smul, jetLin_monomial, scaleVar_monomial,
      Finsupp.prod_fintype _ _ (by simp), Finsupp.prod_fintype _ _ (by simp), Fintype.prod_sum_type]
    simp

theorem jetMap_scale (J : (DVar ι a b →₀ ℕ) → K) (w : ι → K) (c : K) (n : ι → ℕ) (P : Pol K ι a) :
    jetMap (fun m => c * ((m.prod fun v e => w v.1 ^ e) * J m)) n P = c • scaleVar (fun v => w v.1) (jetMap J n P) := by
  simp only [jetMap, LinearMap.comp_apply, AlgHom.toLinearMap_apply]
  rw [jetLin_right, subD_scale, jetLin_left]

theorem scaleVar_hom [DecidableEq ι] (w : ι → K) (d : ι → ℕ) {Q : Pol K ι b}
    (hQ : ∀ τ, IsWeightedHomogeneous (GlobalTheory.JetDeg.posW b τ) Q (d τ)) :
    scaleVar (fun v => w v.1) Q = (∏ τ, w τ ^ d τ) • Q := by
  conv_lhs => rw [Q.as_sum]
  conv_rhs => rw [Q.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [scaleVar_monomial, Finsupp.prod_fintype _ _ (by simp), Fintype.prod_prod_type]
  congr 1
  refine Finset.prod_congr rfl fun τ _ => ?_
  have h := hQ τ (mem_support_iff.mp hm)
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Fintype.sum_prod_type, Finset.sum_eq_single τ] at h
  · rw [← h]
    simp [GlobalTheory.JetDeg.posW, Finset.prod_pow_eq_pow_sum]
  · intro x _ hx
    simp [GlobalTheory.JetDeg.posW, hx]
  · simp

theorem jetOp_scale : ∀ {ι : Type} [Fintype ι] {a b : ℕ} (lam : ι → DomWeight a) (lam' : ι → DomWeight b) (n : ι → ℕ)
    (J : (Formalism.L2.Ker.DVar ι a b →₀ ℕ) → ℂ) (w : ι → ℂ) (c : ℂ), Formalism.L2.Ker.JetInVV ℂ lam lam' n →
    Formalism.L2.Ker.jetOp lam lam' (fun m => c * ((m.prod fun v e => w v.1 ^ e) * J m)) n =
      (c * ∏ τ, w τ ^ (∑ i, (lam' τ).natW i)) • Formalism.L2.Ker.jetOp lam lam' J n := by
  classical
  intro ι _ a b lam lam' n J w c hV
  refine LinearMap.ext fun P => ?_
  simp only [jetOp, LinearMap.smul_apply, LinearMap.comp_apply, Submodule.subtype_apply]
  rw [jetMap_scale, scaleVar_hom w _ fun τ => GlobalTheory.JetDeg.VV_hom lam' τ (hV J P P.2), smul_smul, map_smul]

end GlobalTheory.JetCharScale

end
