module

public import Mathlib
public import Formalism.LocalRingCardinality.DataTheta
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.OscActMonomialOfUnique
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsNegBaseY
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoeffPowEqZeroOfDegreeLt
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousOfDense
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Int.Order
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Omega.Coeffs
public import Init.Omega.Constraint
public import Init.Omega.Int
public import Init.Omega.LinearCombo
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MonoidAlgebra.Module
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Derivation
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Notation.Pi.Basic
public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Algebra.Order.Monoid.Canonical.Defs
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.ExistsOfLE
public import Mathlib.Algebra.Order.Sub.Defs
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
public import Mathlib.Data.Finsupp.Order
public import Mathlib.Data.Finsupp.Single
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.NNRat.Defs
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Rat.Init
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Preorder.Finsupp
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH GlobalTheory.Mem.Osc GlobalTheory.OscGauss Matrix
open scoped ComplexOrder

namespace GlobalTheory.OscGauss

section General

variable {σ : Type} [DecidableEq σ] {F : Fock σ} {v : F.H} {E : MvPowerSeries σ ℂ}


omit [DecidableEq σ] in
theorem prod_factorial_add_single (α : σ →₀ ℕ) (l : σ) :
    (α + Finsupp.single l 1).prod (fun _ k => (k.factorial : ℂ)) =
      ((α l : ℂ) + 1) * α.prod (fun _ k => (k.factorial : ℂ)) := by
  classical
  rw [← FockSeq.mfact_cast, ← FockSeq.mfact_cast, Oscillator.mfact_add_single]
  push_cast
  ring

theorem inner_X_mul_monomial (h : HasCoeff F v E) (l : σ) (α : σ →₀ ℕ) :
    inner ℂ (F.ι (MvPolynomial.X l * MvPolynomial.monomial α 1)) v =
      α.prod (fun _ k => (k.factorial : ℂ)) *
        (((α l : ℂ) + 1) * MvPowerSeries.coeff (α + Finsupp.single l 1) E) := by
  rw [MvPolynomial.X, MvPolynomial.monomial_mul, one_mul, add_comm, h, prod_factorial_add_single]
  ring

theorem inner_pderiv_monomial (h : HasCoeff F v E) (m : σ) (α : σ →₀ ℕ) :
    inner ℂ (F.ι (MvPolynomial.pderiv m (MvPolynomial.monomial α 1))) v =
      α.prod (fun _ k => (k.factorial : ℂ)) * MvPowerSeries.coeff α (MvPowerSeries.X m * E) := by
  have e : ∀ (γ : σ →₀ ℕ) (c : ℂ), (MvPolynomial.monomial γ c : MvPolynomial σ ℂ) =
      c • MvPolynomial.monomial γ 1 := fun γ c => by simp [MvPolynomial.smul_monomial]
  rw [MvPolynomial.pderiv_monomial, e, map_smul, inner_smul_left, h, MvPowerSeries.X_def,
    MvPowerSeries.coeff_monomial_mul]
  by_cases h0 : α m = 0
  · have : ¬ Finsupp.single m 1 ≤ α := by rw [Finsupp.single_le_iff, h0]; omega
    simp [h0, this]
  · have hle : Finsupp.single m 1 ≤ α := Finsupp.single_le_iff.2 (Nat.pos_of_ne_zero h0)
    obtain ⟨β, rfl⟩ := exists_add_of_le hle
    rw [if_pos hle, add_tsub_cancel_left, add_comm, prod_factorial_add_single]
    simp
    ring

theorem inner_X_mul_of_deriv {κ : Type} [Fintype κ] (h : HasCoeff F v E) (l : σ) (c : ℂ) (a : κ → ℂ) (m : κ → σ)
    (hE : ∀ α : σ →₀ ℕ, ((α l : ℂ) + 1) * MvPowerSeries.coeff (α + Finsupp.single l 1) E =
      MvPowerSeries.coeff α (((MvPolynomial.C c + ∑ k, MvPolynomial.C (a k) * MvPolynomial.X (m k) :
        MvPolynomial σ ℂ) : MvPowerSeries σ ℂ) * E)) (f : MvPolynomial σ ℂ) :
    inner ℂ (F.ι (MvPolynomial.X l * f)) v =
      c * inner ℂ (F.ι f) v + ∑ k, a k * inner ℂ (F.ι (MvPolynomial.pderiv (m k) f)) v := by
  induction f using MvPolynomial.induction_on' with
  | add f g hf hg =>
    simp only [mul_add, map_add (f := _), inner_add_left, hf, hg, Finset.sum_add_distrib]
    ring
  | monomial α b =>
    have e : (MvPolynomial.monomial α b : MvPolynomial σ ℂ) = b • MvPolynomial.monomial α 1 := by
      simp [MvPolynomial.smul_monomial]
    have e2 : ((MvPolynomial.C c + ∑ k, MvPolynomial.C (a k) * MvPolynomial.X (m k) :
        MvPolynomial σ ℂ) : MvPowerSeries σ ℂ) =
        MvPowerSeries.C c + ∑ k, MvPowerSeries.C (a k) * MvPowerSeries.X (m k) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← MvPolynomial.coeToMvPowerSeries.ringHom_apply, map_add (f := _), map_sum]
      simp
    rw [e, mul_smul_comm]
    simp only [Derivation.map_smul, map_smul, inner_smul_left]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [inner_X_mul_monomial h, inner_pderiv_monomial h, h α, hE, e2, add_mul, Finset.sum_mul, map_add (f := _),
      map_sum, mul_assoc, MvPowerSeries.coeff_C_mul, mul_add, Finset.mul_sum]
    congr 1
    · ring
    · exact Finset.sum_congr rfl fun k _ => by ring

end General

variable {P Q : ℕ}

theorem pderiv_inl_gaussPoly (A : Matrix (Fin P) (Fin Q) ℂ) (x : Ix P Q → ℂ) (i : Fin P) :
    MvPolynomial.pderiv (Sum.inl i) (gaussPoly A x) =
      MvPolynomial.C (x (Sum.inl i)) + ∑ j, MvPolynomial.C (A i j) * MvPolynomial.X (Sum.inr j) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [gaussPoly, map_add (f := _), map_sum, mul_assoc, MvPolynomial.pderiv_mul,
    MvPolynomial.pderiv_X, Pi.single_apply]
  rw [add_comm, Finset.sum_comm]
  simp

theorem pderiv_inr_gaussPoly (A : Matrix (Fin P) (Fin Q) ℂ) (x : Ix P Q → ℂ) (j : Fin Q) :
    MvPolynomial.pderiv (Sum.inr j) (gaussPoly A x) =
      MvPolynomial.C (x (Sum.inr j)) + ∑ i, MvPolynomial.C (A i j) * MvPolynomial.X (Sum.inl i) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [gaussPoly, map_add (f := _), map_sum, mul_assoc, MvPolynomial.pderiv_mul,
    MvPolynomial.pderiv_X, Pi.single_apply]
  rw [add_comm]
  simp

theorem gauss_annihilator (P Q : ℕ) (F : Fock (Ix P Q)) (A : Matrix (Fin P) (Fin Q) ℂ) (x : Ix P Q → ℂ) (v : F.H)
    (h : HasCoeff F v (expPS (gaussPoly A x))) :
    (∀ (i : Fin P) (f : MvPolynomial (Ix P Q) ℂ), inner ℂ (F.ι (MvPolynomial.X (Sum.inl i) * f)) v =
      x (Sum.inl i) * inner ℂ (F.ι f) v + ∑ j, A i j * inner ℂ (F.ι (MvPolynomial.pderiv (Sum.inr j) f)) v) ∧
    (∀ (j : Fin Q) (f : MvPolynomial (Ix P Q) ℂ), inner ℂ (F.ι (MvPolynomial.X (Sum.inr j) * f)) v =
      x (Sum.inr j) * inner ℂ (F.ι f) v + ∑ i, A i j * inner ℂ (F.ι (MvPolynomial.pderiv (Sum.inl i) f)) v) := by
  refine ⟨fun i f => ?_, fun j f => ?_⟩
  · refine inner_X_mul_of_deriv h _ _ (fun j => A i j) (fun j => Sum.inr j) (fun α => ?_) f
    rw [GlobalTheory.OscExpDeriv.coeff_deriv_expPS _ _ (coeff_zero_gaussPoly A x), pderiv_inl_gaussPoly]
  · refine inner_X_mul_of_deriv h _ _ (fun i => A i j) (fun i => Sum.inl i) (fun α => ?_) f
    rw [GlobalTheory.OscExpDeriv.coeff_deriv_expPS _ _ (coeff_zero_gaussPoly A x), pderiv_inr_gaussPoly]

end GlobalTheory.OscGauss

end
