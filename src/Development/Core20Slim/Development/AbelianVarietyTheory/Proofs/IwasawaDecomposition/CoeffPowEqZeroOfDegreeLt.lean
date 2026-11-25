module

public import Mathlib
public import Formalism.LocalRingCardinality.DataTheta
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.OscActMonomialOfUnique
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsNegBaseY
public import Batteries.Logic
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Int.Lemmas
public import Init.Data.Int.Order
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Omega.Coeffs
public import Init.Omega.Constraint
public import Init.Omega.Int
public import Init.Omega.LinearCombo
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MonoidAlgebra.Module
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Order.Antidiag.Prod
public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Range
public import Mathlib.Data.Finsupp.Antidiagonal
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Finsupp.Single
public import Mathlib.Data.Finsupp.Weight
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.Tactic.FieldSimp.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH GlobalTheory.Mem.Osc GlobalTheory.OscGauss Matrix
open scoped ComplexOrder

namespace GlobalTheory.OscExpDeriv

theorem coeff_pow_eq_zero_of_degree_lt {σ : Type} [DecidableEq σ] (q : MvPolynomial σ ℂ)
    (hq : AddMonoidAlgebra.coeff q 0 = 0) (n : ℕ) :
    ∀ γ : σ →₀ ℕ, γ.degree < n → AddMonoidAlgebra.coeff (q ^ n) γ = 0 := by
  induction n with
  | zero => intro γ h; exact absurd h (Nat.not_lt_zero _)
  | succ n ih =>
    intro γ h
    rw [pow_succ, MvPolynomial.coeff_mul]
    refine Finset.sum_eq_zero fun x hx => ?_
    have hx' : x.1 + x.2 = γ := Finset.HasAntidiagonal.mem_antidiagonal.1 hx
    by_cases h2 : x.2 = 0
    · rw [h2, hq, mul_zero]
    · have hd : x.2.degree ≠ 0 := fun h0 => h2 ((Finsupp.degree_eq_zero_iff _).1 h0)
      have hs : x.1.degree + x.2.degree = γ.degree := by rw [← hx', map_add (f := _)]
      rw [ih x.1 (by omega), zero_mul]

theorem coeff_expPS_eq_sum {σ : Type} [DecidableEq σ] (q : MvPolynomial σ ℂ)
    (hq : AddMonoidAlgebra.coeff q 0 = 0) (γ : σ →₀ ℕ) (N : ℕ) (hN : γ.degree < N) :
    MvPowerSeries.coeff γ (expPS q) =
      ∑ n ∈ Finset.range N, AddMonoidAlgebra.coeff (q ^ n) γ / (n.factorial : ℂ) := by
  change ∑ n ∈ Finset.range (γ.degree + 1), AddMonoidAlgebra.coeff (q ^ n) γ / (n.factorial : ℂ) = _
  refine Finset.sum_subset (Finset.range_mono (by omega)) fun n _ hn => ?_
  rw [coeff_pow_eq_zero_of_degree_lt q hq n γ (by simp only [Finset.mem_range] at hn; omega),
    zero_div]

theorem coeff_deriv_expPS : ∀ (σ : Type) [DecidableEq σ] (q : MvPolynomial σ ℂ),
    AddMonoidAlgebra.coeff q 0 = 0 → ∀ (l : σ) (α : σ →₀ ℕ),
      ((α l : ℂ) + 1) * MvPowerSeries.coeff (α + Finsupp.single l 1) (expPS q) =
        MvPowerSeries.coeff α
          (((MvPolynomial.pderiv l q : MvPolynomial σ ℂ) : MvPowerSeries σ ℂ) * expPS q) := by
  intro σ _ q hq l α
  rw [coeff_expPS_eq_sum q hq _ (α.degree + 1 + 1)
    (by rw [map_add (f := _), Finsupp.degree_single]; omega), Finset.mul_sum, MvPowerSeries.coeff_mul]
  have h1 : ∀ n : ℕ, ((α l : ℂ) + 1) *
      (AddMonoidAlgebra.coeff (q ^ n) (α + Finsupp.single l 1) / (n.factorial : ℂ)) =
      AddMonoidAlgebra.coeff (MvPolynomial.pderiv l (q ^ n)) α / (n.factorial : ℂ) := by
    intro n
    rw [MvPolynomial.coeff_pderiv]
    ring
  simp only [h1]
  rw [Finset.sum_range_succ']
  simp only [pow_zero, Derivation.map_one_eq_zero, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply, zero_div, add_zero]
  have h2 : ∀ n : ℕ, AddMonoidAlgebra.coeff (MvPolynomial.pderiv l (q ^ (n + 1))) α /
      (((n + 1).factorial : ℕ) : ℂ) =
      ∑ x ∈ Finset.HasAntidiagonal.antidiagonal α, AddMonoidAlgebra.coeff (MvPolynomial.pderiv l q) x.1 *
        (AddMonoidAlgebra.coeff (q ^ n) x.2 / (n.factorial : ℂ)) := by
    intro n
    have hn : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    have hf : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
    rw [Derivation.leibniz_pow, Nat.add_sub_cancel, smul_eq_mul, mul_comm, MvPolynomial.coeff_smul,
      MvPolynomial.coeff_mul, Nat.factorial_succ, nsmul_eq_mul]
    simp only [← mul_div_assoc]
    rw [← Finset.sum_div]
    push_cast
    field_simp
  simp only [h2]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x hx => ?_
  have hx' : x.1 + x.2 = α := Finset.HasAntidiagonal.mem_antidiagonal.1 hx
  have hs : x.1.degree + x.2.degree = α.degree := by rw [← hx', map_add (f := _)]
  rw [coeff_expPS_eq_sum q hq x.2 (α.degree + 1) (by omega), MvPolynomial.coeff_coe, Finset.mul_sum]

end GlobalTheory.OscExpDeriv
