module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetVecEq
public import Batteries.Logic
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
public import Init.Classical
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Function
public import Init.Data.Int.Basic
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.CharP.IntermediateField
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.BigOperators
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Subsemigroup.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.GroupWithZero.Units.Lemmas
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Polynomial.Monic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Algebra.Torsor.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Complex.BigOperators
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.Real.Star
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Int.Cast.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Int.Cast.Lemmas
public import Mathlib.Data.NNRat.Defs
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Cast.Order.Basic
public import Mathlib.Data.Rat.Defs
public import Mathlib.Data.Rat.Init
public import Mathlib.FieldTheory.AlgebraicClosure
public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Lattice
public import Mathlib.RingTheory.Algebraic.Defs
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Tactic.FieldSimp.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum GlobalTheory.FunObj.StdDatum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

namespace GlobalTheory.ParsevalRootsOfUnity

theorem isIntegral_of_pow_eq_one {R : Type} [CommRing R] (z : R) (m : ℕ) (hm : 0 < m)
    (h : z ^ m = 1) : IsIntegral ℤ z :=
  ⟨Polynomial.X ^ m - Polynomial.C 1, Polynomial.monic_X_pow_sub_C 1 hm.ne', by simp [h]⟩

theorem mem_Qbar_of_pow_eq_one (z : ℂ) (m : ℕ) (hm : 0 < m) (h : z ^ m = 1) : z ∈ Qbar := by
  rw [mem_algebraicClosure_iff]
  exact ((isIntegral_of_pow_eq_one z m hm h).tower_top (A := ℚ)).isAlgebraic

theorem norm_eq_one_of_pow_eq_one' (z : ℂ) (m : ℕ) (hm : 0 < m) (h : z ^ m = 1) : ‖z‖ = 1 :=
  (pow_eq_one_iff_of_nonneg (norm_nonneg z) hm.ne').1 (by rw [← norm_pow, h, norm_one])

theorem exists_integral_coeffs_sum_norm_sq_le_of_rootOfUnity : ∀ {ι Q : Type} [Fintype ι] [Fintype Q] [AddCommGroup Q] (N k : ℕ) (c : ι → ℂ) (χ : ι → AddChar Q ℂ), 0 < N → (∀ i, ∃ m : ℕ, 0 < m ∧ c i ^ m = 1) → Function.Injective χ → Fintype.card Q = N ^ k → Fintype.card ι ≤ N ^ k → ∃ r : Q → Qbar, (∀ q, (r q : ℂ) = ((N : ℂ) ^ k)⁻¹ * ∑ i, c i * χ i q) ∧ (∀ q, IsIntegral ℤ ((N : Qbar) ^ k * r q)) ∧ ∀ ρ : Qbar →+* ℂ, (∑ q, ‖ρ (r q)‖) ^ 2 ≤ (N : ℝ) ^ k := by
  intro ι Q _ _ _ N k c χ hN hc hχ hQ hι
  classical
  choose m hm hcm using hc
  have hQpos : 0 < Fintype.card Q := Fintype.card_pos
  have hχq : ∀ i q, χ i q ^ Fintype.card Q = 1 := fun i q => by
    rw [← AddChar.map_nsmul_eq_pow, card_nsmul_eq_zero, AddChar.map_zero_eq_one]
  let cq : ι → Qbar := fun i => ⟨c i, mem_Qbar_of_pow_eq_one _ _ (hm i) (hcm i)⟩
  let xq : ι → Q → Qbar := fun i q => ⟨χ i q, mem_Qbar_of_pow_eq_one _ _ hQpos (hχq i q)⟩
  have hNQ : (N : Qbar) ≠ 0 := by exact_mod_cast hN.ne'
  let r : Q → Qbar := fun q => ((N : Qbar) ^ k)⁻¹ * ∑ i, cq i * xq i q
  refine ⟨r, ?_, ?_, ?_⟩
  · intro q
    simp [r, cq, xq]
  · intro q
    have : (N : Qbar) ^ k * r q = ∑ i, cq i * xq i q := by
      simp only [r]
      rw [← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hNQ), one_mul]
    rw [this]
    refine IsIntegral.sum _ fun i _ => IsIntegral.mul ?_ ?_
    · exact isIntegral_of_pow_eq_one _ (m i) (hm i) (Subtype.ext (by simpa [cq] using hcm i))
    · exact isIntegral_of_pow_eq_one _ _ hQpos (Subtype.ext (by simpa [xq] using hχq i q))
  · intro ρ
    let χ' : ι → AddChar Q Qbar := fun i =>
      { toFun := xq i
        map_zero_eq_one' := Subtype.ext (by simp [xq])
        map_add_eq_mul' := fun a b => Subtype.ext (by simp [xq, AddChar.map_add_eq_mul]) }
    let ψ : ι → AddChar Q ℂ := fun i => (ρ : Qbar →* ℂ).compAddChar (χ' i)
    have hψ : ∀ i q, ψ i q = ρ (xq i q) := fun i q => rfl
    let a : ι → ℂ := fun i => ρ (cq i)
    have ha : ∀ i, a i * (starRingEnd ℂ) (a i) = 1 := by
      intro i
      have h1 : a i ^ m i = 1 := by
        simp only [a]
        rw [← map_pow]
        have : cq i ^ m i = 1 := Subtype.ext (by simpa [cq] using hcm i)
        rw [this, map_one]
      rw [Complex.mul_conj', norm_eq_one_of_pow_eq_one' _ _ (hm i) h1]
      simp
    have hinj : Function.Injective ψ := by
      intro i j hij
      apply hχ
      ext q
      have h1 : ρ (xq i q) = ρ (xq j q) := by rw [← hψ, ← hψ, hij]
      have h2 := congrArg Subtype.val (ρ.injective h1)
      simpa [xq] using h2
    have horth : ∀ i j, ∑ q, ψ i q * (starRingEnd ℂ) (ψ j q) = if i = j then (Fintype.card Q : ℂ) else 0 := by
      intro i j
      have : ∀ q, ψ i q * (starRingEnd ℂ) (ψ j q) = (ψ i - ψ j) q := fun q => by
        rw [AddChar.sub_apply, AddChar.map_neg_eq_conj]
      simp_rw [this]
      rw [AddChar.sum_eq_ite]
      by_cases h : i = j
      · simp [h]
      · have : ψ i - ψ j ≠ 0 := fun h' => h (hinj (sub_eq_zero.1 h'))
        simp [h, this]
    let f : Q → ℂ := fun q => ∑ i, a i * ψ i q
    have hpars : ∑ q, ‖f q‖ ^ 2 = (Fintype.card Q : ℝ) * Fintype.card ι := by
      apply Complex.ofReal_injective
      push_cast
      simp_rw [← Complex.mul_conj']
      calc ∑ q, f q * (starRingEnd ℂ) (f q)
          = ∑ q, ∑ i, ∑ j, (a i * (starRingEnd ℂ) (a j)) * (ψ i q * (starRingEnd ℂ) (ψ j q)) := by
            refine Finset.sum_congr rfl fun q _ => ?_
            set_option synthInstance.maxHeartbeats 100000 in
              simp only [f, map_sum, map_mul, Finset.sum_mul_sum]
            refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
            ring
        _ = ∑ i, ∑ j, (a i * (starRingEnd ℂ) (a j)) * ∑ q, (ψ i q * (starRingEnd ℂ) (ψ j q)) := by
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [Finset.sum_comm]
            simp [Finset.mul_sum]
        _ = ∑ i, (Fintype.card Q : ℂ) := by
            refine Finset.sum_congr rfl fun i _ => ?_
            simp [horth, ha]
        _ = (Fintype.card Q : ℂ) * Fintype.card ι := by
            simp [mul_comm]
    have hCS : (∑ q, ‖f q‖) ^ 2 ≤ (Fintype.card Q : ℝ) * ∑ q, ‖f q‖ ^ 2 := by
      have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset Q)) (f := fun q => ‖f q‖)
      simpa using this
    have hρr : ∀ q, ‖ρ (r q)‖ = ((N : ℝ) ^ k)⁻¹ * ‖f q‖ := by
      intro q
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [r, map_mul, map_inv₀, map_pow, map_natCast, map_sum, norm_mul, norm_inv,
        norm_pow, Complex.norm_natCast, f, a, hψ]
    simp_rw [hρr]
    rw [← Finset.mul_sum, mul_pow]
    have hNk : (0 : ℝ) < (N : ℝ) ^ k := by positivity
    have hQr : (Fintype.card Q : ℝ) = (N : ℝ) ^ k := by exact_mod_cast hQ
    have hιr : (Fintype.card ι : ℝ) ≤ (N : ℝ) ^ k := by exact_mod_cast hι
    calc (((N : ℝ) ^ k)⁻¹) ^ 2 * (∑ q, ‖f q‖) ^ 2
        ≤ (((N : ℝ) ^ k)⁻¹) ^ 2 * ((Fintype.card Q : ℝ) * ((Fintype.card Q : ℝ) * (Fintype.card ι : ℝ))) := by
          gcongr
          rw [← hpars]; exact hCS
      _ = (Fintype.card ι : ℝ) := by
          rw [hQr]; field_simp
      _ ≤ (N : ℝ) ^ k := hιr

end GlobalTheory.ParsevalRootsOfUnity
