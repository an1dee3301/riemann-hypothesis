module

public import Mathlib
public import Development.Core20Slim.ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModDefs
public import Batteries.Classes.RatCast
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Fin.Basic
public import Init.Data.Function
public import Init.Data.Int.Basic
public import Init.Data.List.Basic
public import Init.Data.List.FinRange
public import Init.Data.Nat.Basic
public import Init.Data.NeZero
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Init.SizeOf
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Even
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Range
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Int.Cast.Lemmas
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Rat.Cast.CharZero
public import Mathlib.Data.Rat.Defs
public import Mathlib.Data.ZMod.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Logic.Function.Defs
public import Mathlib.NumberTheory.Bernoulli
public import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.NumberTheory.ModularForms.Basic
public import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Basic
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Defs
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion
public import Mathlib.NumberTheory.ModularForms.SlashInvariantForms
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.NatFactorial
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.Ring
public import Mathlib.Topology.Algebra.InfiniteSum.SummationFilter
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane Formalism.L2.Th1.CM

namespace ReciprocityTheory.ChartRestriction.L1

def latMap {L : PeriodPair} {c : ℂ} {τ : ℍ} (h : IsTauOf L c τ) (v : Fin 2 → ℤ) : L.lattice :=
  ⟨c * ((v 0 : ℂ) * (τ : ℂ) + (v 1 : ℂ)), (h.2 _).2 ⟨v 0, v 1, rfl⟩⟩

theorem latMap_bijective {L : PeriodPair} {c : ℂ} {τ : ℍ} (h : IsTauOf L c τ) :
    Function.Bijective (latMap h) := by
  constructor
  · intro v w hvw
    have h1 : c * ((v 0 : ℂ) * (τ : ℂ) + (v 1 : ℂ)) = c * ((w 0 : ℂ) * (τ : ℂ) + (w 1 : ℂ)) :=
      congrArg Subtype.val hvw
    have h2 := mul_left_cancel₀ h.1 h1
    have him := congrArg Complex.im h2
    have hre := congrArg Complex.re h2
    simp only [Complex.add_im, Complex.mul_im, Complex.intCast_re, Complex.intCast_im, zero_mul,
      add_zero, Complex.add_re, Complex.mul_re, sub_zero] at him hre
    have hτ : (τ : ℂ).im ≠ 0 := τ.im_ne_zero
    have h0 : (v 0 : ℝ) = w 0 := mul_right_cancel₀ hτ him
    rw [h0] at hre
    have h1' : (v 1 : ℝ) = w 1 := add_left_cancel hre
    funext i
    fin_cases i
    · exact_mod_cast h0
    · exact_mod_cast h1'
  · rintro ⟨x, hx⟩
    obtain ⟨u, v, rfl⟩ := (h.2 x).1 hx
    exact ⟨![u, v], by simp [latMap]⟩

theorem G_eq {L : PeriodPair} {c : ℂ} {τ : ℍ} (h : IsTauOf L c τ) {k : ℕ} (hk : 3 ≤ k) (hk2 : Even k) :
    L.G k = (c ^ k)⁻¹ * (2 * riemannZeta k) * E hk τ := by
  have hE : E hk τ = (1 / 2 : ℂ) * eisensteinSeries (N := 1) 0 k τ := by
    rw [show E hk τ = (1 / 2 : ℂ) • eisensteinSeriesSIF (N := 1) 0 k τ from rfl,
      eisensteinSeriesSIF_apply 0 k τ, smul_eq_mul]
  have H := tsum_eisSummand_eq_riemannZeta_mul_eisensteinSeries hk τ
  have h1 : L.G k = ∑' v : Fin 2 → ℤ, (c ^ k)⁻¹ * eisSummand k v τ := by
    rw [PeriodPair.G, ← (Equiv.ofBijective _ (latMap_bijective h)).tsum_eq]
    refine tsum_congr fun v => ?_
    simp [latMap, eisSummand, mul_pow, mul_comm]
  rw [h1, tsum_mul_left, H, hE]
  ring

theorem sixVal : riemannZeta 6 = (Real.pi : ℂ) ^ 6 / 945 := by
  have h5 : bernoulli' 5 = 0 := by
    rw [bernoulli'_def]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, bernoulli'_zero, bernoulli'_one,
      bernoulli'_two, bernoulli'_three, bernoulli'_four]
    norm_num [Nat.choose]
  have h6 : bernoulli' 6 = 1 / 42 := by
    rw [bernoulli'_def]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, bernoulli'_zero, bernoulli'_one,
      bernoulli'_two, bernoulli'_three, bernoulli'_four, h5]
    norm_num [Nat.choose]
  have hB : bernoulli 6 = 1 / 42 := by
    rw [bernoulli_eq_bernoulli'_of_ne_one (by norm_num), h6]
  have h := riemannZeta_two_mul_nat (k := 3) (by norm_num)
  norm_num [Nat.factorial, hB] at h
  rw [h]
  ring

theorem g₂_eq {L : PeriodPair} {c : ℂ} {τ : ℍ} (h : IsTauOf L c τ) :
    L.g₂ = (c ^ 4)⁻¹ * (4 * (Real.pi : ℂ) ^ 4 / 3) * E₄ τ := by
  rw [PeriodPair.g₂, G_eq h (k := 4) (by norm_num) ⟨2, rfl⟩,
    show ((4 : ℕ) : ℂ) = 4 by norm_num, riemannZeta_four]
  have hE : E (k := 4) (by norm_num) τ = E₄ τ := rfl
  rw [hE]
  ring

theorem g₃_eq {L : PeriodPair} {c : ℂ} {τ : ℍ} (h : IsTauOf L c τ) :
    L.g₃ = (c ^ 6)⁻¹ * (8 * (Real.pi : ℂ) ^ 6 / 27) * E₆ τ := by
  rw [PeriodPair.g₃, G_eq h (k := 6) (by norm_num) ⟨3, rfl⟩,
    show ((6 : ℕ) : ℂ) = 6 by norm_num, sixVal]
  have hE : E (k := 6) (by norm_num) τ = E₆ τ := rfl
  rw [hE]
  ring

end ReciprocityTheory.ChartRestriction.L1
