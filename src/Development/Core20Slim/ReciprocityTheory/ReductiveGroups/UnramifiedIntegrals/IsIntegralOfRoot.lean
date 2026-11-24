module

public import Mathlib
public import Development.Core20Slim.ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModDefs
public import Development.Core20Slim.ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModBasic
public import Development.Core20Slim.ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModQPrin
public import Development.Core20Slim.ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModLatTau
public import Development.Core20Slim.ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModJTau
public import Development.Core20Slim.ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModCMPoint
public import Development.Core20Slim.ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModVanish
public import Development.Core20Slim.ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModGmForm
public import Development.Core20Slim.ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModGmQ
public import Formalism.LocalToGlobal.TorsionIntegrality.CMGoodModels.Statement
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Int.DivMod.Basic
public import Init.Data.Int.DivMod.Bootstrap
public import Init.Data.Int.Lemmas
public import Init.Data.Int.Order
public import Init.Data.List.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Nat.Div.Basic
public import Init.Data.Nat.Lemmas
public import Init.Data.NeZero
public import Init.Data.Zero
public import Init.Omega.Coeffs
public import Init.Omega.Constraint
public import Init.Omega.Int
public import Init.Omega.LinearCombo
public import Init.Omega.Logic
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Even
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.Order.Group.Defs
public import Mathlib.Algebra.Order.Group.Int
public import Mathlib.Algebra.Order.Ring.Int
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Int
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import Mathlib.Algebra.Polynomial.Degree.Operations
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Polynomial.Monic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Squarefree.Basic
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.NumberTheory.ModularForms.QExpansion
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Lattice
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.Polynomial.IsIntegral
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.Tactic.Linarith.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

noncomputable section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane Formalism.L2.Th1.CM

namespace ReciprocityTheory.ChartRestriction.L1

theorem isIntegral_of_root {P : Polynomial ℂ} (hP : ∀ i, IsIntegral ℤ (P.coeff i))
    (hu : IsIntegral ℤ (P.leadingCoeff)⁻¹) (h0 : P.leadingCoeff ≠ 0) {x : ℂ} (hx : P.eval x = 0) :
    IsIntegral ℤ x := by
  have hmon : (Polynomial.C (P.leadingCoeff)⁻¹ * P).Monic :=
    Polynomial.monic_C_mul_of_mul_leadingCoeff_eq_one (inv_mul_cancel₀ h0)
  have hdeg : (Polynomial.C (P.leadingCoeff)⁻¹ * P).natDegree ≠ 0 := by
    rw [Polynomial.natDegree_C_mul (inv_ne_zero h0)]
    intro hd
    rw [Polynomial.eq_C_of_natDegree_eq_zero hd, Polynomial.eval_C] at hx
    apply h0
    rw [Polynomial.leadingCoeff, hd]
    exact hx
  refine IsIntegral.of_aeval_monic_of_isIntegral_coeff hmon hdeg ?_ ?_
  · rw [Polynomial.eval_mul, hx, mul_zero]
    exact isIntegral_zero
  · intro i
    rw [Polynomial.coeff_C_mul]
    exact hu.mul (hP i)

theorem jT_isIntegral {m : ℕ} (hm : 0 < m) (hsq : ¬ IsSquare m) {τ : ℍ} (h : Gm m τ = 0) :
    IsIntegral ℤ (jT τ) := by
  obtain ⟨n0, u, hu1, hu2, hu3, hlow, hcoef⟩ := gmQ_low hm hsq
  have hmf : IsMF (12 * ((2 * (Tm m).card : ℕ) : ℤ)) (Gm m) :=
    (gmForm hm).congr_weight (by push_cast; ring)
  obtain ⟨P, hPR, -, hlead, hval⟩ := qPrin_low (Rm m) _ (Gm m) hmf (gmQ_coeffIn hm) n0 u hu3 hlow hcoef
  have h1 := hval τ
  rw [h] at h1
  have h2 : P.eval (jT τ) = 0 := by
    rcases mul_eq_zero.mp h1.symm with h3 | h3
    · exact absurd h3 (pow_ne_zero _ (DD_ne_zero τ))
    · exact h3
  exact isIntegral_of_root (fun i => Rm_isIntegral hm (hPR i)) (by rw [hlead]; exact Rm_isIntegral hm hu2)
    (by rw [hlead]; exact hu3) h2

theorem cm1 : JInvariantIntegrality := by
  intro d L hsf hd4 hL
  obtain ⟨c, τ, hτ⟩ := latTau L
  have hd : 0 < d := by omega
  obtain ⟨A, B, C, D, h1, h2, h3⟩ := cmPoint hd hL hτ (-1) 2
  rw [jInv_eq_jT hτ]
  refine jT_isIntegral hd ?_ (Gm_vanish hd τ A B C D (by linarith) ?_)
  · rintro ⟨r, hr⟩
    have : r % 4 = 0 ∨ r % 4 = 1 ∨ r % 4 = 2 ∨ r % 4 = 3 := by omega
    rcases this with h | h | h | h <;> simp [hr, Nat.mul_mod, h] at hd4
  · rw [← h1, h2]; ring

end ReciprocityTheory.ChartRestriction.L1
