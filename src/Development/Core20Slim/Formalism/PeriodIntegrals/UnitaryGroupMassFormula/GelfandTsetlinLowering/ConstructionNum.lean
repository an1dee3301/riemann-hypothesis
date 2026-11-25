module

public import Development.Core20Slim.Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.ZScalarVanish
public import Development.Core20Slim.Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinTopCoefficient.NumMore
public import Formalism.LocalRingCardinality.DataCoeff
public import Development.Core20Slim.Formalism.PeriodIntegrals.GTBranch
public import Development.Core20Slim.Formalism.PeriodIntegrals.GTDefs
public import Development.Core20Slim.Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinTopCoefficient.InterlacingDefectEqCard
public import Init.BinderNameHint
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Nat.Lemmas
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Erase
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

noncomputable section

namespace PI.WGL

open Formalism.BasicNotions MvPolynomial

theorem numbers_dominant_large : Numbers := by
  intro n N h lam sg hI
  exact ⟨PI.GTNum.cBr_ne_zero h lam sg hI, PI.GTNum.abs_cBr_le_cBd h lam sg hI,
    PI.GTNum.degZ_eq h lam sg⟩

theorem scalar_vanishing_criterion : ZScalarVanish := by
  intro n N h lam sg mu hsg hmu hne hw
  have hsum : (∑ i : Fin n, mu.w i) = ∑ i : Fin n, sg.w i := by
    unfold wsum at hw
    exact hw
  have hD : D0 h lam mu = D0 h lam sg := by
    unfold D0
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, hsum]
  obtain ⟨i, hi⟩ : ∃ i, mu.w i ≠ sg.w i := by
    by_contra hc
    push_neg at hc
    exact hne (funext hc)
  have hmem : mu.w i ∈ Rset h lam sg i := by
    have hm := PI.GTNum.sg_mem_R h lam mu hmu i
    unfold Rset at hm ⊢
    rw [hD] at hm
    exact hm
  unfold zScalar
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  apply Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hi, hmem⟩)
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  ring

end PI.WGL
