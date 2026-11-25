module

public import Development.Core20Slim.Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.EpsteinZeta.Jacobi
public import Batteries.Logic
public import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.EpsteinZeta.DedekindFactorK
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Ring.CharZero
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.NumberTheory.ModularForms.DedekindEta
public import Mathlib.Order.Basic
public import Mathlib.Tactic.FieldSimp.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5

open NumberField Classical
open scoped Pointwise

lemma conj_mul_im_eq_normSq_mul_div_im (a b : ℂ) (ha : a ≠ 0) :
    ((starRingEnd ℂ) a * b).im = Complex.normSq a * (b / a).im := by
  have hn : Complex.normSq a ≠ 0 := (Complex.normSq_pos.mpr ha).ne'
  rw [Complex.div_im, Complex.mul_im, Complex.conj_re, Complex.conj_im]
  field_simp
  ring

lemma ne_zero_and_div_im_pos (a b : ℂ) (hab : 0 < ((starRingEnd ℂ) a * b).im) :
    a ≠ 0 ∧ 0 < (b / a).im := by
  have ha : a ≠ 0 := by
    rintro rfl
    simp at hab
  refine ⟨ha, ?_⟩
  rw [conj_mul_im_eq_normSq_mul_div_im a b ha] at hab
  exact pos_of_mul_pos_right hab (Complex.normSq_nonneg a)

theorem discr_closure_pair_ne_zero (a b : ℂ) (hab : 0 < ((starRingEnd ℂ) a * b).im) :
    discr (AddSubgroup.closure {a, b}) ≠ 0 := by
  obtain ⟨ha, hpos⟩ := ne_zero_and_div_im_pos a b hab
  rw [discr_closure_pair a b hpos]
  have hpi : (2 * Real.pi / a : ℂ) ≠ 0 := by
    refine div_ne_zero ?_ ha
    exact mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  exact mul_ne_zero (pow_ne_zero _ hpi) (pow_ne_zero _ (ModularForm.eta_ne_zero hpos))

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5
