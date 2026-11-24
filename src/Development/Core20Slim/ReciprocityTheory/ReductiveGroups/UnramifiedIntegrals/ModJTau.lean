module

public import Mathlib
public import Development.Core20Slim.ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModDefs
public import Development.Core20Slim.ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModBasic
public import Development.Core20Slim.ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModGEis
public import Batteries.Logic
public import Formalism.LocalToGlobal.TorsionIntegrality.CMGoodModels.Statement
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.NumberTheory.ModularForms.Basic
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Basic
public import Mathlib.NumberTheory.ModularForms.LevelOne.GradedRing
public import Mathlib.Tactic.FieldSimp.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

noncomputable section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane Formalism.L2.Th1.CM

namespace ReciprocityTheory.ChartRestriction.L1

theorem disc_eq {L : PeriodPair} {c : ℂ} {τ : ℍ} (h : IsTauOf L c τ) :
    L.g₂ ^ 3 - 27 * L.g₃ ^ 2 = (c ^ 12)⁻¹ * (4096 * (Real.pi : ℂ) ^ 12) * DD τ := by
  have hc : c ≠ 0 := h.1
  have hD : DD τ = (E₄ τ ^ 3 - E₆ τ ^ 2) / 1728 := ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq τ
  rw [g₂_eq h, g₃_eq h, hD]
  field_simp
  ring

theorem jInv_eq_jT {L : PeriodPair} {c : ℂ} {τ : ℍ} (h : IsTauOf L c τ) : jInv L = jT τ := by
  have hc : c ≠ 0 := h.1
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hDD : DD τ ≠ 0 := DD_ne_zero τ
  show 1728 * L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) = E₄ τ ^ 3 / DD τ
  rw [disc_eq h, g₂_eq h]
  field_simp
  ring

end ReciprocityTheory.ChartRestriction.L1
