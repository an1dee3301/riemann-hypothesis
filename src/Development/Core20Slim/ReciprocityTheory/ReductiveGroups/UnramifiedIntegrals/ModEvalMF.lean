module

public import Mathlib
public import Development.Core20Slim.ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModDefs
public import Development.Core20Slim.ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModBasic
public import Development.Core20Slim.ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModEvalSer
public import Batteries.Logic
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.Ring.Unbundled.Basic
public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Algebra.Order.ZeroLEOne
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Complex.Periodic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.Real.Star
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Cast.Order.Basic
public import Mathlib.Data.Nat.Init
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.Logic.Function.Defs
public import Mathlib.NumberTheory.ModularForms.ArithmeticSubgroups
public import Mathlib.NumberTheory.ModularForms.Basic
public import Mathlib.NumberTheory.ModularForms.Cusps
public import Mathlib.NumberTheory.ModularForms.LevelOne.Basic
public import Mathlib.NumberTheory.ModularForms.QExpansion
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.Tactic.FieldSimp.Lemmas
public import Mathlib.Tactic.Linarith.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Positivity.Core
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.SummationFilter
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane Formalism.L2.Th1.CM

namespace ReciprocityTheory.ChartRestriction.L1

theorem qm_eq_qParam (m : ℕ) (τ : ℍ) : qm m τ = Function.Periodic.qParam (m : ℝ) τ := by
  simp [qm, Function.Periodic.qParam]

theorem qm_norm_lt_one {m : ℕ} (hm : 0 < m) (τ : ℍ) : ‖qm m τ‖ < 1 := by
  rw [qm_eq_qParam]
  exact Function.Periodic.norm_qParam_lt_one (by exact_mod_cast hm) τ.im_pos

theorem qm_surj {m : ℕ} (hm : 0 < m) {x : ℂ} (h0 : 0 < ‖x‖) (h1 : ‖x‖ < 1) : ∃ τ : ℍ, qm m τ = x := by
  have hlog : Real.log ‖x‖ < 0 := Real.log_neg h0 h1
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have him : 0 < (Function.Periodic.invQParam (m : ℝ) x).im := by
    rw [Function.Periodic.im_invQParam]
    refine mul_pos_of_neg_of_neg ?_ hlog
    exact div_neg_of_neg_of_pos (by linarith) (by positivity)
  refine ⟨⟨_, him⟩, ?_⟩
  rw [qm_eq_qParam]
  exact Function.Periodic.qParam_right_inv hmR.ne' (norm_pos_iff.mp h0)

theorem qm_pow {m : ℕ} (hm : 0 < m) (τ : ℍ) : qm m τ ^ m = qm 1 τ := by
  have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  rw [qm, qm, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  field_simp

theorem qm_one_eq (τ : ℍ) : qm 1 τ = Function.Periodic.qParam 1 τ := by
  simpa using qm_eq_qParam 1 τ

theorem qm_pt {a e : ℕ} (ha : 0 < a) (he : 0 < e) (b : ℕ) (τ : ℍ) :
    qm 1 (pt a b e τ) = zetaC e ^ b * qm (a * e) τ ^ (a ^ 2) := by
  have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have he' : (e : ℂ) ≠ 0 := by exact_mod_cast he.ne'
  rw [qm, qm, zetaC, pt_coe ha he, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul,
    ← Complex.exp_add]
  congr 1
  push_cast
  field_simp
  ring

theorem IsMF.hasSum {k : ℤ} {f : ℍ → ℂ} (hf : IsMF k f) (τ : ℍ) :
    HasSum (fun n => PowerSeries.coeff n (qExpansion 1 f) * qm 1 τ ^ n) (f τ) := by
  obtain ⟨g, hg⟩ := hf
  have hgf : (⇑g : ℍ → ℂ) = f := funext hg
  have h := ModularForm.hasSum_qExpansion (f := g) one_pos one_mem_strictPeriods_SL τ
  rw [hgf, ← qm_one_eq] at h
  exact h

theorem IsMF.conv {k : ℤ} {f : ℍ → ℂ} (hf : IsMF k f) : Conv (qExpansion 1 f) := by
  apply conv_of_hasSum
  intro x hx
  by_cases h0 : x = 0
  · subst h0
    exact (hasSum_single 0 fun n hn => by simp [zero_pow hn]).summable
  · obtain ⟨τ, hτ⟩ := qm_surj one_pos (norm_pos_iff.mpr h0) hx
    rw [← hτ]
    exact (hf.hasSum τ).summable

theorem IsMF.ev_eq {k : ℤ} {f : ℍ → ℂ} (hf : IsMF k f) (τ : ℍ) : ev (qExpansion 1 f) (qm 1 τ) = f τ := by
  exact (hf.hasSum τ).tsum_eq

end ReciprocityTheory.ChartRestriction.L1
