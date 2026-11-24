module

public import Development.Core20Slim.Formalism.PeriodIntegrals.CubicExponentialFactor
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Int.Lemmas
public import Init.Data.Int.Order
public import Init.Data.Nat.Basic
public import Init.Data.Order.Lemmas
public import Init.Data.Zero
public import Init.Omega.Coeffs
public import Init.Omega.Constraint
public import Init.Omega.Int
public import Init.Omega.LinearCombo
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Order.Antidiag.Prod
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.Algebra.Order.ZeroLEOne
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Instances
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Group.Completion
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.Analysis.Normed.Module.Completion
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Logic.Basic
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Empty
public import Mathlib.Data.Finset.Insert
public import Mathlib.Data.Finset.NatAntidiagonal
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.RelClasses
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.GroupCompletion
public import Mathlib.Topology.Algebra.UniformField
public import Mathlib.Topology.Algebra.UniformRing
public import Mathlib.Topology.Algebra.Valued.ValuationTopology
public import Mathlib.Topology.Algebra.Valued.ValuedField
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

namespace PI.CubicExponentialFactor.Wk

open PI.CubicExponentialFactor

variable {p : ℕ} [Fact p.Prime]

theorem norm_add_le_one {x y : ℂ_[p]} (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) : ‖x + y‖ ≤ 1 :=
  (IsUltrametricDist.norm_add_le_max x y).trans (max_le hx hy)

theorem trunc_mul {f g : PowerSeries ℂ_[p]} {k : ℕ} (hf : ∀ j < k, ‖PowerSeries.coeff j f‖ ≤ 1)
    (hg : ∀ j < k, ‖PowerSeries.coeff j g‖ ≤ 1) : ∀ j < k, ‖PowerSeries.coeff j (f * g)‖ ≤ 1 := by
  classical
  intro j hj
  rw [PowerSeries.coeff_mul]
  have key : ∀ s : Finset (ℕ × ℕ), (∀ q ∈ s, q.1 + q.2 = j) →
      ‖∑ q ∈ s, PowerSeries.coeff q.1 f * PowerSeries.coeff q.2 g‖ ≤ 1 := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro _; simp
    | insert q s hq ih =>
      intro hs
      rw [Finset.sum_insert hq]
      have hq' := hs q (Finset.mem_insert_self q s)
      refine norm_add_le_one ?_ (ih fun q' h' => hs q' (Finset.mem_insert_of_mem h'))
      rw [norm_mul]
      exact mul_le_one₀ (hf _ (by omega)) (norm_nonneg _) (hg _ (by omega))
  exact key _ (fun q h => by simpa using h)

theorem term_int {a : ℂ_[p]} (ha : ‖a‖ ≤ 1) {m k : ℕ} (hm : 1 ≤ m) {F : PowerSeries ℂ_[p]}
    (hF : ∀ j < k, ‖PowerSeries.coeff j F‖ ≤ 1) :
    ‖PowerSeries.coeff k (algebraMap ℂ_[p] (PowerSeries ℂ_[p]) a * PowerSeries.X ^ m * F)‖ ≤ 1 := by
  rw [mul_assoc, ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm (PowerSeries.X ^ m) F,
    PowerSeries.coeff_mul_X_pow']
  split_ifs with h
  · rw [norm_mul]
    exact mul_le_one₀ ha (norm_nonneg _) (hF _ (by omega))
  · simp

theorem term_int1 {a : ℂ_[p]} (ha : ‖a‖ ≤ 1) {k : ℕ} {F : PowerSeries ℂ_[p]}
    (hF : ∀ j < k, ‖PowerSeries.coeff j F‖ ≤ 1) :
    ‖PowerSeries.coeff k (algebraMap ℂ_[p] (PowerSeries ℂ_[p]) a * PowerSeries.X * F)‖ ≤ 1 := by
  have h := term_int ha (m := 1) le_rfl hF
  rwa [pow_one] at h

theorem wq_int {W : WeierstrassCurve ℂ_[p]} {wq : PowerSeries ℂ_[p]} (ha1 : IsIntP W.a₁)
    (ha2 : IsIntP W.a₂) (ha3 : IsIntP W.a₃) (ha4 : IsIntP W.a₄) (ha6 : IsIntP W.a₆)
    (hW : IsWq W wq) : ∀ k, ‖PowerSeries.coeff k wq‖ ≤ 1 := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    have h2 : ∀ j < k, ‖PowerSeries.coeff j (wq ^ 2)‖ ≤ 1 := by
      rw [pow_two]
      exact trunc_mul ih ih
    have h3 : ∀ j < k, ‖PowerSeries.coeff j (wq ^ 3)‖ ≤ 1 := by
      have e : wq ^ 3 = wq ^ 2 * wq := by ring
      rw [e]
      exact trunc_mul h2 ih
    dsimp only [IsWq] at hW
    rw [hW]
    simp only [map_add (f := _)]
    refine norm_add_le_one (norm_add_le_one (norm_add_le_one (norm_add_le_one
      (norm_add_le_one ?_ ?_) ?_) ?_) ?_) ?_
    · rw [PowerSeries.coeff_one]
      split_ifs <;> simp
    · exact term_int1 ha1 ih
    · exact term_int ha2 (by norm_num) ih
    · exact term_int ha3 (by norm_num) h2
    · exact term_int ha4 (by norm_num) h2
    · exact term_int ha6 (by norm_num) h3

end PI.CubicExponentialFactor.Wk

end
