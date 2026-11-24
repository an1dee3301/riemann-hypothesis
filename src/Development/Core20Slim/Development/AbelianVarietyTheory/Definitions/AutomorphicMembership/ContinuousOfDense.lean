module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.Foundations.IsFockIPOfFockData
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Function
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.NeZero
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Ker
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MonoidAlgebra.Module
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.Notation.Pi.Basic
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Algebra.Order.ZeroLEOne
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Mathlib.Analysis.CStarAlgebra.Module.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Cast.Order.Ring
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Filter.Basic
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.Tactic.CancelDenoms.Core
public import Mathlib.Tactic.Linarith.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Positivity.Core
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.SummationFilter
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.MetricSpace.Algebra
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Neighborhoods
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

namespace GlobalTheory.FockSeq

open MvPolynomial GlobalTheory.FockAlg

variable {σ : Type}

abbrev L2 (σ : Type) : Type := lp (fun _ : σ →₀ ℕ => ℂ) 2

def mfact (α : σ →₀ ℕ) : ℕ := α.prod fun _ k => k.factorial

theorem mfact_pos (α : σ →₀ ℕ) : 0 < mfact α := by
  unfold mfact Finsupp.prod
  exact Finset.prod_pos fun l _ => Nat.factorial_pos (α l)

theorem mfact_cast (α : σ →₀ ℕ) : ((mfact α : ℕ) : ℂ) = α.prod fun _ k => (k.factorial : ℂ) := by
  unfold mfact Finsupp.prod
  push_cast
  rfl

def wt (α : σ →₀ ℕ) : ℂ := (Real.sqrt (mfact α) : ℝ)

theorem wt_ne_zero (α : σ →₀ ℕ) : wt α ≠ 0 := by
  have h : 0 < Real.sqrt (mfact α : ℝ) := Real.sqrt_pos.2 (Nat.cast_pos.2 (mfact_pos α))
  unfold wt
  exact_mod_cast h.ne'

theorem star_wt_mul (α : σ →₀ ℕ) : (starRingEnd ℂ) (wt α) * wt α = (mfact α : ℕ) := by
  have h : Real.sqrt (mfact α : ℝ) * Real.sqrt (mfact α : ℝ) = (mfact α : ℝ) :=
    Real.mul_self_sqrt (Nat.cast_nonneg _)
  unfold wt
  rw [Complex.conj_ofReal, ← Complex.ofReal_mul, h, Complex.ofReal_natCast]

variable [DecidableEq σ]

def emb (σ : Type) [DecidableEq σ] : MvPolynomial σ ℂ →ₗ[ℂ] L2 σ :=
  (basisMonomials σ ℂ).constr ℂ fun α => lp.single 2 α (wt α)

theorem emb_monomial (α : σ →₀ ℕ) (c : ℂ) : emb σ (monomial α c) = lp.single 2 α (c * wt α) := by
  have h : monomial α c = c • basisMonomials σ ℂ α := by
    rw [coe_basisMonomials, smul_monomial, smul_eq_mul, mul_one]
  rw [h, map_smul, emb, Module.Basis.constr_basis, ← smul_eq_mul, lp.single_smul]

theorem emb_apply (f : MvPolynomial σ ℂ) (α : σ →₀ ℕ) : emb σ f α = AddMonoidAlgebra.coeff f α * wt α := by
  induction f using MvPolynomial.induction_on' with
  | monomial β c =>
    rw [emb_monomial, lp.single_apply, coeff_monomial]
    by_cases h : β = α
    · subst h
      simp
    · simp [h]
  | add f g hf hg =>
    rw [map_add (f := _), lp.coeFn_add, Pi.add_apply, hf, hg, MvPolynomial.coeff_add, add_mul]

theorem emb_injective : Function.Injective (emb σ) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro f hf
  ext α
  have h : emb σ f α = 0 := by rw [hf]; rfl
  rw [emb_apply] at h
  simpa [AddMonoidAlgebra.coeff] using (mul_eq_zero.1 h).resolve_right (wt_ne_zero α)

theorem dense_range_emb : Dense (Set.range (emb σ)) := by
  intro x
  have hx := lp.hasSum_single (E := fun _ : σ →₀ ℕ => ℂ) (p := 2) ENNReal.ofNat_ne_top x
  rw [HasSum] at hx
  refine mem_closure_of_tendsto hx (Filter.Eventually.of_forall fun s => ?_)
  refine ⟨∑ α ∈ s, monomial α (x α / wt α), ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [emb_monomial, div_mul_cancel₀ _ (wt_ne_zero α)]

theorem isFockIsometry_embedding : IsFockIP (emb σ) := by
  intro α β
  rw [emb_monomial, emb_monomial, lp.inner_single_left, lp.single_apply, one_mul, one_mul]
  by_cases h : α = β
  · subst h
    rw [Pi.single_eq_same, if_pos rfl, RCLike.inner_apply, mul_comm, star_wt_mul, mfact_cast]
  · rw [Pi.single_eq_of_ne h, if_neg h, inner_zero_right]


omit [DecidableEq σ] in
def diag (c : (σ →₀ ℕ) → ℂ) (hc : ∀ α, ‖c α‖ = 1) : L2 σ →L[ℂ] L2 σ :=
  lp.mapCLM 2 (fun α => c α • ContinuousLinearMap.id ℂ ℂ) zero_le_one fun α => by
    simp [norm_smul, hc]


omit [DecidableEq σ] in
@[simp] theorem diag_apply (c : (σ →₀ ℕ) → ℂ) (hc : ∀ α, ‖c α‖ = 1) (x : L2 σ) (α : σ →₀ ℕ) :
    diag c hc x α = c α * x α := rfl


omit [DecidableEq σ] in


theorem continuous_of_dense {G H : Type*} [TopologicalSpace G] [NormedAddCommGroup H] [NormedSpace ℂ H]
    (π : G → H →L[ℂ] H) (hπ : ∀ g x, ‖π g x‖ = ‖x‖) {S : Set H} (hS : Dense S)
    (h : ∀ x ∈ S, Continuous fun g => π g x) (x : H) : Continuous fun g => π g x := by
  rw [continuous_iff_continuousAt]
  intro g₀
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨y, hyS, hxy⟩ := Metric.mem_closure_iff.1 (hS x) (ε / 3) (by positivity)
  have hy := (h y hyS).continuousAt (x := g₀)
  rw [ContinuousAt, Metric.tendsto_nhds] at hy
  have hd : ∀ g, dist (π g x) (π g y) = dist x y := fun g => by
    rw [dist_eq_norm, dist_eq_norm, ← map_sub, hπ]
  filter_upwards [hy (ε / 3) (by positivity)] with g hg
  have h₁ := hd g
  have h₂ := hd g₀
  rw [dist_comm] at h₂
  calc dist (π g x) (π g₀ x)
      ≤ dist (π g x) (π g y) + dist (π g y) (π g₀ y) + dist (π g₀ y) (π g₀ x) :=
        dist_triangle4 _ _ _ _
    _ < ε := by rw [h₁, h₂]; linarith

end GlobalTheory.FockSeq
