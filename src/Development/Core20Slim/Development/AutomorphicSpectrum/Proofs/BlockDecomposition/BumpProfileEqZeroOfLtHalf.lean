module

public import Mathlib
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.UnitTestFunctions.LiftUnit
public import Batteries.Logic
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.StationaryPhaseModel
public import Init.BinderNameHint
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.NeZero
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Pi
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Notation.Pi.Basic
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.Group.Defs
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.Ring.Unbundled.Basic
public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Algebra.Ring.Basic
public import Mathlib.Algebra.Ring.Commute
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Analysis.Calculus.BumpFunction.Basic
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.RCLike.Lemmas
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.Real.Star
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.ENat.Defs
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Cast.Order.Ring
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.Filter.Tendsto
public import Mathlib.Order.Lattice
public import Mathlib.Order.Notation
public import Mathlib.Order.TypeTags
public import Mathlib.Tactic.CancelDenoms.Core
public import Mathlib.Tactic.FieldSimp.Lemmas
public import Mathlib.Tactic.Linarith.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Topology.Algebra.Support
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
public import Mathlib.Topology.MetricSpace.Pseudo.Pi
public import Mathlib.Topology.Order.Basic
public import Mathlib.Topology.Separation.Basic
public import Mathlib.Topology.Separation.CompletelyRegular
public import Mathlib.Topology.Separation.Regular
public import Mathlib.Topology.UniformSpace.Defs
public import Mathlib.Topology.UniformSpace.Uniformizable

@[expose] public section

open PositivityTheory.RgEis PositivityTheory.RgEis.TF

noncomputable section

namespace GlobalTheory.CompanionTheory.TestFun

theorem contDiff_mul_of_vanish {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {N : E → ℝ} (hN : ContDiff ℝ (⊤ : ℕ∞) N) {φ : ℝ → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφ0 : ∀ s, s < 1 / 2 → φ s = 0) {H : E → ℝ}
    (hH : ∀ y, 0 < N y → ContDiffAt ℝ (⊤ : ℕ∞) H y) :
    ContDiff ℝ (⊤ : ℕ∞) (fun y => φ (N y) * H y) := by
  rw [contDiff_iff_contDiffAt]
  intro y
  by_cases hy : 0 < N y
  · exact (hφ.comp hN).contDiffAt.mul (hH y hy)
  · have hlt : N y < 1 / 2 := by linarith [not_lt.mp hy]
    have hev : ∀ᶠ z in nhds y, N z < 1 / 2 :=
      hN.continuous.continuousAt.eventually (gt_mem_nhds hlt)
    refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [hev] with z hz
    simp [hφ0 _ hz]

def sqSum {ι : Type} [Fintype ι] (y : ι → ℝ) : ℝ := ∑ j, y j ^ 2

theorem sqSum_contDiff {ι : Type} [Fintype ι] : ContDiff ℝ (⊤ : ℕ∞) (sqSum (ι := ι)) := by
  unfold sqSum
  exact ContDiff.sum fun j _ => (contDiff_apply ℝ (fun _ => ℝ) j).pow 2

theorem sqSum_smul {ι : Type} [Fintype ι] (t : ℝ) (v : ι → ℝ) :
    sqSum (t • v) = t ^ 2 * sqSum v := by
  unfold sqSum
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by simp [mul_pow]

theorem sq_le_sqSum {ι : Type} [Fintype ι] (y : ι → ℝ) (j : ι) : y j ^ 2 ≤ sqSum y := by
  unfold sqSum
  exact Finset.single_le_sum (f := fun j => y j ^ 2) (fun i _ => sq_nonneg _) (Finset.mem_univ j)

theorem hasCompactSupport_of_sqSum {ι : Type} [Fintype ι] {F : (ι → ℝ) → ℝ}
    (h : ∀ y, 2 < sqSum y → F y = 0) : HasCompactSupport F := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : ι → ℝ) 2) ?_
  intro y hy
  apply h
  have hn : (2 : ℝ) < ‖y‖ := by simpa [mem_closedBall_zero_iff] using hy
  have : ∃ j, 2 < |y j| := by
    by_contra hc
    push Not at hc
    have : ‖y‖ ≤ 2 := (pi_norm_le_iff_of_nonneg (by norm_num)).2 fun j => by
      simpa [Real.norm_eq_abs] using hc j
    linarith
  obtain ⟨j, hj⟩ := this
  have h4 : (2 : ℝ) ^ 2 < y j ^ 2 := by
    rw [← sq_abs (y j)]
    exact pow_lt_pow_left₀ hj (by norm_num) (by norm_num)
  linarith [sq_le_sqSum y j]

def phi0 : ContDiffBump (1 : ℝ) := ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩

theorem bumpProfile_one : phi0 1 = 1 :=
  phi0.one_of_mem_closedBall (by simp [phi0])

theorem bumpProfile_eq_zero_of_lt_half (s : ℝ) (hs : s < 1 / 2) : phi0 s = 0 := by
  refine phi0.zero_of_le_dist ?_
  show (1 / 2 : ℝ) ≤ dist s 1
  rw [Real.dist_eq, abs_sub_comm]
  exact le_trans (by linarith) (le_abs_self _)

theorem bumpProfile_eq_zero_of_two_lt (s : ℝ) (hs : 2 < s) : phi0 s = 0 := by
  refine phi0.zero_of_le_dist ?_
  show (1 / 2 : ℝ) ≤ dist s 1
  rw [Real.dist_eq]
  exact le_trans (by linarith) (le_abs_self _)

theorem bumpProfile_contDiff : ContDiff ℝ (⊤ : ℕ∞) (fun s : ℝ => phi0 s) := phi0.contDiff

def bumpAt (δ : ℝ) (hδ : 0 < δ) : ContDiffBump (1 : ℝ) :=
  ⟨δ / 2, δ, half_pos hδ, half_lt_self hδ⟩

theorem bumpAt_one (δ : ℝ) (hδ : 0 < δ) : bumpAt δ hδ 1 = 1 :=
  (bumpAt δ hδ).one_of_mem_closedBall (by simp [bumpAt]; linarith)

theorem bumpAt_ne (δ : ℝ) (hδ : 0 < δ) {s : ℝ} (h : bumpAt δ hδ s ≠ 0) : 1 - δ < s := by
  by_contra hc
  refine h ((bumpAt δ hδ).zero_of_le_dist ?_)
  show δ ≤ dist s 1
  rw [Real.dist_eq, abs_sub_comm]
  exact le_trans (by linarith [not_lt.mp hc]) (le_abs_self _)

def angular {ι : Type} [Fintype ι] (i₀ : ι) (m : ℕ) (δ : ℝ) (hδ : 0 < δ) (y : ι → ℝ) : ℝ :=
  bumpAt δ hδ (y i₀ ^ 2 / sqSum y) * (y i₀ / Real.sqrt (sqSum y)) ^ m

theorem angular_contDiffAt {ι : Type} [Fintype ι] (i₀ : ι) (m : ℕ) (δ : ℝ) (hδ : 0 < δ)
    (y : ι → ℝ) (hy : 0 < sqSum y) : ContDiffAt ℝ (⊤ : ℕ∞) (angular i₀ m δ hδ) y := by
  have hN : ContDiffAt ℝ (⊤ : ℕ∞) (sqSum (ι := ι)) y := sqSum_contDiff.contDiffAt
  have hc : ContDiffAt ℝ (⊤ : ℕ∞) (fun y : ι → ℝ => y i₀) y := (contDiff_apply ℝ (fun _ => ℝ) i₀).contDiffAt
  have hq : ContDiffAt ℝ (⊤ : ℕ∞) (fun y : ι → ℝ => y i₀ ^ 2 / sqSum y) y :=
    (hc.pow 2).div hN hy.ne'
  have hbc : ContDiff ℝ (⊤ : ℕ∞) (fun s : ℝ => bumpAt δ hδ s) := (bumpAt δ hδ).contDiff
  have hb : ContDiffAt ℝ (⊤ : ℕ∞) (fun y : ι → ℝ => bumpAt δ hδ (y i₀ ^ 2 / sqSum y)) y :=
    ContDiff.comp_contDiffAt (g := fun s : ℝ => bumpAt δ hδ s)
      (f := fun y : ι → ℝ => y i₀ ^ 2 / sqSum y) y hbc hq
  have hs : ContDiffAt ℝ (⊤ : ℕ∞) (fun y : ι → ℝ => Real.sqrt (sqSum y)) y := hN.sqrt hy.ne'
  exact hb.mul ((hc.div hs (Real.sqrt_pos.2 hy).ne').pow m)

def bigF {ι : Type} [Fintype ι] (i₀ : ι) (m : ℕ) (δ : ℝ) (hδ : 0 < δ) (y : ι → ℝ) : ℝ :=
  phi0 (sqSum y) * angular i₀ m δ hδ y

def smallF (m : ℕ) (t : ℝ) : ℝ := phi0 (t ^ 2) * (t / Real.sqrt (t ^ 2)) ^ m

theorem smallF_contDiff (m : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (smallF m) := by
  refine contDiff_mul_of_vanish (N := fun t : ℝ => t ^ 2) (contDiff_id.pow 2) bumpProfile_contDiff
    bumpProfile_eq_zero_of_lt_half (H := fun t => (t / Real.sqrt (t ^ 2)) ^ m) ?_
  intro y hy
  have hN : ContDiffAt ℝ (⊤ : ℕ∞) (fun t : ℝ => t ^ 2) y := (contDiff_id.pow 2).contDiffAt
  exact (contDiffAt_id.div (hN.sqrt hy.ne') (Real.sqrt_pos.2 hy).ne').pow m

theorem smallF_compact (m : ℕ) : HasCompactSupport (smallF m) := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : ℝ) 2) ?_
  intro t ht
  have hn : (2 : ℝ) < |t| := by simpa [mem_closedBall_zero_iff] using ht
  have h4 : (2 : ℝ) ^ 2 < t ^ 2 := by
    rw [← sq_abs t]
    exact pow_lt_pow_left₀ hn (by norm_num) (by norm_num)
  simp [smallF, bumpProfile_eq_zero_of_two_lt (t ^ 2) (by linarith)]

theorem bigF_unit {ι : Type} [Fintype ι] (i₀ : ι) (m : ℕ) (δ : ℝ) (hδ : 0 < δ) (v : ι → ℝ)
    (hv : sqSum v = 1) : bigF i₀ m δ hδ v = bumpAt δ hδ (v i₀ ^ 2) * v i₀ ^ m := by
  simp [bigF, angular, hv, bumpProfile_one]

theorem bigF_smul {ι : Type} [Fintype ι] (i₀ : ι) (m : ℕ) (δ : ℝ) (hδ : 0 < δ) (v : ι → ℝ)
    (hv : sqSum v = 1) (t : ℝ) :
    bigF i₀ m δ hδ (t • v) = smallF m t * bigF i₀ m δ hδ v := by
  rw [bigF_unit i₀ m δ hδ v hv]
  have hN : sqSum (t • v) = t ^ 2 := by rw [sqSum_smul, hv, mul_one]
  by_cases ht : t = 0
  · subst ht
    have h0 : sqSum (0 : ι → ℝ) = 0 := by simp [sqSum]
    simp [bigF, smallF, h0, bumpProfile_eq_zero_of_lt_half 0 (by norm_num)]
  · have ht2 : t ^ 2 ≠ 0 := pow_ne_zero 2 ht
    have hq : (t • v) i₀ ^ 2 / sqSum (t • v) = v i₀ ^ 2 := by
      rw [hN, Pi.smul_apply, smul_eq_mul, mul_pow]
      field_simp
    have hr : (t • v) i₀ / Real.sqrt (sqSum (t • v)) = t / Real.sqrt (t ^ 2) * v i₀ := by
      rw [hN, Pi.smul_apply, smul_eq_mul]
      ring
    simp only [bigF, angular, smallF]
    rw [hq, hr, hN, mul_pow]
    ring

theorem realBump : RealBump := by
  intro ι _ _ i₀ m δ hδ
  have hone : sqSum (Pi.single i₀ (1 : ℝ) : ι → ℝ) = 1 := by
    unfold sqSum
    rw [Finset.sum_eq_single i₀]
    · simp
    · intro j _ hj
      simp [Pi.single_eq_of_ne hj]
    · simp
  refine ⟨bigF i₀ m δ hδ, smallF m, ?_, ?_, smallF_contDiff m, smallF_compact m, ?_, ?_, ?_, ?_, ?_⟩
  · exact contDiff_mul_of_vanish sqSum_contDiff bumpProfile_contDiff bumpProfile_eq_zero_of_lt_half
      (angular_contDiffAt i₀ m δ hδ)
  · refine hasCompactSupport_of_sqSum fun y hy => ?_
    simp [bigF, bumpProfile_eq_zero_of_two_lt _ hy]
  · rw [bigF_unit i₀ m δ hδ _ hone]
    simp [bumpAt_one]
  · simp [smallF, bumpProfile_one]
  · intro t ht
    refine mul_nonneg phi0.nonneg (pow_nonneg (div_nonneg ht (Real.sqrt_nonneg _)) m)
  · intro t
    simp only [smallF, neg_sq, neg_div, neg_pow t]
    ring_nf
  · intro v hv
    have hv' : sqSum v = 1 := hv
    refine ⟨bigF_smul i₀ m δ hδ v hv', ?_, ?_⟩
    · intro h
      rw [bigF_unit i₀ m δ hδ v hv'] at h
      exact bumpAt_ne δ hδ (left_ne_zero_of_mul h)
    · intro h
      rw [bigF_unit i₀ m δ hδ v hv']
      exact mul_nonneg (bumpAt δ hδ).nonneg (pow_nonneg h.le m)

end GlobalTheory.CompanionTheory.TestFun
