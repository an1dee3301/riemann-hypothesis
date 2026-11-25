module

public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.DerAlong
public import Batteries.Logic
public import Init.Classical
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Function
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.NeZero
public import Init.Data.OfScientific.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Notation.Support
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.Group.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.ExistsOfLE
public import Mathlib.Algebra.Order.Ring.Basic
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.Ring.Unbundled.Basic
public import Mathlib.Algebra.Order.Ring.Unbundled.Rat
public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Algebra.Order.ZeroLEOne
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.ENNReal.Operations
public import Mathlib.Basic.ENNReal.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.Real.Star
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Finset.Insert
public import Mathlib.Data.Finset.Range
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Int.Cast.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.NNRat.Defs
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Cast.Order.Basic
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Rat.Init
public import Mathlib.Data.Set.CoeSort
public import Mathlib.Data.Set.Defs
public import Mathlib.Logic.Function.Defs
public import Mathlib.NumberTheory.ZetaValues
public import Mathlib.Order.Basic
public import Mathlib.Order.CompleteBooleanAlgebra
public import Mathlib.Order.CompleteLattice.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Defs
public import Mathlib.Order.ConditionallyCompletePartialOrder.Defs
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Lattice
public import Mathlib.Order.SetNotation
public import Mathlib.Tactic.CancelDenoms.Core
public import Mathlib.Tactic.FieldSimp.Lemmas
public import Mathlib.Tactic.Linarith.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Positivity.Core
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt
public import Mathlib.Topology.Algebra.InfiniteSum.Ring
public import Mathlib.Topology.Algebra.InfiniteSum.SummationFilter
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Metrizable.Basic
public import Mathlib.Topology.Metrizable.Uniformity
public import Mathlib.Topology.Order.Real
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition GlobalTheory.MixedTerm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
open scoped ENNReal

namespace GlobalTheory.TwBoundFour

def wt (N : ℕ) (c : ℤ) : ℝ≥0∞ := ENNReal.ofReal (1 / (1 + ((c : ℝ) / N) ^ 2))

lemma real_bound (N : ℕ) (hN : 0 < N) (y : ℝ) (hy : 0 < y) :
    1 / (1 + (y / N) ^ 2) ≤ (N:ℝ)^2 * (1 / y^2) := by
  have hN' : (0:ℝ) < N := by exact_mod_cast hN
  rw [div_pow, mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
  field_simp
  nlinarith [sq_nonneg y, sq_nonneg (N:ℝ)]

lemma half_sum_le (N : ℕ) (hN : 0 < N) :
    ∑' m : ℕ, ENNReal.ofReal (1 / (1 + (((m:ℝ) + 1) / N) ^ 2)) ≤ ENNReal.ofReal (2 * (N:ℝ)^2) := by
  have hz : HasSum (fun m : ℕ => (1:ℝ) / ((m:ℝ) + 1) ^ 2) (Real.pi ^ 2 / 6) := by
    have h := (hasSum_nat_add_iff' (f := fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) 1).mpr hasSum_zeta_two
    simpa using h
  have hz2 : HasSum (fun m : ℕ => (N:ℝ)^2 * (1 / ((m:ℝ) + 1) ^ 2)) ((N:ℝ)^2 * (Real.pi ^ 2 / 6)) :=
    hz.mul_left _
  calc ∑' m : ℕ, ENNReal.ofReal (1 / (1 + (((m:ℝ) + 1) / N) ^ 2))
      ≤ ∑' m : ℕ, ENNReal.ofReal ((N:ℝ)^2 * (1 / ((m:ℝ) + 1) ^ 2)) :=
        ENNReal.tsum_le_tsum fun m => ENNReal.ofReal_le_ofReal (real_bound N hN _ (by positivity))
    _ = ENNReal.ofReal ((N:ℝ)^2 * (Real.pi ^ 2 / 6)) := by
        rw [← ENNReal.ofReal_tsum_of_nonneg (fun m => by positivity) hz2.summable, hz2.tsum_eq]
    _ ≤ ENNReal.ofReal (2 * (N:ℝ)^2) := by
        apply ENNReal.ofReal_le_ofReal
        have hp := Real.pi_lt_d2
        have hp0 := Real.pi_pos
        have : Real.pi ^ 2 / 6 ≤ 2 := by nlinarith
        nlinarith [sq_nonneg (N:ℝ)]

lemma int_sum_le (N : ℕ) (hN : 0 < N) :
    ∑' c : ℤ, wt N c ≤ ENNReal.ofReal (5 * (N:ℝ)^2) := by
  rw [tsum_of_add_one_of_neg_add_one ENNReal.summable ENNReal.summable]
  have h1 : ∑' m : ℕ, wt N ((m:ℤ) + 1) ≤ ENNReal.ofReal (2 * (N:ℝ)^2) := by
    refine le_trans (le_of_eq ?_) (half_sum_le N hN)
    congr 1; funext m; simp [wt]
  have h2 : ∑' m : ℕ, wt N (-((m:ℤ) + 1)) ≤ ENNReal.ofReal (2 * (N:ℝ)^2) := by
    refine le_trans (le_of_eq ?_) (half_sum_le N hN)
    congr 1; funext m; unfold wt; congr 1; push_cast; ring
  have h0 : wt N 0 = 1 := by simp [wt]
  have hN1 : (1:ℝ) ≤ (N:ℝ)^2 := by
    have : (1:ℝ) ≤ N := by exact_mod_cast hN
    nlinarith
  calc _ ≤ ENNReal.ofReal (2 * (N:ℝ)^2) + 1 + ENNReal.ofReal (2 * (N:ℝ)^2) := by
        rw [h0]; gcongr
    _ = ENNReal.ofReal (2 * (N:ℝ)^2 + 1 + 2 * (N:ℝ)^2) := by
        rw [ENNReal.ofReal_add (by positivity) (by positivity),
          ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_one]
    _ ≤ ENNReal.ofReal (5 * (N:ℝ)^2) := ENNReal.ofReal_le_ofReal (by linarith)

lemma pi_sum_le (n : ℕ) (f : ℤ → ℝ≥0∞) :
    ∑' c : Fin n → ℤ, ∏ j, f (c j) ≤ (∑' z, f z) ^ n := by
  classical
  rw [ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun s => ?_
  let t : Fin n → Finset ℤ := fun j => s.image (fun x => x j)
  have hs : s ⊆ Fintype.piFinset t := by
    intro x hx
    rw [Fintype.mem_piFinset]
    intro j
    exact Finset.mem_image_of_mem _ hx
  calc ∑ c ∈ s, ∏ j, f (c j) ≤ ∑ c ∈ Fintype.piFinset t, ∏ j, f (c j) :=
        Finset.sum_le_sum_of_subset hs
    _ = ∏ j, ∑ z ∈ t j, f z := (Finset.prod_univ_sum t (fun _ z => f z)).symm
    _ ≤ ∏ _j : Fin n, ∑' z, f z := Finset.prod_le_prod' fun j _ => ENNReal.sum_le_tsum _
    _ = (∑' z, f z) ^ n := by simp

theorem tsum_le {Y : Type} (n N : ℕ) (hN : 0 < N) (a : Y → ENNReal) (T : Fin n → Y → ℝ)
    (hinj : ∀ y y', a y ≠ 0 → a y' ≠ 0 → (∀ j, T j y = T j y') → y = y')
    (hint : ∀ y, a y ≠ 0 → ∀ j, ∃ c : ℤ, (N : ℝ) * T j y = c) (S : ENNReal)
    (hS : ∀ y, a y * ∏ j, ENNReal.ofReal (1 + T j y ^ 2) ≤ S) :
    ∑' y, a y ≤ S * ENNReal.ofReal ((5 * (N : ℝ) ^ 2) ^ n) := by
  classical
  have hN' : (N:ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  let cf : Function.support a → Fin n → ℤ := fun y j => Classical.choose (hint y.1 y.2 j)
  have hcf : ∀ (y : Function.support a) j, (N : ℝ) * T j y.1 = cf y j :=
    fun y j => Classical.choose_spec (hint y.1 y.2 j)
  have hT : ∀ (y : Function.support a) j, T j y.1 = (cf y j : ℝ) / N := fun y j => by
    rw [eq_div_iff hN', mul_comm]; exact hcf y j
  have hcinj : Function.Injective cf := by
    intro y y' h
    apply Subtype.ext
    apply hinj y.1 y'.1 y.2 y'.2
    intro j
    rw [hT y j, hT y' j, h]
  have hbound : ∀ y : Function.support a, a y.1 ≤ S * ∏ j, wt N (cf y j) := by
    intro y
    have hP : (∏ j, ENNReal.ofReal (1 + T j y.1 ^ 2)) * ∏ j, wt N (cf y j) = 1 := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_eq_one fun j _ => ?_
      have hpos : (0:ℝ) < 1 + T j y.1 ^ 2 := by positivity
      rw [wt, ← hT y j, ← ENNReal.ofReal_mul hpos.le, mul_one_div_cancel hpos.ne', ENNReal.ofReal_one]
    calc a y.1 = a y.1 * ((∏ j, ENNReal.ofReal (1 + T j y.1 ^ 2)) * ∏ j, wt N (cf y j)) := by
          rw [hP, mul_one]
      _ = (a y.1 * ∏ j, ENNReal.ofReal (1 + T j y.1 ^ 2)) * ∏ j, wt N (cf y j) := by
          rw [mul_assoc]
      _ ≤ S * ∏ j, wt N (cf y j) := by gcongr; exact hS y.1
  rw [← tsum_subtype_support]
  calc ∑' y : Function.support a, a y.1 ≤ ∑' y : Function.support a, S * ∏ j, wt N (cf y j) :=
        ENNReal.tsum_le_tsum hbound
    _ = S * ∑' y : Function.support a, ∏ j, wt N (cf y j) := ENNReal.tsum_mul_left
    _ ≤ S * ∑' c : Fin n → ℤ, ∏ j, wt N (c j) := by
        gcongr
        exact ENNReal.tsum_comp_le_tsum_of_injective hcinj (fun c => ∏ j, wt N (c j))
    _ ≤ S * (∑' z, wt N z) ^ n := by gcongr; exact pi_sum_le n (wt N)
    _ ≤ S * ENNReal.ofReal (5 * (N:ℝ)^2) ^ n := by gcongr; exact int_sum_le N hN
    _ = S * ENNReal.ofReal ((5 * (N : ℝ) ^ 2) ^ n) := by
        rw [ENNReal.ofReal_pow (by positivity)]

end GlobalTheory.TwBoundFour
