module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.FunctionalLowerBoundOfConditionsNumeric
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.FpTiedIffExistsLeafFP
public import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
public import Init.Classical
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Order.Lemmas
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.ExistsOfLE
public import Mathlib.Algebra.Order.Ring.Basic
public import Mathlib.Algebra.Order.Ring.Cast
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.Ring.Int
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Cast.Order.Basic
public import Mathlib.Data.Nat.Init
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Lattice
public import Mathlib.Order.RelClasses
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

open Module NumberField IsDedekindDomain
open scoped Matrix nonZeroDivisors

noncomputable section

namespace GlobalTheory.FinitePlacesProbe

open Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.Indef.Tree

variable {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {Df : DefSide Bs}

theorem logArg_nonneg (O : FunData K Df) {b : ℝ} (hb : 1 ≤ b) :
    0 ≤ Real.log (b * O.nr * O.g1 * O.g2 * O.pd * O.pd' * |(O.dE : ℝ)|) := by
  have e : b * O.nr * O.g1 * O.g2 * O.pd * O.pd' * |(O.dE : ℝ)| =
      b * ((O.nr * O.g1 * O.g2 * O.pd * O.pd' * O.dE.natAbs : ℕ) : ℝ) := by
    push_cast [Nat.cast_natAbs]; ring
  rw [e]
  rcases Nat.eq_zero_or_pos (O.nr * O.g1 * O.g2 * O.pd * O.pd' * O.dE.natAbs) with h | h
  · rw [h]; simp
  · exact Real.log_nonneg (one_le_mul_of_one_le_of_one_le hb (by exact_mod_cast h))

theorem sigma_mono_in_constant (O : FunData K Df) {C C' b : ℝ} (h : C ≤ C') (hb : 1 ≤ b) : O.Sig0 C b ≤ O.Sig0 C' b := by
  refine Finset.sum_le_sum fun q _ => mul_le_mul_of_nonneg_right ?_ (Real.log_natCast_nonneg _)
  have : O.ee C b q ≤ O.ee C' b q := by
    unfold FunData.ee
    split_ifs
    · refine Nat.succ_le_succ (Nat.floor_le_floor (div_le_div_of_nonneg_right ?_ (Real.log_natCast_nonneg _)))
      unfold FunData.PPF
      have := logArg_nonneg O hb
      gcongr
    · exact le_rfl
  exact_mod_cast this

end GlobalTheory.FinitePlacesProbe
