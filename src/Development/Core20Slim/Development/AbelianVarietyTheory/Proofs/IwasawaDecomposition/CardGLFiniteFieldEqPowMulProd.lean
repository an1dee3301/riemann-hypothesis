module

public import Mathlib
public import Formalism.LocalToGlobal.Divisibility.QLocTied
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.HostPins
public import Formalism.DoubleCosetMeasures.LatticeCoset
public import Batteries.Logic
public import Formalism.SharpRestriction.Divisibility.ZetaProductPairs
public import Init.Classical
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Int.Lemmas
public import Init.Data.Int.Order
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Omega.Coeffs
public import Init.Omega.Constraint
public import Init.Omega.Int
public import Init.Omega.LinearCombo
public import Init.Omega.Logic
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Basic.Nontrivial.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Range
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Int.Cast.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Cast.Order.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Tactic.FieldSimp.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

open MeasureTheory Matrix NumberField IsDedekindDomain Formalism.BasicNotions Formalism.DoubleCosetMeasures Formalism.L2.Host Formalism.L2.DIV Formalism.L2.DIV.QLoc GlobalTheory.Mem.HD

namespace GlobalTheory.Mem

theorem card_GL_eq_pow_mul_qE (k : Type) [Field k] [Fintype k] (r : ℕ) :
    (Nat.card (GL (Fin r) k) : ℝ)
      = (Fintype.card k : ℝ) ^ (r * r) * Formalism.MainNotions.ZetaProductPairs.qE (Fintype.card k : ℝ) 1 r := by
  have hq1 : 1 < Fintype.card k := Fintype.one_lt_card
  have hq0 : (Fintype.card k : ℝ) ≠ 0 := by
    have : 0 < Fintype.card k := by omega
    exact_mod_cast this.ne'
  have hconst : (Fintype.card k : ℝ) ^ (r * r)
      = ∏ _j ∈ Finset.Icc 1 r, (Fintype.card k : ℝ) ^ r := by
    rw [Finset.prod_const, Nat.card_Icc, Nat.add_sub_cancel, ← pow_mul]
  rw [Matrix.card_GL_field, Nat.cast_prod,
    Fin.prod_univ_eq_prod_range
      (fun i => ((Fintype.card k ^ r - Fintype.card k ^ i : ℕ) : ℝ)) r,
    hconst, Formalism.MainNotions.ZetaProductPairs.qE, ← Finset.prod_mul_distrib]
  refine Finset.prod_nbij' (fun i => r - i) (fun j => r - j) ?_ ?_ ?_ ?_ ?_
  · intro i hi
    have := Finset.mem_range.mp hi
    exact Finset.mem_Icc.mpr (by omega)
  · intro j hj
    have := Finset.mem_Icc.mp hj
    exact Finset.mem_range.mpr (by omega)
  · intro i hi
    have := Finset.mem_range.mp hi
    show r - (r - i) = i
    omega
  · intro j hj
    have := Finset.mem_Icc.mp hj
    show r - (r - j) = j
    omega
  · intro i hi
    have hir : i < r := Finset.mem_range.mp hi
    have hle : Fintype.card k ^ i ≤ Fintype.card k ^ r :=
      Nat.pow_le_pow_right (by omega) hir.le
    rw [Nat.cast_sub hle, Nat.cast_pow, Nat.cast_pow, mul_sub, mul_one]
    congr 1
    have hcast : (-((r - i : ℕ) : ℤ)) = (i : ℤ) - (r : ℤ) := by
      rw [Nat.cast_sub hir.le]; ring
    rw [hcast, zpow_sub₀ hq0, zpow_natCast, zpow_natCast]
    field_simp

end GlobalTheory.Mem
