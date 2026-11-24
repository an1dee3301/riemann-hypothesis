module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Init.Data.Cast
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Algebra.Order.Monoid.Unbundled.ExistsOfLE
public import Mathlib.Algebra.Order.Monoid.Unbundled.Pow
public import Mathlib.Algebra.Order.Ring.Basic
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Cast.Order.Basic
public import Mathlib.Data.Nat.Cast.Order.Ring
public import Mathlib.Data.Nat.Init
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Lattice
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Positivity.Core

@[expose] public section

noncomputable section

open Formalism.BasicNotions

namespace GlobalTheory.ClassCount

def hBd (D : D7) (n : ℕ) : ℝ := (12 * (D.R.f : ℝ) ^ 2 * (n : ℝ) ^ 4 * D.host.rdE ^ 2) ^ (6 * D.R.f * n ^ 2)

theorem hBd_mono {D : D7} {n N : ℕ} (hn : n ≤ N) (h1 : 1 ≤ 12 * (D.R.f : ℝ) ^ 2 * (N : ℝ) ^ 4 * D.host.rdE ^ 2)
    (hrd : 0 ≤ D.host.rdE) : hBd D n ≤ hBd D N := by
  unfold hBd
  have hb : 12 * (D.R.f : ℝ) ^ 2 * (n : ℝ) ^ 4 * D.host.rdE ^ 2 ≤ 12 * (D.R.f : ℝ) ^ 2 * (N : ℝ) ^ 4 * D.host.rdE ^ 2 := by
    have : (n : ℝ) ^ 4 ≤ (N : ℝ) ^ 4 := pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast hn) 4
    gcongr
  calc _ ≤ (12 * (D.R.f : ℝ) ^ 2 * (N : ℝ) ^ 4 * D.host.rdE ^ 2) ^ (6 * D.R.f * n ^ 2) :=
        pow_le_pow_left₀ (by positivity) hb _
    _ ≤ _ := pow_le_pow_right₀ h1 (by gcongr)

end GlobalTheory.ClassCount

end
