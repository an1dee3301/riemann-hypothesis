module

public import Mathlib
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Logic.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Cast.Order.Basic
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.ZMod.Defs
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Filter.Defs
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.Topology.Algebra.Group.Neighborhood
public import Mathlib.Topology.Algebra.Nonarchimedean.Basic
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Instances.ZMod
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

theorem UpperTheory.Reformulated.B.Yde3.continuous_toZModPow :
    ∀ {ℓ : ℕ} [hℓ : Fact (Nat.Prime ℓ)] (n : ℕ), Continuous (⇑(PadicInt.toZModPow n) : ℤ_[ℓ] → ZMod (ℓ ^ n)) := by
  intro ℓ hℓ n
  refine continuous_of_continuousAt_zero (PadicInt.toZModPow (p := ℓ) n) ?_
  have hpos : (0 : ℝ) < (ℓ : ℝ) ^ (-n : ℤ) :=
    zpow_pos (by exact_mod_cast hℓ.out.pos) _
  refine (continuousAt_const (y := (0 : ZMod (ℓ ^ n)))).congr ?_
  filter_upwards [Metric.closedBall_mem_nhds (0 : ℤ_[ℓ]) hpos] with x hx
  rw [mem_closedBall_zero_iff, PadicInt.norm_le_pow_iff_mem_span_pow,
    ← PadicInt.ker_toZModPow, RingHom.mem_ker] at hx
  exact hx.symm
