module

public import Mathlib
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Int.DivMod.Lemmas
public import Init.Data.Nat.Basic
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Pi
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Lattice.Full
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Pi
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Int.Cast.Lemmas
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Rat.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.FieldTheory.Perfect
public import Mathlib.FieldTheory.Separable
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.Algebraic.Defs
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Localization.Integral
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

namespace GlobalTheory.IntSmulMemLatticeTwistedOperators

open NumberField

theorem exists_int_mul_integral {E : Type} [Field E] [NumberField E] (a : E) :
    ∃ d : ℤ, d ≠ 0 ∧ IsIntegral ℤ ((d : E) * a) := by
  obtain ⟨y, hy, hint⟩ := IsAlgebraic.exists_integral_multiple (R := ℤ) ((IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr (Algebra.IsAlgebraic.isAlgebraic a))
  refine ⟨y, hy, ?_⟩
  simpa [zsmul_eq_mul] using hint

theorem exists_int_smul_mem {E : Type} [Field E] [NumberField E] {n : ℕ}
    (L : Submodule (RingOfIntegers E) (Fin n → E)) (hL : Submodule.IsFullLattice E L)
    (v : Fin n → E) : ∃ c : ℤ, c ≠ 0 ∧ c • v ∈ L := by
  have hv : v ∈ Submodule.span E (L : Set (Fin n → E)) := by rw [hL.span_eq_top]; trivial
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨c, hc, hcx⟩ := hx
    obtain ⟨d, hd, hdy⟩ := hy
    refine ⟨c * d, mul_ne_zero hc hd, ?_⟩
    rw [smul_add]
    refine L.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact zsmul_mem hcx d
    · rw [mul_smul]; exact zsmul_mem hdy c
  | smul a x _ hx =>
    obtain ⟨c, hc, hcx⟩ := hx
    obtain ⟨d, hd, hint⟩ := exists_int_mul_integral a
    let b : RingOfIntegers E := ⟨(d : E) * a, hint⟩
    refine ⟨d * c, mul_ne_zero hd hc, ?_⟩
    have key : (d * c) • (a • x) = b • (c • x) := by
      ext i
      simp only [Pi.smul_apply, smul_eq_mul, zsmul_eq_mul, Int.cast_mul]
      rw [Algebra.smul_def]
      have hb : algebraMap (RingOfIntegers E) E b = (d : E) * a := rfl
      rw [hb]
      simp
      ring
    rw [key]
    exact L.smul_mem b hcx

theorem exists_nonzero_int_smul_mem_of_isLattice : ∀ {E : Type} [inst : Field E] [NumberField E] {n : ℕ} (L : Submodule (NumberField.RingOfIntegers E) (Fin n → E)), Submodule.IsFullLattice E L → ∀ (v : Fin n → E), ∃ (c : ℤ), c ≠ (0 : ℤ) ∧ c • v ∈ L :=
  fun L hL v => exists_int_smul_mem L hL v

end GlobalTheory.IntSmulMemLatticeTwistedOperators
