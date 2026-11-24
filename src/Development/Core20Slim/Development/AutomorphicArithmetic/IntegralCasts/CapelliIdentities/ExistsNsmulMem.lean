module

public import Mathlib
public import Development.Core20Slim.GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Objects
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Algebra.Order.ZeroLEOne
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Rat.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.Algebraic.Defs
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Localization.Integral

@[expose] public section

theorem UpperTheory.Reformulated.B.ExistsNsmulMem.exists_nsmul_mem.{u_1, u_2} :
    ∀ {E : Type u_1} {W : Type u_2} [inst : Field E] [NumberField E] [inst_2 : AddCommGroup W]
    [inst_3 : _root_.Module E W] {La : AddSubgroup W},
    GroundTheory.Heights₂.Heights.FiniteCovolume.IsLattice (E := E) La →
      ∀ (w : W),
        ∃ (d : ℕ),
          (0 : ℕ) < d ∧
            d • w ∈ La := by
  intro E W _ _ _ _ La hL w
  induction (hL.span_eq_top ▸ Submodule.mem_top : w ∈ Submodule.span E (La : Set W))
    using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_pos, by simpa using hx⟩
  | zero => exact ⟨1, one_pos, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨⟨d, hd, hx⟩, ⟨e, he, hy⟩⟩ := And.intro hx hy
    refine ⟨d * e, mul_pos hd he, smul_add (d * e) x y ▸ La.add_mem ?_ ?_⟩
    exacts [mul_comm e d ▸ mul_smul e d x ▸ La.nsmul_mem hx e, mul_smul d e y ▸ La.nsmul_mem hy d]
  | smul a x _ hx =>
    obtain ⟨⟨d, hd, hx⟩, n, s, hn, hs⟩ := And.intro hx (((IsFractionRing.isAlgebraic_iff ℤ ℚ E).2
      (.of_finite ℚ a)).exists_nsmul_eq (NumberField.RingOfIntegers E))
    refine ⟨n * d, mul_pos (Nat.pos_of_ne_zero hn) hd, ?_⟩
    rw [mul_smul, smul_comm d a x, ← smul_assoc, hs]; exact hL.smul_mem s _ hx
