module

public import Mathlib
public import Init.Core
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.ExistsOfLE
public import Mathlib.Algebra.Order.Ring.Basic
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Lattice

@[expose] public section

namespace SupNormSqLeSumNormSq

private lemma entry_le {m n : ℕ} (x : Fin m → Fin n → ℂ) (a : Fin m) (j : Fin n) :
    ‖x a j‖ ≤ Real.sqrt (∑ a : Fin m, ∑ j : Fin n, ‖x a j‖ ^ (2 : ℕ)) := by
  apply Real.le_sqrt_of_sq_le
  calc ‖x a j‖ ^ (2 : ℕ) ≤ ∑ j : Fin n, ‖x a j‖ ^ (2 : ℕ) :=
        Finset.single_le_sum (f := fun j => ‖x a j‖ ^ (2 : ℕ)) (fun _ _ => by positivity)
          (Finset.mem_univ j)
    _ ≤ ∑ a : Fin m, ∑ j : Fin n, ‖x a j‖ ^ (2 : ℕ) :=
        Finset.single_le_sum (f := fun a => ∑ j : Fin n, ‖x a j‖ ^ (2 : ℕ))
          (fun _ _ => by positivity) (Finset.mem_univ a)

end SupNormSqLeSumNormSq

theorem UpperTheory.Reformulated.B.Yhb3.main :
    ∀ {m n : ℕ} (x : Fin m → Fin n → ℂ), ‖x‖ ^ (2 : ℕ) ≤ ∑ a : Fin m, ∑ j : Fin n, ‖x a j‖ ^ (2 : ℕ) := by
  intro m n x
  have hS : 0 ≤ ∑ a : Fin m, ∑ j : Fin n, ‖x a j‖ ^ (2 : ℕ) := by positivity
  have h : ‖x‖ ≤ Real.sqrt (∑ a : Fin m, ∑ j : Fin n, ‖x a j‖ ^ (2 : ℕ)) := by
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun a => ?_
    exact (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun j => SupNormSqLeSumNormSq.entry_le x a j
  calc ‖x‖ ^ (2 : ℕ) ≤ (Real.sqrt (∑ a : Fin m, ∑ j : Fin n, ‖x a j‖ ^ (2 : ℕ))) ^ (2 : ℕ) :=
        pow_le_pow_left₀ (norm_nonneg _) h 2
    _ = _ := Real.sq_sqrt hS
