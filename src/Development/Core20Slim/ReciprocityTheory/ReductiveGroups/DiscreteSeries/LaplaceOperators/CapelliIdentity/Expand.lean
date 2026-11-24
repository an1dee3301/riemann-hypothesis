module

public import Development.Core20Slim.ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.CapelliIdentity.RowCol
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Fin.Basic
public import Init.Data.Fin.Lemmas
public import Init.Data.Function
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.NeZero
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.GroupWithZero.Action
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Algebra.Ring.Commute
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Units
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fin.SuccPred
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.Logic.Equiv.Defs
public import Development.Core20Slim.ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.CapelliIdentity.BasicCycleRangeLastCastSucc
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.CapelliIdentity.CapelliCentralStatement

@[expose] public section

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.Lap.Capelli

open ReciprocityTheory.ChartRestriction.DS

variable {𝒰 : Type*} [Ring 𝒰] [Algebra ℂ 𝒰] {m : ℕ} (E : Fin (m + 1) → Fin (m + 1) → 𝒰)

theorem expand_cons_succAbove_eq (c : Fin (m + 1)) :
    (Fin.cons c c.succAbove : Fin (m + 1) → Fin (m + 1)) = id ∘ ⇑(Fin.cycleRange c).symm := by
  funext j
  refine Fin.cases ?_ (fun j => ?_) j
  · simp [Fin.cycleRange_symm_zero]
  · simp [Fin.cycleRange_symm_succ]

theorem expand_sign_cycleRange_symm (c : Fin (m + 1)) :
    (((Equiv.Perm.sign (Fin.cycleRange c).symm : ℤˣ) : ℤ) : ℂ) = (-1 : ℂ) ^ (c : ℕ) := by
  rw [Equiv.Perm.sign_symm, Fin.sign_cycleRange]
  push_cast
  rfl

theorem expand_cons_not_inj {b c : Fin (m + 1)} (h : b ≠ c) :
    ¬ Function.Injective (Fin.cons b c.succAbove : Fin (m + 1) → Fin (m + 1)) := by
  intro hinj
  obtain ⟨z, hz⟩ := Fin.exists_succAbove_eq h
  have h0 : (Fin.cons b c.succAbove : Fin (m + 1) → Fin (m + 1)) 0 =
      (Fin.cons b c.succAbove : Fin (m + 1) → Fin (m + 1)) z.succ := by
    simp [hz]
  exact Fin.succ_ne_zero z (hinj h0).symm


theorem capelli_expand_minus (hE : GlRelR E) (om : ℂ) (a c : Fin (m + 1)) :
    ∑ d : Fin (m + 1), ((-1 : ℂ) ^ ((d : ℕ) + (c : ℕ))) •
        (capEntry E (om - (m : ℂ)) a d * cminor E c.succAbove d.succAbove om) =
      if a = c then capelliC E om else 0 := by
  have key : cminor E (Fin.cons a c.succAbove : Fin (m + 1) → Fin (m + 1)) id om =
      ∑ d : Fin (m + 1), ((-1 : ℂ) ^ (d : ℕ)) •
        (capEntry E (om - (m : ℂ)) a d * cminor E c.succAbove d.succAbove om) := by
    rw [cminor_succ_row (E := E) hE]
    rfl
  have hsum : ∑ d : Fin (m + 1), ((-1 : ℂ) ^ ((d : ℕ) + (c : ℕ))) •
        (capEntry E (om - (m : ℂ)) a d * cminor E c.succAbove d.succAbove om) =
      ((-1 : ℂ) ^ (c : ℕ)) • ∑ d : Fin (m + 1), ((-1 : ℂ) ^ (d : ℕ)) •
        (capEntry E (om - (m : ℂ)) a d * cminor E c.succAbove d.succAbove om) := by
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [smul_smul, pow_add, mul_comm]
  rw [hsum, ← key]
  by_cases hac : a = c
  · subst hac
    rw [if_pos rfl, expand_cons_succAbove_eq, cminor_perm_rows (E := E),
      ← Int.cast_smul_eq_zsmul ℂ, expand_sign_cycleRange_symm, smul_smul, ← pow_add, ← two_mul,
      pow_mul, neg_one_sq, one_pow, one_smul]
    rfl
  · rw [if_neg hac, cminor_rows_not_inj (E := E) _ _ _ (expand_cons_not_inj hac), smul_zero]

end ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
