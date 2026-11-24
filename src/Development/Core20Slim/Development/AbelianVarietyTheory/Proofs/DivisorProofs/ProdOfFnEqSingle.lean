module

public import Mathlib
public import Init.Core
public import Init.Data.Fin.Basic
public import Init.Data.Fin.Lemmas
public import Init.Data.List.Basic
public import Init.Data.List.OfFn
public import Init.Data.Nat.Basic
public import Init.Data.NeZero
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Data.Fin.SuccPred

@[expose] public section

universe u_1

namespace GlobalTheory.ProductOfFnSingle

theorem prod_ofFn_eq_single {M : Type u_1} [inst : Monoid M] {d : ℕ} (g : Fin d → M) (j : Fin d)
    (h : ∀ (i : Fin d), i ≠ j → g i = (1 : M)) : List.prod (List.ofFn g) = g j := by
  induction d with
  | zero => exact j.elim0
  | succ d ih =>
    rw [List.ofFn_succ, List.prod_cons]
    by_cases hj : j = 0
    · subst hj
      have hrest : List.prod (List.ofFn fun i : Fin d => g i.succ) = 1 := by
        apply List.prod_eq_one
        intro x hx
        simp only [List.mem_ofFn] at hx
        obtain ⟨i, rfl⟩ := hx
        exact h _ (Fin.succ_ne_zero i)
      rw [hrest, mul_one]
    · obtain ⟨j', rfl⟩ := Fin.exists_succ_eq.mpr hj
      rw [h 0 (fun e => hj e.symm), one_mul]
      exact ih (fun i => g i.succ) j' (fun i hi => h _ (fun e => hi (Fin.succ_injective _ e)))

end GlobalTheory.ProductOfFnSingle
