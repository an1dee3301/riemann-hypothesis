module

public import Development.Core20Slim.ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.CapelliIdentity.ColAnti
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Fin.Basic
public import Init.Data.Fin.Lemmas
public import Init.Data.Int.Basic
public import Init.Data.Int.DivMod.Basic
public import Init.Data.Int.DivMod.Bootstrap
public import Init.Data.Int.Lemmas
public import Init.Data.Int.Order
public import Init.Data.List.Basic
public import Init.Data.List.Lemmas
public import Init.Data.List.OfFn
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.GetElem
public import Init.Omega.Coeffs
public import Init.Omega.Constraint
public import Init.Omega.Int
public import Init.Omega.LinearCombo
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Opposite
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.List.Lemmas
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Group.Equiv.Opposite
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.InjSurj
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Opposite
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Opposites
public import Mathlib.Algebra.Ring.Commute
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Opposite
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Data.Fin.Rev
public import Mathlib.Data.Fin.SuccPred
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Int.Cast.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Int.Order.Units
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Development.Core20Slim.ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.CapelliIdentity.BasicCycleRangeLastCastSucc
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.CapelliIdentity.CapelliCentralStatement

@[expose] public section

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.Lap.Capelli

open ReciprocityTheory.ChartRestriction.DS

variable {𝒰 : Type*} [Ring 𝒰] [Algebra ℂ 𝒰] {n : ℕ} (E : Fin n → Fin n → 𝒰)

theorem shiftedEntry_op (x : ℂ) (a b : Fin n) :
    capEntry (fun a b => MulOpposite.op (E b a)) x a b = MulOpposite.op (capEntry E x b a) := by
  unfold capEntry
  by_cases h : a = b
  · subst h
    simp [MulOpposite.algebraMap_apply]
  · have h' : b ≠ a := Ne.symm h
    simp [h, h']

private theorem list_ofFn_reverse_eq_ofFn_rev {α : Type*} {p : ℕ} (f : Fin p → α) :
    (List.ofFn f).reverse = List.ofFn (fun i => f i.rev) := by
  apply List.ext_getElem (by simp)
  intro k h1 h2
  simp only [List.getElem_reverse, List.getElem_ofFn, List.length_ofFn]
  congr 1
  ext
  simp only [Fin.val_rev]
  try simp only [List.length_reverse, List.length_ofFn] at h1 h2
  omega

theorem columnMinor_op_rev {p : ℕ} (R C : Fin p → Fin n) (x : ℂ) :
    cminor (fun a b => MulOpposite.op (E b a)) (C ∘ Fin.rev) (R ∘ Fin.rev) x =
      MulOpposite.op (rminor E R C x) := by
  have hop : ∀ g : Equiv.Perm (Fin p) → 𝒰,
      MulOpposite.op (∑ σ, g σ) = ∑ σ, MulOpposite.op (g σ) :=
    fun g => map_sum (MulOpposite.opAddEquiv : 𝒰 ≃+ 𝒰ᵐᵒᵖ) g _
  unfold cminor rminor
  rw [hop]
  refine Fintype.sum_equiv (MulAut.conj (Fin.revPerm (n := p))).toEquiv _ _ (fun σ => ?_)
  have hs : Equiv.Perm.sign (Fin.revPerm * σ * (Fin.revPerm (n := p))⁻¹) = Equiv.Perm.sign σ := by
    rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_mul, Equiv.Perm.sign_inv,
      mul_comm (Equiv.Perm.sign (Fin.revPerm (n := p))), mul_assoc, Int.units_mul_self, mul_one]
  have hτ : ∀ j : Fin p, ((Fin.revPerm * σ * (Fin.revPerm (n := p))⁻¹ : Equiv.Perm (Fin p))) (Fin.rev j) = Fin.rev (σ j) := by
    intro j
    have h1 : (Fin.revPerm (n := p))⁻¹ (Fin.rev j) = j := by
      rw [Equiv.Perm.inv_eq_iff_eq, Fin.revPerm_apply]
    simp only [Equiv.Perm.mul_apply, h1, Fin.revPerm_apply]
  simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, MulAut.conj_apply, hs,
    MulOpposite.op_smul]
  congr 1
  rw [MulOpposite.op_list_prod, List.map_ofFn, list_ofFn_reverse_eq_ofFn_rev]
  refine congrArg List.prod (congrArg List.ofFn (funext fun j => ?_))
  simp only [Function.comp_apply, hτ, shiftedEntry_op]
  congr 2
  rw [Fin.val_rev, Nat.cast_sub (by have := j.isLt; omega)]
  push_cast
  ring

theorem rowMinor_eq_unop {p : ℕ} (R C : Fin p → Fin n) (x : ℂ) :
    rminor E R C x = MulOpposite.unop
      (cminor (fun a b => MulOpposite.op (E b a)) (C ∘ Fin.rev) (R ∘ Fin.rev) x) := by
  rw [columnMinor_op_rev, MulOpposite.unop_op]

theorem neg_one_pow_add_rev {p : ℕ} (i j : Fin (p + 1)) :
    (-1 : ℂ) ^ ((j : ℕ) + ((Fin.rev i : Fin (p + 1)) : ℕ)) =
      (-1 : ℂ) ^ ((i : ℕ) + ((Fin.rev j : Fin (p + 1)) : ℕ)) := by
  rw [neg_one_pow_eq_pow_mod_two ((j : ℕ) + ((Fin.rev i : Fin (p + 1)) : ℕ)),
    neg_one_pow_eq_pow_mod_two ((i : ℕ) + ((Fin.rev j : Fin (p + 1)) : ℕ))]
  congr 1
  rw [Fin.val_rev, Fin.val_rev]
  have := i.isLt
  have := j.isLt
  omega

theorem rminor_row_at (hE : GlRelR E) {p : ℕ} (R C : Fin (p + 1) → Fin n) (i : Fin (p + 1)) (x : ℂ) :
    rminor E R C x = ∑ j : Fin (p + 1), ((-1 : ℂ) ^ ((i : ℕ) + (j : ℕ))) •
      (rminor E (R ∘ i.succAbove) (C ∘ j.succAbove) (x - 1) * capEntry E x (R i) (C j)) := by
  have hunop : ∀ g : Fin (p + 1) → 𝒰ᵐᵒᵖ,
      MulOpposite.unop (∑ i, g i) = ∑ i, MulOpposite.unop (g i) :=
    fun g => map_sum (MulOpposite.opAddEquiv : 𝒰 ≃+ 𝒰ᵐᵒᵖ).symm g _
  rw [rowMinor_eq_unop, cminor_col_at (hE := glRelR_op (hE := hE)) _ _ _ (Fin.rev i), hunop]
  refine Fintype.sum_equiv (Fin.revPerm (n := p + 1)) _ _ (fun i' => ?_)
  have e1 : (C ∘ Fin.rev) ∘ i'.succAbove = (C ∘ (Fin.rev i').succAbove) ∘ Fin.rev := by
    funext k
    simp [Fin.rev_succAbove]
  have e2 : (R ∘ Fin.rev) ∘ (Fin.rev i).succAbove = (R ∘ i.succAbove) ∘ Fin.rev := by
    funext k
    simp [Fin.rev_succAbove]
  rw [MulOpposite.unop_smul, MulOpposite.unop_mul, e1, e2, columnMinor_op_rev, MulOpposite.unop_op]
  simp only [Function.comp_apply, shiftedEntry_op, MulOpposite.unop_op, Fin.rev_rev, Fin.revPerm_apply]
  rw [neg_one_pow_add_rev]

end ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
