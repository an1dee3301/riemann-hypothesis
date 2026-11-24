module

public import Mathlib
public import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds
public import Formalism.RealPlaceAnalysis.StatementA
public import Formalism.RealPlaceAnalysis.StatementB
public import Init.ByCases
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Fin.Basic
public import Init.Data.Int.Basic
public import Init.Data.Int.Lemmas
public import Init.Data.Int.Order
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Omega.Coeffs
public import Init.Omega.Constraint
public import Init.Omega.Int
public import Init.Omega.LinearCombo
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.BigOperators
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Module.Submodule.LinearMap
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.Order.Basic
public import Mathlib.Order.BoundedOrder.Basic
public import Mathlib.Order.CompleteLattice.Defs
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Defs
public import Mathlib.Order.ConditionallyCompletePartialOrder.Defs
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Disjoint
public import Mathlib.Order.Fin.Basic
public import Mathlib.Order.SetNotation
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

open Formalism.REAL

namespace GlobalTheory

inductive LoweringWord {V : Type} [AddCommGroup V] [Module ℂ V] {n : ℕ}
    (E : Fin n → Fin n → Module.End ℂ V) (v : V) : ℕ → V → Prop
  | base : LoweringWord E v 0 v
  | step {N : ℕ} {x : V} (a b : Fin n) (h : b < a) :
      LoweringWord E v N x → LoweringWord E v (N + (a.val - b.val)) (E a b x)

section
variable {V : Type} [AddCommGroup V] [Module ℂ V] {n : ℕ}
  {E : Fin n → Fin n → Module.End ℂ V} {ν : Fin n → ℂ} {v : V}

theorem glRel_apply_comm (hE : GlRel E) (a b c d : Fin n) (y : V) :
    E a b (E c d y) = E c d (E a b y) + (if b = c then E a d y else 0)
      - (if d = a then E c b y else 0) := by
  have h := congrArg (fun f : Module.End ℂ V => f y) (hE a b c d)
  simp only [LinearMap.sub_apply, Module.End.mul_apply] at h
  have h1 : (if b = c then E a d else 0) y = if b = c then E a d y else 0 := by
    split_ifs <;> simp
  have h2 : (if d = a then E c b else 0) y = if d = a then E c b y else 0 := by
    split_ifs <;> simp
  rw [h1, h2] at h
  rw [add_sub_assoc, ← h]
  abel

theorem loweringWord_span_lower (a b : Fin n) (hab : b < a) :
    ∀ x ∈ Submodule.span ℂ {x | ∃ N, LoweringWord E v N x},
      E a b x ∈ Submodule.span ℂ {x | ∃ N, LoweringWord E v N x} := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨N, hN⟩ := hx
    exact Submodule.subset_span ⟨_, hN.step a b hab⟩
  | zero => simp
  | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx

theorem loweringWord_apply_mem (hE : GlRel E) (hv : IsHW E ν v) {N : ℕ} {x : V}
    (hx : LoweringWord E v N x) :
    ∀ a b, E a b x ∈ Submodule.span ℂ {x | ∃ N, LoweringWord E v N x} := by
  induction hx with
  | base =>
    intro a b
    rcases lt_trichotomy a b with h | h | h
    · rw [hv.2 a b h]; exact Submodule.zero_mem _
    · subst h
      rw [hv.1 a]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, LoweringWord.base⟩)
    · exact Submodule.subset_span ⟨_, LoweringWord.base.step a b h⟩
  | step c d h _ ih =>
    intro a b
    rw [glRel_apply_comm hE]
    refine Submodule.sub_mem _ (Submodule.add_mem _ (loweringWord_span_lower c d h _ (ih a b)) ?_) ?_
    · split_ifs
      · exact ih _ _
      · exact Submodule.zero_mem _
    · split_ifs
      · exact ih _ _
      · exact Submodule.zero_mem _

theorem loweringWord_height (hE : GlRel E) (hv : IsHW E ν v) {N : ℕ} {x : V}
    (hx : LoweringWord E v N x) :
    (∑ a : Fin n, ((a.val : ℕ) : ℂ) • E a a) x
      = ((∑ a : Fin n, ((a.val : ℕ) : ℂ) * ν a) + (N : ℂ)) • x := by
  induction hx with
  | base =>
    simp [LinearMap.sum_apply, hv.1, Finset.sum_smul, mul_smul]
  | @step N y c d h _ ih =>
    have key : (∑ a : Fin n, ((a.val : ℕ) : ℂ) • E a a) (E c d y)
        = E c d ((∑ a : Fin n, ((a.val : ℕ) : ℂ) • E a a) y)
          + ((c.val : ℕ) : ℂ) • E c d y - ((d.val : ℕ) : ℂ) • E c d y := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul]
      simp only [glRel_apply_comm hE _ _ c d y, smul_sub, smul_add, Finset.sum_sub_distrib,
        Finset.sum_add_distrib, smul_ite, smul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq',
        Finset.mem_univ, if_true]
    rw [key, ih, map_smul]
    have hle : d.val ≤ c.val := le_of_lt h
    push_cast [Nat.cast_sub hle]
    module

theorem loweringWord_zero_or_pos {N : ℕ} {x : V} (hx : LoweringWord E v N x) :
    x = v ∨ 0 < N := by
  cases hx with
  | base => exact Or.inl rfl
  | step c d h _ =>
    right
    have : d.val < c.val := h
    omega

end

theorem exists_stable_submodule_topWeight_line :
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (n : ℕ) (E : Fin n → Fin n → Module.End ℂ V)
      (ν : Fin n → ℂ) (v : V), GlRel E → IsHW E ν v →
      ∃ S : Submodule ℂ V, (∀ a b, ∀ x ∈ S, E a b x ∈ S) ∧ v ∈ S ∧
        ∀ x ∈ S, (∀ a, E a a x = ν a • x) → ∃ c : ℂ, x = c • v := by
  intro V _ _ n E ν v hE hv
  refine ⟨Submodule.span ℂ {x | ∃ N, LoweringWord E v N x}, ?_,
    Submodule.subset_span ⟨0, LoweringWord.base⟩, ?_⟩
  · intro a b x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨N, hN⟩ := hx
      exact loweringWord_apply_mem hE hv hN a b
    | zero => simp
    | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
    | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx
  · intro x hx hw
    set H : Module.End ℂ V := ∑ a : Fin n, ((a.val : ℕ) : ℂ) • E a a with hH
    set h : ℂ := ∑ a : Fin n, ((a.val : ℕ) : ℂ) * ν a with hh
    have hle : Submodule.span ℂ {x | ∃ N, LoweringWord E v N x}
        ≤ Submodule.span ℂ {v} ⊔ ⨆ (μ : ℂ) (_ : μ ≠ h), H.eigenspace μ := by
      rw [Submodule.span_le]
      rintro y ⟨N, hN⟩
      rcases loweringWord_zero_or_pos hN with rfl | hpos
      · exact Submodule.mem_sup_left (Submodule.mem_span_singleton_self _)
      · refine Submodule.mem_sup_right ?_
        have hne : h + (N : ℂ) ≠ h := by
          have : (N : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
          simpa using this
        refine Submodule.mem_iSup_of_mem (h + (N : ℂ)) (Submodule.mem_iSup_of_mem hne ?_)
        rw [Module.End.mem_eigenspace_iff]
        exact loweringWord_height hE hv hN
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 (hle hx)
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hy
    have hxe : x ∈ H.eigenspace h := by
      rw [Module.End.mem_eigenspace_iff]
      simp [hH, hh, LinearMap.sum_apply, hw, Finset.sum_smul, mul_smul]
    have hve : v ∈ H.eigenspace h := by
      rw [Module.End.mem_eigenspace_iff]
      simp [hH, hh, LinearMap.sum_apply, hv.1, Finset.sum_smul, mul_smul]
    have hze : z ∈ H.eigenspace h := by
      have : z = x - c • v := by rw [← hyz]; abel
      rw [this]
      exact Submodule.sub_mem _ hxe (Submodule.smul_mem _ _ hve)
    have hd := Module.End.eigenspaces_iSupIndep H h
    have hz0 : z = 0 := (Submodule.disjoint_def.1 hd) z hze hz
    exact ⟨c, by rw [← hyz, hz0, add_zero]⟩

end GlobalTheory
