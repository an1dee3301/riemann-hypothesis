module

public import Mathlib
public import Init.BinderNameHint
public import Init.Classical
public import Init.Core
public import Init.Data.Function
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.BigOperators.GroupWithZero.Action
public import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.BigOperators
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Ker
public import Mathlib.Algebra.Module.Submodule.LinearMap
public import Mathlib.Algebra.Module.Torsion.Pi
public import Mathlib.Algebra.Ring.Basic
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Empty
public import Mathlib.Data.Finset.Erase
public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Finset.Insert
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Finsupp.SMul
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Subtype
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.LinearAlgebra.LinearIndependent.Basic
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.LinearAlgebra.Multilinear.Basic
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.Logic.Function.Basic
public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TotallySplit
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

open Finset Function in
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_smul_multilinear_eq_zero_of_prod_vanish : ∀ {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] {X : ι → Type} (A : ∀ i, Submodule K (X i → K)) {M : Type} [AddCommGroup M] [Module K M] (P : (∀ i, A i) →ₘₗ[K] M) {D : Type} (s : Finset D) (c : D → K) (f : D → ∀ i, A i), (∀ x : ∀ i, X i, ∑ d ∈ s, c d * ∏ i, (f d i : X i → K) (x i) = 0) → ∑ d ∈ s, c d • P (f d) = 0 := by
  intro K _ ι _ _ X A M _ _ P
  have vanish (S : Finset ι) :
      ∀ {D : Type} (s : Finset D) (c : D → K) (f : D → ∀ i, A i),
        (∀ i ∉ S, ∀ d ∈ s, ∀ d' ∈ s, f d i = f d' i) →
        (∀ x : ∀ i, X i, ∑ d ∈ s, c d * ∏ i, (f d i : X i → K) (x i) = 0) →
        ∑ d ∈ s, c d • P (f d) = 0 := by
    induction S using Finset.induction_on with
    | empty =>
      intro D s c f hconst hx
      rcases s.eq_empty_or_nonempty with rfl | ⟨d₀, hd₀⟩
      · simp
      have hf : ∀ d ∈ s, f d = f d₀ := fun d hd =>
        funext fun i => hconst i (Finset.notMem_empty i) d hd d₀ hd₀
      have hsum : ∑ d ∈ s, c d • P (f d) = (∑ d ∈ s, c d) • P (f d₀) := by
        rw [Finset.sum_smul]; exact Finset.sum_congr rfl fun d hd => by rw [hf d hd]
      have hx' : ∀ x : ∀ i, X i, (∑ d ∈ s, c d) * ∏ i, (f d₀ i : X i → K) (x i) = 0 := by
        intro x; rw [Finset.sum_mul, ← hx x]
        exact Finset.sum_congr rfl fun d hd => by rw [hf d hd]
      rw [hsum]
      by_cases hc : ∑ d ∈ s, c d = 0
      · rw [hc, zero_smul]
      · by_contra hne
        have hex : ∀ i, ∃ t : X i, (f d₀ i : X i → K) t ≠ 0 := by
          intro i
          by_contra h
          push Not at h
          apply hne
          have h0 : f d₀ i = 0 := by
            apply Subtype.ext
            funext t
            simpa using h t
          rw [P.map_coord_zero i h0, smul_zero]
        choose x hxne using hex
        have h1 := hx' x
        rw [mul_eq_zero] at h1
        rcases h1 with h | h
        · exact hc h
        · exact (Finset.prod_ne_zero_iff.mpr fun i _ => hxne i) h
    | insert i₀ S hi₀ ih =>
      intro D s c f hconst hx
      classical
      let W : Submodule K (A i₀) := Submodule.span K (↑(s.image fun d => f d i₀))
      let b := Module.finBasis K W
      have hmem : ∀ d ∈ s, f d i₀ ∈ W := fun d hd =>
        Submodule.subset_span (by simp only [Finset.coe_image]; exact ⟨d, hd, rfl⟩)
      let a : D → Fin (Module.finrank K W) → K := fun d l =>
        if hd : d ∈ s then b.repr ⟨f d i₀, hmem d hd⟩ l else 0
      have hexp : ∀ d ∈ s, f d i₀ = ∑ l, a d l • (b l : A i₀) := by
        intro d hd
        have h := congrArg Subtype.val (b.sum_repr ⟨f d i₀, hmem d hd⟩)
        simp only [Submodule.coe_sum, Submodule.coe_smul] at h
        simp only [a, dite_eq_left hd]
        exact h.symm
      have hP : ∀ d ∈ s, P (f d) = ∑ l, a d l • P (update (f d) i₀ (b l)) := by
        intro d hd
        have e : f d = update (f d) i₀ (∑ l, a d l • (b l : A i₀)) := by
          rw [← hexp d hd, update_eq_self]
        rw [e, P.map_update_sum]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [P.map_update_smul, RingHom.id_apply, update_idem]

      have hsplit : ∀ (g : ∀ i, A i) (y : ∀ i, X i), ∏ i, (g i : X i → K) (y i) =
          (g i₀ : X i₀ → K) (y i₀) * ∏ i ∈ univ.erase i₀, (g i : X i → K) (y i) := fun g y =>
        (Finset.mul_prod_erase univ (fun i => (g i : X i → K) (y i)) (mem_univ i₀)).symm
      have hupd : ∀ (g : ∀ i, A i) (v : A i₀) (y : ∀ i, X i),
          ∏ i ∈ univ.erase i₀, (update g i₀ v i : X i → K) (y i) =
            ∏ i ∈ univ.erase i₀, (g i : X i → K) (y i) := fun g v y =>
        Finset.prod_congr rfl fun i hi => by rw [update_of_ne (Finset.ne_of_mem_erase hi)]
      have hupdx : ∀ (g : ∀ i, A i) (y : ∀ i, X i) (t : X i₀),
          ∏ i ∈ univ.erase i₀, (g i : X i → K) (update y i₀ t i) =
            ∏ i ∈ univ.erase i₀, (g i : X i → K) (y i) := fun g y t =>
        Finset.prod_congr rfl fun i hi => by rw [update_of_ne (Finset.ne_of_mem_erase hi)]
      have hli : LinearIndependent K (fun l => ((b l : A i₀) : X i₀ → K)) :=
        b.linearIndependent.map' ((A i₀).subtype ∘ₗ W.subtype)
          (LinearMap.ker_eq_bot_of_injective (Subtype.val_injective.comp Subtype.val_injective))

      have hB : ∀ (x : ∀ i, X i) (l : Fin (Module.finrank K W)),
          ∑ d ∈ s, c d * a d l * ∏ i ∈ univ.erase i₀, (f d i : X i → K) (x i) = 0 := by
        intro x
        refine Fintype.linearIndependent_iff.mp hli _ ?_
        funext t
        have h := hx (update x i₀ t)
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
        rw [← h]
        simp only [Finset.sum_mul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun d hd => ?_
        rw [hsplit, hupdx, update_self, hexp d hd]
        simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
          smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl fun l _ => ?_
        ring
      have hstep : ∑ d ∈ s, c d • P (f d) =
          ∑ l, ∑ d ∈ s, (c d * a d l) • P (update (f d) i₀ (b l)) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun d hd => ?_
        rw [hP d hd, Finset.smul_sum]
        simp only [mul_smul]
      rw [hstep]
      refine Finset.sum_eq_zero fun l _ => ih s (fun d => c d * a d l)
        (fun d => update (f d) i₀ (b l)) ?_ ?_
      · intro i hi d hd d' hd'
        by_cases h : i = i₀
        · subst h; simp
        · simp only [update_of_ne h]
          exact hconst i (by simp [h, hi]) d hd d' hd'
      · intro x
        have h := hB x l
        calc ∑ d ∈ s, c d * a d l * ∏ i, (update (f d) i₀ (b l) i : X i → K) (x i)
            = ((b l : A i₀) : X i₀ → K) (x i₀) *
                ∑ d ∈ s, c d * a d l * ∏ i ∈ univ.erase i₀, (f d i : X i → K) (x i) := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun d _ => ?_
              rw [hsplit, hupd, update_self]
              ring
          _ = 0 := by rw [h, mul_zero]
  intro D s c f hx
  exact vanish univ s c f (fun i hi => absurd (mem_univ i) hi) hx
