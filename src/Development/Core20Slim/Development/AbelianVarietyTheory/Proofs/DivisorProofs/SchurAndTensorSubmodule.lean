module

public import Mathlib
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.Foundations.IsFockIPOfFockData
public import Batteries.Classes.RatCast
public import Formalism.LocalRingCardinality.DataTheta
public import Init.BinderNameHint
public import Init.ByCases
public import Init.Classical
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Rat.Basic
public import Init.Data.Sum.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.BigOperators
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Submodule.Basic
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Ker
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Module.Submodule.LinearMap
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Order.Group.Unbundled.Basic
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
public import Mathlib.Algebra.Order.Ring.Rat
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Ring.Unbundled.Rat
public import Mathlib.Algebra.Order.Star.Rat
public import Mathlib.Algebra.Order.ZeroLEOne
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Algebra.Star.Rat
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Nontrivial.Defs
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.ENat.Basic
public import Mathlib.Data.ENat.Defs
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Basis
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Cast.Order.Basic
public import Mathlib.Data.Rat.BigOperators
public import Mathlib.Data.Rat.Cast.CharZero
public import Mathlib.Data.Rat.Cast.Defs
public import Mathlib.Data.Rat.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Set.Finite.Lemmas
public import Mathlib.Data.Set.Function
public import Mathlib.Data.Set.Operations
public import Mathlib.Data.Sum.Basic
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Minpoly
public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.Order.BoundedOrder.Basic
public import Mathlib.Order.CompleteLattice.Basic
public import Mathlib.Order.CompleteLattice.Defs
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Hom.Basic
public import Mathlib.Order.Lattice
public import Mathlib.Order.Notation
public import Mathlib.Order.SetNotation
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Tactic.Linarith.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial

noncomputable section
namespace GlobalTheory.IrrTensor

section General
variable {V : Type} [AddCommGroup V] [Module ℂ V] {ι : Type} (A : ι → Module.End ℂ V)


variable {W : Type} [AddCommGroup W] [Module ℂ W]

end General

variable {p q : ℕ}

theorem mem_wtSub {V : Type} [AddCommGroup V] [Module ℂ V] {act : Mat p q →ₗ[ℂ] Module.End ℂ V}
    {μ : Ix p q → ℚ} {v : V} : v ∈ wtSub act μ ↔ ∀ a, act (Eab a a) v = ((μ a : ℚ) : ℂ) • v := by
  simp [wtSub, Submodule.mem_iInf, sub_eq_zero]

theorem root_shift {V : Type} [AddCommGroup V] [Module ℂ V] {act : Mat p q →ₗ[ℂ] Module.End ℂ V}
    (hl : IsLieAct act) {μ : Ix p q → ℚ} {v : V} (hv : v ∈ wtSub act μ) (a b : Ix p q) :
    act (Eab a b) v ∈ wtSub act (fun c => μ c + ((if c = a then 1 else 0) - (if c = b then 1 else 0))) := by
  rw [mem_wtSub] at hv ⊢
  intro c
  have h := LinearMap.congr_fun (hl (Eab c c) (Eab a b)) v
  have e : (Eab c c * Eab a b - Eab a b * Eab c c : Mat p q) =
      (((if c = a then 1 else 0) - (if c = b then 1 else 0) : ℚ) : ℂ) • Eab a b := by
    unfold Eab
    have e1 : (Matrix.single c c 1 * Matrix.single a b 1 : Mat p q) =
        (if c = a then (1 : ℂ) else 0) • Matrix.single a b 1 := by
      split_ifs with h
      · subst h; simp
      · simp [Matrix.single_mul_single_of_ne, h]
    have e2 : (Matrix.single a b 1 * Matrix.single c c 1 : Mat p q) =
        (if c = b then (1 : ℂ) else 0) • Matrix.single a b 1 := by
      split_ifs with h
      · subst h; simp
      · simp [Matrix.single_mul_single_of_ne, Ne.symm h]
    rw [e1, e2, ← sub_smul]
    congr 1
    split_ifs <;> simp
  rw [e, map_smul, LinearMap.smul_apply, LinearMap.sub_apply, Module.End.mul_apply,
    Module.End.mul_apply, hv c, map_smul, eq_sub_iff_add_eq] at h
  rw [← h, Rat.cast_add, add_smul, add_comm]

theorem exists_highest (M : GKMod p q) [Nontrivial M.V] : ∃ μ v, IsHW M.act μ v := by
  obtain ⟨μ₀, v₀, hv₀, hv₀'⟩ : ∃ μ v, v ∈ wtSub M.act μ ∧ v ≠ 0 := by
    by_contra h
    push Not at h
    obtain ⟨x, hx⟩ := exists_ne (0 : M.V)
    have : (⨆ μ : Ix p q → ℚ, wtSub M.act μ) = ⊥ :=
      iSup_eq_bot.2 fun μ => (Submodule.eq_bot_iff _).2 (h μ)
    have h2 := M.wts x
    rw [this] at h2
    exact hx h2
  obtain ⟨U, hfd, hU, hK⟩ := M.kfin v₀
  let k : Ix p q → ℚ := Sum.elim (fun i => -((i : ℕ) : ℚ)) (fun i => -((i : ℕ) : ℚ))
  let h : (Ix p q → ℚ) → ℚ := fun μ => ∑ a, k a * μ a
  let H : Mat p q := ∑ a, ((k a : ℚ) : ℂ) • Eab a a
  have hKE : ∀ a b : Ix p q, sameBlock a b → IsKC (Eab a b) := by
    intro a b hab c d hcd
    unfold Eab
    rw [Matrix.single_apply, if_neg]
    rintro ⟨rfl, rfl⟩
    exact hcd hab
  have hH : ∀ x ∈ U, M.act H x ∈ U := by
    intro x hx
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [H, map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]
    exact U.sum_mem fun a _ => U.smul_mem _ (hK _ (hKE a a (by cases a <;> trivial)) x hx)
  let S : Set (Ix p q → ℚ) := {μ | ∃ v ∈ U, v ∈ wtSub M.act μ ∧ v ≠ 0}
  have hfin : (h '' S).Finite := by
    have h1 := Module.End.finite_hasEigenvalue ((M.act H).restrict hH)
    refine (h1.preimage (f := fun x : ℚ => (x : ℂ)) Rat.cast_injective.injOn).subset ?_
    rintro _ ⟨μ, ⟨v, hvU, hv, hv0⟩, rfl⟩
    refine Module.End.hasEigenvalue_of_hasEigenvector (x := ⟨v, hvU⟩) ⟨?_, fun e => hv0 (congrArg Subtype.val e)⟩
    rw [Module.End.mem_eigenspace_iff]
    apply Subtype.ext
    show M.act H v = ((h μ : ℚ) : ℂ) • v
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [H, h, map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
      mem_wtSub.1 hv, smul_smul, ← Finset.sum_smul]
    push_cast
    rfl
  obtain ⟨_, ⟨μ, ⟨v, hvU, hv, hv0⟩, rfl⟩, hmax⟩ :=
    Set.exists_max_image (h '' S) id hfin ⟨_, μ₀, ⟨v₀, hU, hv₀, hv₀'⟩, rfl⟩
  refine ⟨μ, v, hv0, hv, ?_⟩
  simp only [SetLike.mem_coe, Submodule.mem_iInf, LinearMap.mem_ker]
  intro a b hab
  by_contra hne
  have hs : sameBlock a b := by cases a <;> cases b <;> first | trivial | exact hab
  have hlt : k b < k a := by
    cases a <;> cases b <;> first | exact hab.elim | skip
    all_goals
      simp only [k, Sum.elim_inl, Sum.elim_inr, neg_lt_neg_iff, Nat.cast_lt]
      exact hab
  have := hmax _ ⟨_, ⟨_, hK _ (hKE a b hs) v hvU, root_shift M.lie hv a b, hne⟩, rfl⟩
  simp only [id, h, mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, mul_ite,
    mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at this
  linarith

theorem schur (M : GKMod p q) (hI : IrrGK M) (hA : AdmGK M) (T : M.V →ₗ[ℂ] M.V)
    (hT : ∀ Z, T ∘ₗ M.act Z = M.act Z ∘ₗ T) : ∃ c : ℂ, T = c • LinearMap.id := by
  haveI := hI.1
  obtain ⟨μ, v, hv0, hv⟩ := exists_highest M
  have hf : ∀ Z x, T (M.act Z x) = M.act Z (T x) := fun Z x => LinearMap.congr_fun (hT Z) x
  have hst : ∀ x ∈ hwSub M.act μ, T x ∈ hwSub M.act μ := by
    intro x hx
    simp only [hwSub, wtSub, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker,
      LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply] at hx ⊢
    refine ⟨fun c => ?_, fun c d h => ?_⟩
    · rw [← hf, ← map_smul, ← map_sub, hx.1 c, map_zero]
    · rw [← hf, hx.2 c d h, map_zero]
  haveI := hA μ
  haveI : Nontrivial (hwSub M.act μ) := ⟨⟨⟨v, hv⟩, 0, fun e => hv0 (congrArg Subtype.val e)⟩⟩
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue (T.restrict hst)
  obtain ⟨x, hx⟩ := hc.exists_hasEigenvector
  have hx1 : T x = c • (x : M.V) := congrArg Subtype.val hx.apply_eq_smul
  refine ⟨c, ?_⟩
  rcases hI.2 (LinearMap.ker (T - c • LinearMap.id)) (fun Z y hy => by
    simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
      sub_eq_zero] at hy ⊢
    rw [hf, hy, map_smul]) with h | h
  · exact absurd (Subtype.ext ((Submodule.eq_bot_iff _).1 h x (by simp [hx1]))) hx.2
  · exact sub_eq_zero.1 (LinearMap.ker_eq_top.1 h)

end GlobalTheory.IrrTensor
