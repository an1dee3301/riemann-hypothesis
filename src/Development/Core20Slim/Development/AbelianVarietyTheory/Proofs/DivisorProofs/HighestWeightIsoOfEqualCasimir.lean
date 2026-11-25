module

public import Mathlib
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.Foundations.IsFockIPOfFockData
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemOrthSucc
public import Batteries.Classes.RatCast
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockMinimalKTypeSecondMember
public import Formalism.LocalRingCardinality.DataTheta
public import Init.Classical
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Function
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Order.Lemmas
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Ext
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Prod
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Basic
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.IsApply
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Prod
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Prod
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Equiv
public import Mathlib.Algebra.Module.Submodule.Ker
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Module.Submodule.LinearMap
public import Mathlib.Algebra.Module.Submodule.Map
public import Mathlib.Algebra.Module.Submodule.Range
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Notation.Prod
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Nontrivial.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Insert
public import Mathlib.Data.Sum.Basic
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Prod
public import Mathlib.LinearAlgebra.Span.Basic
public import Mathlib.Order.Basic
public import Mathlib.Order.Bounds.Defs
public import Mathlib.Order.CompleteLattice.Defs
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Defs
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Notation
public import Mathlib.Order.RelClasses
public import Mathlib.Order.SetNotation
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.Finiteness.Prod
public import Mathlib.Tactic.Linarith.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.LowGen

variable {p q : ℕ}

theorem mem_hwSub {V : Type} [AddCommGroup V] [Module ℂ V] (act : Mat p q →ₗ[ℂ] Module.End ℂ V)
    (μ : Ix p q → ℚ) (x : V) : x ∈ hwSub act μ ↔
      (∀ a, act (Eab a a) x = ((μ a : ℚ) : ℂ) • x) ∧ ∀ a b, posC a b → act (Eab a b) x = 0 := by
  simp [hwSub, wtSub, Submodule.mem_iInf, sub_eq_zero]

theorem genSub_stable {V : Type} [AddCommGroup V] [Module ℂ V] (act : Mat p q →ₗ[ℂ] Module.End ℂ V)
    (S : Set V) (Z : Mat p q) : ∀ y ∈ genSub act S, act Z y ∈ genSub act S := by
  intro y hy
  rw [genSub, Submodule.mem_sInf] at hy ⊢
  exact fun N hN => hN.2 Z y (hy N hN)

theorem mem_genSub_self {V : Type} [AddCommGroup V] [Module ℂ V] (act : Mat p q →ₗ[ℂ] Module.End ℂ V)
    (u : V) : u ∈ genSub act {u} := by
  rw [genSub, Submodule.mem_sInf]
  exact fun N hN => hN.1 rfl

theorem genSub_le {V : Type} [AddCommGroup V] [Module ℂ V] {act : Mat p q →ₗ[ℂ] Module.End ℂ V}
    {u : V} {N : Submodule ℂ V} (hu : u ∈ N) (hN : ∀ Z, ∀ y ∈ N, act Z y ∈ N) : genSub act {u} ≤ N :=
  sInf_le ⟨Set.singleton_subset_iff.2 hu, hN⟩

theorem gen_irred_adm {V : Type} [AddCommGroup V] [Module ℂ V]
    (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (hlie : IsLieAct act) (ip : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ)
    (herm : ∀ x y, star (ip x y) = ip y x) (pos : ∀ x, x ≠ 0 → 0 < (ip x x).re)
    (hadj : ∀ Z x y, ip (act Z x) y = ip x (act (adjZ Z) y))
    {lam : Ix p q → ℚ} (hl : IsParam lam) (hg1 : GapGt lam (((p + q : ℕ) : ℝ) ^ 3 / 24 + 1))
    (hg2 : GapGt lam (((p + q : ℕ) : ℝ) - 1)) (u : V)
    (hfin : ∃ W : Submodule ℂ V, FiniteDimensional ℂ W ∧ u ∈ W ∧ KStable act W)
    (hu : u ∈ hwSub act (blattner lam))
    (hc : casimir act u = ((normSq lam - rhoSq (p + q) : ℚ) : ℂ) • u) :
    (∀ Q : Submodule ℂ V, Q ≤ genSub act {u} → (∀ Z, ∀ y ∈ Q, act Z y ∈ Q) → u ∉ Q → Q = ⊥) ∧
    ∀ μ, ∃ S : Submodule ℂ V, FiniteDimensional ℂ S ∧ ∀ x ∈ genSub act {u}, x ∈ hwSub act μ → x ∈ S := by
  first
  | exact @_root_.GlobalTheory.FiltrationEquivalenceRelation.main
  | exact _root_.GlobalTheory.FiltrationEquivalenceRelation.main
  | (apply _root_.GlobalTheory.FiltrationEquivalenceRelation.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.FiltrationEquivalenceRelation.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.FiltrationEquivalenceRelation.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.FiltrationEquivalenceRelation.main ..)

def prodAct {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
    (a : Mat p q →ₗ[ℂ] Module.End ℂ V) (a' : Mat p q →ₗ[ℂ] Module.End ℂ V') :
    Mat p q →ₗ[ℂ] Module.End ℂ (V × V') where
  toFun Z := (a Z).prodMap (a' Z)
  map_add' Y Z := by ext <;> simp
  map_smul' c Z := by ext <;> simp

@[simp] theorem prodAct_apply {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
    (a : Mat p q →ₗ[ℂ] Module.End ℂ V) (a' : Mat p q →ₗ[ℂ] Module.End ℂ V') (Z : Mat p q) (x : V × V') :
    prodAct a a' Z x = (a Z x.1, a' Z x.2) := rfl

def prodForm {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
    (b : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ) (b' : V' →ₗ⋆[ℂ] V' →ₗ[ℂ] ℂ) : (V × V') →ₗ⋆[ℂ] (V × V') →ₗ[ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ) (fun x y => b x.1 y.1 + b' x.2 y.2)
    (fun x y z => by simp; ring) (fun c x y => by simp; ring) (fun x y z => by simp; ring)
    (fun c x y => by simp; ring)

theorem prodForm_apply {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
    (b : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ) (b' : V' →ₗ⋆[ℂ] V' →ₗ[ℂ] ℂ) (x y : V × V') :
    prodForm b b' x y = b x.1 y.1 + b' x.2 y.2 := rfl

theorem ip_nonneg (M : UGKMod p q) (x : M.M.V) : 0 ≤ (M.ip x x).re := by
  by_cases hx : x = 0
  · simp [hx]
  · exact (M.pos x hx).le

theorem diag_irred {lam : Ix p q → ℚ} (hl : IsParam lam) (hg1 : GapGt lam (((p + q : ℕ) : ℝ) ^ 3 / 24 + 1))
    (hg2 : GapGt lam (((p + q : ℕ) : ℝ) - 1)) (M M' : UGKMod p q) (u : M.M.V) (u' : M'.M.V)
    (hu : u ∈ hwSub M.M.act (blattner lam)) (hu' : u' ∈ hwSub M'.M.act (blattner lam))
    (hc : casimir M.M.act u = ((normSq lam - rhoSq (p + q) : ℚ) : ℂ) • u)
    (hc' : casimir M'.M.act u' = ((normSq lam - rhoSq (p + q) : ℚ) : ℂ) • u') :
    ∀ Q : Submodule ℂ (M.M.V × M'.M.V), Q ≤ genSub (prodAct M.M.act M'.M.act) {(u, u')} →
      (∀ Z, ∀ y ∈ Q, prodAct M.M.act M'.M.act Z y ∈ Q) → (u, u') ∉ Q → Q = ⊥ := by
  refine (gen_irred_adm (prodAct M.M.act M'.M.act) ?_ (prodForm M.ip M'.ip) ?_ ?_ ?_ hl hg1 hg2 (u, u')
    ?_ ?_ ?_).1
  · intro X Y
    refine LinearMap.ext fun x => ?_
    simp only [prodAct_apply, M.M.lie X Y, M'.M.lie X Y, LinearMap.sub_apply, Module.End.mul_apply]
    rfl
  · intro x y
    rw [prodForm_apply, prodForm_apply, star_add, M.herm, M'.herm]
  · intro x hx
    rw [prodForm_apply, Complex.add_re]
    have h1 := ip_nonneg M x.1
    have h2 := ip_nonneg M' x.2
    by_cases h : x.1 = 0
    · have := M'.pos x.2 fun h' => hx (Prod.ext h h')
      linarith
    · have := M.pos x.1 h
      linarith
  · intro Z x y
    simp only [prodForm_apply, prodAct_apply, M.adj, M'.adj]
  · obtain ⟨W, hW, huW, hst⟩ := M.M.kfin u
    obtain ⟨W', hW', huW', hst'⟩ := M'.M.kfin u'
    exact ⟨W.prod W', Module.Finite.of_fg (Submodule.FG.prod (Submodule.FG.of_finite) (Submodule.FG.of_finite)), ⟨huW, huW'⟩,
      fun X hX w hw => ⟨hst X hX _ hw.1, hst' X hX _ hw.2⟩⟩
  · rw [mem_hwSub] at hu hu' ⊢
    exact ⟨fun a => Prod.ext (hu.1 a) (hu'.1 a), fun a b h => Prod.ext (hu.2 a b h) (hu'.2 a b h)⟩
  · refine Prod.ext ?_ ?_
    · rw [Prod.smul_fst, ← hc]
      simp [casimir, Prod.fst_sum]
    · rw [Prod.smul_snd, ← hc']
      simp [casimir, Prod.snd_sum]

theorem gen_iso_of_lowest_type : admQ7 → admQ8 → ∀ (p q : ℕ) (lam : Ix p q → ℚ), IsParam lam → GapGt lam (((p + q : ℕ) : ℝ) ^ 3 / 24 + 1) → GapGt lam (((p + q : ℕ) : ℝ) - 1) → ∀ (M M' : UGKMod p q) (u : M.M.V) (u' : M'.M.V), IsHW M.M.act (blattner lam) u → IsHW M'.M.act (blattner lam) u' → casimir M.M.act u = ((normSq lam - rhoSq (p + q) : ℚ) : ℂ) • u → casimir M'.M.act u' = ((normSq lam - rhoSq (p + q) : ℚ) : ℂ) • u' → IrrGK M'.M → (∃ e : M'.M.V →ₗ[ℂ] M.M.V, Function.Injective e ∧ (∀ Z x, e (M'.M.act Z x) = M.M.act Z (e x)) ∧ e u' = u ∧ LinearMap.range e = genSub M.M.act {u}) ∧ AdmGK M'.M := by
  intro _ _ p q lam hl hg1 hg2 M M' u u' hu hu' hc hc' hirr
  constructor
  · set N := genSub (prodAct M.M.act M'.M.act) {(u, u')} with hN
    have hNs := genSub_stable (prodAct M.M.act M'.M.act) {(u, u')}
    have hw : (u, u') ∈ N := mem_genSub_self _ _
    let π : N →ₗ[ℂ] M'.M.V := LinearMap.snd ℂ _ _ ∘ₗ N.subtype
    have hinj : Function.Injective π := by
      have h := diag_irred hl hg1 hg2 M M' u u' hu.2 hu'.2 hc hc' (N ⊓ LinearMap.ker (LinearMap.snd ℂ _ _))
        inf_le_left (fun Z y hy => ⟨hNs Z y hy.1, by
          have h2 : y.2 = 0 := hy.2
          change M'.M.act Z y.2 = 0
          rw [h2, map_zero]⟩) (fun h => hu'.1 h.2)
      set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
      intro x hx
      have : (x : M.M.V × M'.M.V) ∈ N ⊓ LinearMap.ker (LinearMap.snd ℂ _ _) := ⟨x.2, hx⟩
      rw [h] at this
      exact Subtype.ext this
    have hsurj : Function.Surjective π := by
      rcases hirr.2 (LinearMap.range π) (by
        rintro Z _ ⟨x, rfl⟩
        exact ⟨⟨_, hNs Z x x.2⟩, rfl⟩) with h | h
      · have : u' ∈ LinearMap.range π := ⟨⟨_, hw⟩, rfl⟩
        rw [h] at this
        exact absurd this hu'.1
      · exact LinearMap.range_eq_top.1 h
    let φ := LinearEquiv.ofBijective π ⟨hinj, hsurj⟩
    let e : M'.M.V →ₗ[ℂ] M.M.V := (LinearMap.fst ℂ _ _ ∘ₗ N.subtype) ∘ₗ φ.symm.toLinearMap
    have he : ∀ x : N, e (x : M.M.V × M'.M.V).2 = (x : M.M.V × M'.M.V).1 := fun x =>
      congrArg (fun y : N => (y : M.M.V × M'.M.V).1) (φ.symm_apply_apply x)
    have heZ : ∀ Z x, e (M'.M.act Z x) = M.M.act Z (e x) := by
      intro Z x
      obtain ⟨y, rfl⟩ := hsurj x
      have h1 := he ⟨_, hNs Z y y.2⟩
      have h2 := he y
      exact h1.trans (congrArg (M.M.act Z) h2.symm)
    have heu : e u' = u := he ⟨_, hw⟩
    refine ⟨e, ?_, heZ, heu, le_antisymm ?_ (genSub_le ⟨u', heu⟩ ?_)⟩
    · rcases hirr.2 (LinearMap.ker e) (fun Z y hy => by
        rw [LinearMap.mem_ker] at hy ⊢
        rw [heZ, hy, map_zero]) with h | h
      · exact LinearMap.ker_eq_bot.1 h
      · have : u' ∈ LinearMap.ker e := h ▸ Submodule.mem_top
        rw [LinearMap.mem_ker, heu] at this
        exact absurd this hu.1
    · rintro _ ⟨x, rfl⟩
      obtain ⟨y, rfl⟩ := hsurj x
      have h1 : N ≤ (genSub M.M.act {u}).comap (LinearMap.fst ℂ _ _) :=
        genSub_le (mem_genSub_self _ u) fun Z z hz => genSub_stable _ _ Z _ hz
      exact (he y).symm ▸ h1 y.2
    · rintro Z _ ⟨x, rfl⟩
      exact ⟨_, heZ Z x⟩
  · intro μ
    obtain ⟨S, hS, hS'⟩ := (gen_irred_adm M'.M.act M'.M.lie M'.ip M'.herm M'.pos M'.adj hl hg1 hg2 u'
      (M'.M.kfin u') hu'.2 hc').2 μ
    have htop : genSub M'.M.act {u'} = ⊤ := by
      rcases hirr.2 _ (genSub_stable M'.M.act {u'}) with h | h
      · have := mem_genSub_self M'.M.act u'
        rw [h] at this
        exact absurd this hu'.1
      · exact h
    exact Submodule.finiteDimensional_of_le (S₂ := S) fun x hx => hS' x (htop ▸ Submodule.mem_top) hx

end GlobalTheory.LowGen
