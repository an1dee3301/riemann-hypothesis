module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FramePositiveSum
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchwartzBruhatMatrixExistsOpenAddSubgroupInvaria
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.StandardOrderExtendedBasisApplyLowBlock
public import Init.Classical
public import Init.Core
public import Init.Data.Order.Lemmas
public import Init.Data.Zero
public import Init.Prelude
public import Init.PropLemmas
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.GroupWithZero.Units.Lemmas
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Order.IsBotOne
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.Pow
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Set.Basic
public import Mathlib.Data.Set.BooleanAlgebra
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.GroupTheory.ArchimedeanDensely
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.Order.Basic
public import Mathlib.Order.CompleteBooleanAlgebra
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Order.Filter.AtTopBot.Defs
public import Mathlib.Order.Filter.Basic
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.Filter.Finite
public import Mathlib.Order.Filter.Pi
public import Mathlib.Order.Lattice
public import Mathlib.Order.RelClasses
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.Valuation.Basic
public import Mathlib.RingTheory.Valuation.Integers
public import Mathlib.RingTheory.Valuation.ValuativeRel.Basic
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Neighborhoods
public import Mathlib.Topology.NhdsWithin

@[expose] public section

open MeasureTheory ValuativeRel Matrix Topology GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum

namespace GlobalTheory.AdaptedExp

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem eventually_pow_le {ϖ : kˣ} (h : IsUnif ϖ) (s : kˣ) :
    ∀ᶠ e : ℕ in Filter.atTop, valuation k ((ϖ ^ e : kˣ) : k) ≤ valuation k (s : k) := by
  have h1 : valuation k (ϖ : k) < 1 := (h _).2 le_rfl
  have hs : valuation k (s : k) ≠ 0 := by simp
  obtain ⟨m, hm⟩ := exists_pow_lt₀ h1 (Units.mk0 _ hs)
  filter_upwards [Filter.eventually_ge_atTop m] with e he
  rw [Units.val_pow_eq_pow_val, map_pow]
  exact (pow_le_pow_right_of_le_one' h1.le he).trans hm.le

theorem eventually_subset_cball {ϖ : kˣ} (h : IsUnif ϖ) {K : Set k} (hK : IsCompact K) :
    ∀ᶠ e : ℕ in Filter.atTop, K ⊆ cball (ϖ ^ e)⁻¹ := by
  have key : ∀ s : kˣ, ∀ᶠ e : ℕ in Filter.atTop, cball s ⊆ cball (ϖ ^ e)⁻¹ := by
    intro s
    filter_upwards [eventually_pow_le h s⁻¹] with e he x hx
    have hs : 0 < valuation k (s : k) := by simp [pos_iff_ne_zero]
    have he0 : 0 < valuation k ((ϖ ^ e : kˣ) : k) := by
      rw [pos_iff_ne_zero]; simp
    simp only [cball, Set.mem_ofPred_eq, Units.val_inv_eq_inv_val, map_inv₀] at hx he ⊢
    exact hx.trans ((le_inv_comm₀ he0 hs).1 he)
  refine hK.induction_on (p := fun K => ∀ᶠ e : ℕ in Filter.atTop, K ⊆ cball (ϖ ^ e)⁻¹)
    (by simp) ?_ ?_ ?_
  · intro s t hst ht
    exact ht.mono fun e he => hst.trans he
  · intro s t hs ht
    filter_upwards [hs, ht] with e h1 h2 using Set.union_subset h1 h2
  · intro x _
    by_cases hx : x = 0
    · subst hx
      exact ⟨cball 1, mem_nhdsWithin_of_mem_nhds (cball_mem_nhds 1), key 1⟩
    · exact ⟨cball (Units.mk0 x hx), mem_nhdsWithin_of_mem_nhds
        ((isOpen_cball _).mem_nhds (by simp [cball])), key _⟩

variable {n n' : Type}

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem withCol_add (x₀ : Matrix n n' k) (y z : n → k) :
    withCol x₀ (y + z) = withCol x₀ y + withCol (0 : Matrix n n' k) z := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> simp [withCol]

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in
theorem continuous_withCol_zero :
    Continuous fun z : n → k => withCol (0 : Matrix n n' k) z := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  rcases i with i | i <;> rcases j with j | j <;> simp only [withCol, fromBlocks_apply₁₁,
    fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂, of_apply] <;> fun_prop

theorem eventually_box_subset [Fintype n] {ϖ : kˣ} (h : IsUnif ϖ) {U : Set (n → k)}
    (hU : U ∈ 𝓝 (0 : n → k)) :
    ∀ᶠ e : ℕ in Filter.atTop, ∀ z ∈ box n (ϖ ^ e), z ∈ U := by
  rw [nhds_pi, Filter.mem_pi] at hU
  obtain ⟨I, -, t, ht, hsub⟩ := hU
  choose s hs using fun i => exists_cball_subset (ht i)
  filter_upwards [Filter.eventually_all.2 fun i => eventually_pow_le h (s i)] with e he z hz
  exact hsub fun i _ => hs i (le_trans (hz i) (he i))

theorem eventually_adapted [Fintype n] [Fintype n'] {ϖ : kˣ} (h : IsUnif ϖ)
    {Ψ : Matrix (n ⊕ Fin 0) (n' ⊕ Fin (0 + 1)) k → ℂ}
    (hΨ : Ψ ∈ SB (Matrix (n ⊕ Fin 0) (n' ⊕ Fin (0 + 1)) k)) :
    ∀ᶠ e : ℕ in Filter.atTop, ∀ (x₀ : Matrix n n' k) (y : n → k),
      (Ψ (withCol x₀ y) ≠ 0 → y ∈ box n (ϖ ^ e)⁻¹) ∧
        ∀ z ∈ box n (ϖ ^ e), Ψ (withCol x₀ (y + z)) = Ψ (withCol x₀ y) := by
  obtain ⟨Λ, hΛ, hinv⟩ := sb_matrix_exists_isOpen_addSubgroup k _ _ Ψ hΨ
  have hc : IsCompact (tsupport Ψ) := hΨ.2
  have h1 : ∀ r : n, ∀ᶠ e : ℕ in Filter.atTop,
      (fun x : Matrix (n ⊕ Fin 0) (n' ⊕ Fin (0 + 1)) k => x (Sum.inl r) (Sum.inr 0)) ''
        tsupport Ψ ⊆ cball (ϖ ^ e)⁻¹ := fun r =>
    eventually_subset_cball h (hc.image (by fun_prop))
  have h0 : withCol (0 : Matrix n n' k) (0 : n → k) = 0 := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;> simp [withCol]
  have h2 : (fun z : n → k => withCol (0 : Matrix n n' k) z) ⁻¹' (Λ : Set _) ∈ 𝓝 (0 : n → k) :=
    (hΛ.preimage continuous_withCol_zero).mem_nhds (by
      simp only [Set.mem_preimage, h0]; exact Λ.zero_mem)
  filter_upwards [Filter.eventually_all.2 h1, eventually_box_subset h h2] with e he1 he2 x₀ y
  refine ⟨fun hne r => ?_, fun z hz => ?_⟩
  · exact he1 r ⟨withCol x₀ y, subset_tsupport _ hne, rfl⟩
  · rw [withCol_add]
    exact hinv _ _ (he2 z hz)

theorem exists_adapted_exponent : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n] (n' : Type) [Fintype n'] [DecidableEq n'] (S : Set (Matrix (n ⊕ Fin 0) (n' ⊕ Fin (0 + 1)) k → ℂ)), S.Finite → (∀ Ψ ∈ S, Ψ ∈ SB (Matrix (n ⊕ Fin 0) (n' ⊕ Fin (0 + 1)) k)) → ∀ ϖ : kˣ, IsUnif ϖ → ∃ e : ℕ, 1 ≤ e ∧ ∀ Ψ ∈ S, ∀ (x₀ : Matrix n n' k) (y : n → k), (Ψ (withCol x₀ y) ≠ 0 → y ∈ box n (ϖ ^ e)⁻¹) ∧ ∀ z ∈ box n (ϖ ^ e), Ψ (withCol x₀ (y + z)) = Ψ (withCol x₀ y) := by
  intro k _ _ _ _ n _ _ n' _ _ S hS hSB ϖ h
  exact ((Filter.eventually_ge_atTop 1).and ((Filter.eventually_all_finite hS).2
    fun Ψ hΨ => eventually_adapted h (hSB Ψ hΨ))).exists

end GlobalTheory.AdaptedExp
