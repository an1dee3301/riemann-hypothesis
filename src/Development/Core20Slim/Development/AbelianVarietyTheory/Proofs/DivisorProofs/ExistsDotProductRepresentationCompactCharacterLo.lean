module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsNotRelZero
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareTriple
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareStanding
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VacFn
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReGt
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.BinderNameHint
public import Init.Classical
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Subsemigroup.Defs
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Group.WithOne.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Notation.Pi.Basic
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Quotient
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Fourier.FiniteAbelian.Orthogonality
public import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Empty
public import Mathlib.Data.Finset.Insert
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Set.CoeSort
public import Mathlib.Data.Set.Defs
public import Mathlib.GroupTheory.Coset.Defs
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Push
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Group.Subgroup
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.Nonarchimedean.Basic
public import Mathlib.Topology.Algebra.OpenSubgroup
public import Mathlib.Topology.Algebra.Valued.NormedValued
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.MetricSpace.Pseudo.Pi
public import Mathlib.Topology.MetricSpace.Ultra.Basic
public import Mathlib.Topology.MetricSpace.Ultra.Pi
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.CompactCharDual

theorem eq_one_of_pow_close {z : ℂ} (h : ∀ n : ℕ, ‖z ^ n - 1‖ < 1 / 2) : z = 1 := by
  first
  | exact @_root_.GlobalTheory.UnitNormRealPartBound.main
  | exact _root_.GlobalTheory.UnitNormRealPartBound.main
  | (apply _root_.GlobalTheory.UnitNormRealPartBound.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.UnitNormRealPartBound.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.UnitNormRealPartBound.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.UnitNormRealPartBound.main ..)

theorem exists_ball_ker {K : Type} [NormedAddCommGroup K] [IsUltrametricDist K] (ψ : AddChar K ℂ)
    (hc : Continuous ψ) : ∃ δ > 0, ∀ x : K, ‖x‖ < δ → ψ x = 1 := by
  obtain ⟨δ, hδ, h⟩ := Metric.continuousAt_iff.1 (hc.continuousAt (x := 0)) (1 / 2) (by norm_num)
  refine ⟨δ, hδ, fun x hx => eq_one_of_pow_close fun n => ?_⟩
  have := h (x := n • x) (by
    rw [dist_zero_right]; exact (IsUltrametricDist.norm_nsmul_le x n).trans_lt hx)
  rwa [AddChar.map_zero_eq_one, dist_eq_norm, AddChar.map_nsmul_eq_pow] at this

theorem mem_of_separates {Q : Type} [AddCommGroup Q] [Finite Q] (H : AddSubgroup (AddChar Q ℂ))
    (h : ∀ x : Q, x ≠ 0 → ∃ χ ∈ H, χ x ≠ 1) (χ : AddChar Q ℂ) : χ ∈ H := by
  by_contra hχ
  have h0 : (QuotientAddGroup.mk χ : AddChar Q ℂ ⧸ H) ≠ 0 := fun e => hχ ((QuotientAddGroup.eq_zero_iff _).1 e)
  obtain ⟨Λ, hΛ⟩ := AddChar.exists_apply_ne_zero.2 h0
  obtain ⟨x, hx⟩ := (AddChar.doubleDualEquiv (α := Q)).surjective (Λ.compAddMonoidHom (QuotientAddGroup.mk' H))
  have hev : ∀ φ : AddChar Q ℂ, φ x = Λ (QuotientAddGroup.mk φ) := fun φ => DFunLike.congr_fun hx φ
  by_cases hx0 : x = 0
  · exact hΛ (by rw [← hev, hx0, AddChar.map_zero_eq_one])
  · obtain ⟨φ, hφ, hφx⟩ := h x hx0
    exact hφx (by rw [hev, (QuotientAddGroup.eq_zero_iff _).2 hφ, AddChar.map_zero_eq_one])

theorem exists_lift {G : Type} [AddCommGroup G] (N : AddSubgroup G) (φ : AddChar G ℂ)
    (hφ : ∀ x ∈ N, φ x = 1) : ∃ Λ : AddChar (G ⧸ N) ℂ, ∀ x : G, Λ x = φ x := by
  refine ⟨⟨Quotient.lift φ fun a b hab => ?_, φ.map_zero_eq_one, ?_⟩, fun x => rfl⟩
  · have := hφ _ (QuotientAddGroup.leftRel_apply.1 hab)
    rw [← add_neg_cancel_left a b, AddChar.map_add_eq_mul, this, mul_one]
  · rintro ⟨a⟩ ⟨b⟩
    exact φ.map_add_eq_mul a b

end GlobalTheory.CompactCharDual

namespace GlobalTheory.CompactCharDual

theorem exists_dotProduct_eq {K : Type} [NormedField K] [IsUltrametricDist K] {κ : Type} [Fintype κ]
    (ψ₀ : AddChar K ℂ) (hc : Continuous ψ₀) (hne : ψ₀ ≠ 1)
    (L : AddSubgroup (κ → K)) (hL : IsCompact (L : Set (κ → K)))
    (L' : AddSubgroup (κ → K)) (hL' : IsOpen (L' : Set (κ → K)))
    (χ : (κ → K) → ℂ) (hmul : ∀ y ∈ L, ∀ y' ∈ L, χ (y + y') = χ y * χ y') (htriv : ∀ y ∈ L, y ∈ L' → χ y = 1) :
    ∃ x₀ : κ → K, ∀ y ∈ L, χ y = ψ₀ (x₀ ⬝ᵥ y) := by
  classical
  obtain ⟨δ, hδ, hψδ⟩ := exists_ball_ker ψ₀ hc
  obtain ⟨r, hr, hrL'⟩ := Metric.isOpen_iff.1 hL' 0 L'.zero_mem
  obtain ⟨t₁, ht₁⟩ : ∃ t, ψ₀ t ≠ 1 := by
    by_contra h
    push_neg at h
    exact hne (DFunLike.ext _ _ fun t => by rw [h t, AddChar.one_apply])
  have ht0 : 0 < ‖t₁‖ := norm_pos_iff.2 fun h => ht₁ (by rw [h, AddChar.map_zero_eq_one])
  set ρ := ‖t₁‖ / r with hρ
  have hρ0 : 0 < ρ := div_pos ht0 hr
  set η := min r (δ / ρ) with hη
  have hη0 : 0 < η := lt_min hr (div_pos hδ hρ0)

  have small : ∀ a y : κ → K, ‖a‖ ≤ ρ → ‖y‖ < η → ψ₀ (a ⬝ᵥ y) = 1 := by
    intro a y ha hy
    have key : ∀ s : Finset κ, (∀ i ∈ s, ψ₀ (a i * y i) = 1) → ψ₀ (∑ i ∈ s, a i * y i) = 1 := by
      intro s
      induction s using Finset.induction_on with
      | empty => intro _; simp
      | insert i s hi ih =>
        intro hf
        rw [Finset.sum_insert hi, AddChar.map_add_eq_mul, hf i (Finset.mem_insert_self _ _),
          ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)), one_mul]
    show ψ₀ (∑ i, a i * y i) = 1
    refine key Finset.univ fun i _ => hψδ _ ?_
    rw [norm_mul]
    have h1 : ‖a i‖ ≤ ρ := (norm_le_pi_norm a i).trans ha
    have h2 : ‖y i‖ < δ / ρ := ((norm_le_pi_norm y i).trans_lt hy).trans_le (min_le_right _ _)
    calc ‖a i‖ * ‖y i‖ ≤ ρ * ‖y i‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
      _ < ρ * (δ / ρ) := mul_lt_mul_of_pos_left h2 hρ0
      _ = δ := mul_div_cancel₀ _ hρ0.ne'
  let M : AddSubgroup (κ → K) :=
    { carrier := {y | ∀ a : κ → K, ‖a‖ ≤ ρ → ψ₀ (a ⬝ᵥ y) = 1}
      add_mem' := fun {y y'} hy hy' a ha => by
        rw [dotProduct_add, AddChar.map_add_eq_mul, hy a ha, hy' a ha, mul_one]
      zero_mem' := fun a _ => by rw [dotProduct_zero, AddChar.map_zero_eq_one]
      neg_mem' := fun {y} hy a ha => by
        rw [dotProduct_neg, ← neg_dotProduct]
        exact hy (-a) (by rwa [norm_neg]) }
  have hMmem : ∀ y, y ∈ M ↔ ∀ a : κ → K, ‖a‖ ≤ ρ → ψ₀ (a ⬝ᵥ y) = 1 := fun y => Iff.rfl

  have hML' : ∀ y ∈ M, y ∈ L' := by
    intro y hy
    refine hrL' (mem_ball_zero_iff.2 ?_)
    rw [pi_norm_lt_iff hr]
    intro k
    by_contra hk
    push_neg at hk
    have hyk : 0 < ‖y k‖ := hr.trans_le hk
    refine ht₁ ?_
    have hnorm : ‖(Pi.single k (t₁ / y k) : κ → K)‖ ≤ ρ := by
      refine (pi_norm_le_iff_of_nonneg hρ0.le).2 fun i => ?_
      by_cases hi : i = k
      · subst hi
        rw [Pi.single_eq_same, norm_div]
        exact div_le_div_of_nonneg_left ht0.le hr hk
      · rw [Pi.single_eq_of_ne hi, norm_zero]; exact hρ0.le
    have := (hMmem y).1 hy _ hnorm
    rwa [single_dotProduct, div_mul_cancel₀ _ (norm_pos_iff.1 hyk)] at this

  let U : AddSubgroup (κ → K) :=
    { carrier := Metric.ball 0 η
      add_mem' := fun {a b} ha hb => mem_ball_zero_iff.2
        ((IsUltrametricDist.norm_add_le_max a b).trans_lt (max_lt (mem_ball_zero_iff.1 ha) (mem_ball_zero_iff.1 hb)))
      zero_mem' := Metric.mem_ball_self hη0
      neg_mem' := fun {a} ha => by simpa using ha }
  have hUM : U ≤ M := fun y hy a ha => small a y ha (mem_ball_zero_iff.1 hy)
  let N : AddSubgroup L := M.addSubgroupOf L
  have hNo : IsOpen (N : Set L) := by
    refine AddSubgroup.isOpen_mono (H₁ := U.addSubgroupOf L)
      (fun y hy => AddSubgroup.mem_addSubgroupOf.2 (hUM (AddSubgroup.mem_addSubgroupOf.1 hy))) ?_
    exact (Metric.isOpen_ball (x := (0 : κ → K)) (ε := η)).preimage continuous_subtype_val
  haveI : CompactSpace L := isCompact_iff_compactSpace.1 hL
  haveI : Finite (L ⧸ N) := AddSubgroup.quotient_finite_of_isOpen N hNo

  let e : (κ → K) → AddChar L ℂ := fun a =>
    { toFun := fun y => ψ₀ (a ⬝ᵥ (y : κ → K))
      map_zero_eq_one' := by simp
      map_add_eq_mul' := fun y y' => by
        rw [AddSubgroup.coe_add, dotProduct_add, AddChar.map_add_eq_mul] }
  have he : ∀ a (y : L), e a y = ψ₀ (a ⬝ᵥ (y : κ → K)) := fun _ _ => rfl
  have hχ0 : χ 0 = 1 := htriv 0 L.zero_mem L'.zero_mem
  let χL : AddChar L ℂ :=
    { toFun := fun y => χ y
      map_zero_eq_one' := hχ0
      map_add_eq_mul' := fun y y' => hmul _ y.2 _ y'.2 }
  obtain ⟨X, hX⟩ := exists_lift N χL fun y hy => htriv _ y.2 (hML' _ hy)
  let H : AddSubgroup (AddChar (L ⧸ N) ℂ) :=
    { carrier := {Λ | ∃ a : κ → K, ‖a‖ ≤ ρ ∧ ∀ y : L, Λ y = ψ₀ (a ⬝ᵥ (y : κ → K))}
      add_mem' := by
        rintro Λ Λ' ⟨a, ha, h⟩ ⟨b, hb, h'⟩
        refine ⟨a + b, (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb), fun y => ?_⟩
        rw [AddChar.add_apply, h, h', add_dotProduct, AddChar.map_add_eq_mul]
      zero_mem' := ⟨0, by rw [norm_zero]; exact hρ0.le, fun y => by simp⟩
      neg_mem' := by
        rintro Λ ⟨a, ha, h⟩
        refine ⟨-a, by rwa [norm_neg], fun y => ?_⟩
        rw [AddChar.neg_apply, ← QuotientAddGroup.mk_neg, h, AddSubgroup.coe_neg, dotProduct_neg, neg_dotProduct] }
  have hsep : ∀ q : L ⧸ N, q ≠ 0 → ∃ Λ ∈ H, Λ q ≠ 1 := by
    intro q hq
    obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective q
    have hyN : (y : κ → K) ∉ M := fun h => hq ((QuotientAddGroup.eq_zero_iff _).2 h)
    rw [hMmem] at hyN
    push_neg at hyN
    obtain ⟨a, ha, hay⟩ := hyN
    obtain ⟨Λ, hΛ⟩ := exists_lift N (e a) fun z hz => hz a ha
    exact ⟨Λ, ⟨a, ha, fun z => hΛ z⟩, by rw [hΛ]; exact hay⟩
  obtain ⟨a, -, ha⟩ := mem_of_separates H hsep X
  exact ⟨a, fun y hy => (hX ⟨y, hy⟩).symm.trans (ha ⟨y, hy⟩)⟩

end GlobalTheory.CompactCharDual

namespace GlobalTheory.CompactCharDual

theorem exists_dotProduct_eq_local : ∀ {F : Type} [Field F] [NumberField F] (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) {κ : Type} [Fintype κ]
    (ψ₀ : AddChar (Fv F v) ℂ), Continuous ψ₀ → ψ₀ ≠ 1 →
    ∀ L : AddSubgroup (κ → Fv F v), IsCompact (L : Set (κ → Fv F v)) →
    ∀ L' : AddSubgroup (κ → Fv F v), IsOpen (L' : Set (κ → Fv F v)) →
    ∀ χ : (κ → Fv F v) → ℂ, (∀ y ∈ L, ∀ y' ∈ L, χ (y + y') = χ y * χ y') → (∀ y ∈ L, y ∈ L' → χ y = 1) →
    ∃ x₀ : κ → Fv F v, ∀ y ∈ L, χ y = ψ₀ (x₀ ⬝ᵥ y) := by
  intro F _ _ v κ _ ψ₀ hc hne L hL L' hL' χ hmul htriv
  haveI : IsUltrametricDist (Fv F v) := inferInstance
  exact exists_dotProduct_eq ψ₀ hc hne L hL L' hL' χ hmul htriv

end GlobalTheory.CompactCharDual
