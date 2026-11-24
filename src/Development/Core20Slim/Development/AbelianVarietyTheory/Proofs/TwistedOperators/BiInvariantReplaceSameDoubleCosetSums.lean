module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLenOfLatLen
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.FiniteCosetsInDoset
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.HeckeActMem
public import Formalism.SatakeDualWeyl.Statement
public import Init.Classical
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Order.Lemmas
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Notation.Indicator
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Notation.Support
public import Mathlib.Algebra.Quotient
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.InfiniteSum
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Normed.Order.Lattice
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.IsEmpty.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Quot
public import Mathlib.Data.Set.Basic
public import Mathlib.Data.Set.CoeSort
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.GroupTheory.Coset.Defs
public import Mathlib.GroupTheory.DoubleCoset
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Logic.Equiv.Sum
public import Mathlib.Order.RelClasses
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Constructions
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import Mathlib.Topology.Algebra.InfiniteSum.Group
public import Mathlib.Topology.Algebra.InfiniteSum.Order
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Topology.Algebra.InfiniteSum.Ring
public import Mathlib.Topology.Algebra.InfiniteSum.SummationFilter
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Metrizable.Basic
public import Mathlib.Topology.Metrizable.Uniformity
public import Mathlib.Topology.Separation.CompletelyRegular
public import Mathlib.Topology.UniformSpace.Defs
public import Mathlib.Topology.UniformSpace.Uniformizable

@[expose] public section

open GlobalTheory.InertZeta

noncomputable section

namespace GlobalTheory.InertZeta

open Formalism.UG

section DosetSwapProof

variable {G : Type} [Group G] {K : Subgroup G}

def dosetOf (K : Subgroup G) (x : G ⧸ K) : Set G :=
  DoubleCoset.doubleCoset x.out (K : Set G) (K : Set G)

theorem mem_dosetOf_iff {x y : G ⧸ K} :
    y.out ∈ DoubleCoset.doubleCoset x.out (K : Set G) (K : Set G) ↔ dosetOf K y = dosetOf K x := by
  constructor
  · intro h
    exact DoubleCoset.doubleCoset_eq_of_mem h
  · intro h
    unfold dosetOf at h
    rw [← h]
    exact DoubleCoset.mem_doubleCoset_self K K _

theorem exists_of_dosetOf_eq {x y : G ⧸ K} (h : dosetOf K y = dosetOf K x) :
    ∃ a b : K, y.out = (a : G) * x.out * b := by
  obtain ⟨a, ha, b, hb, e⟩ := DoubleCoset.mem_doubleCoset.1 (mem_dosetOf_iff.2 h)
  exact ⟨⟨a, ha⟩, ⟨b, hb⟩, e⟩

theorem finite_dosetOf_fibre (hK : IsCommensurated K) (S : Set G) :
    Finite {x : G ⧸ K // dosetOf K x = S} := by
  by_cases h : ∃ x₀ : G ⧸ K, dosetOf K x₀ = S
  · obtain ⟨x₀, rfl⟩ := h
    have hf := Formalism.UG.P.finite_cosets_in_doset hK x₀.out
    have hs : {x : G ⧸ K | dosetOf K x = dosetOf K x₀} ⊆ {x : G ⧸ K | ∃ a b : K, x.out = (a : G) * x₀.out * b} :=
      fun y hy => exists_of_dosetOf_eq hy
    exact (hf.subset hs).to_subtype
  · haveI : IsEmpty {x : G ⧸ K // dosetOf K x = S} := ⟨fun y => h ⟨y.1, y.2⟩⟩
    infer_instance

theorem biInv_of_dosetOf_eq {F : G → ℂ} (hF : IsBiInv K F) {x y : G ⧸ K} (h : dosetOf K y = dosetOf K x) :
    F y.out = F x.out := by
  obtain ⟨a, b, e⟩ := exists_of_dosetOf_eq h
  rw [e, hF a b]

theorem hAct_dosetInd_eq (hK : IsCommensurated K) (x₀ : G ⧸ K) (v : G → ℂ) :
    hAct K (dosetInd ℂ K x₀.out) v 1 = ∑' y : {x : G ⧸ K // dosetOf K x = dosetOf K x₀}, v y.1.out := by
  set s : Set (G ⧸ K) := {x | dosetOf K x = dosetOf K x₀} with hs
  have e : ∀ x : G ⧸ K, dosetInd ℂ K x₀.out x.out • v (1 * x.out) = s.indicator (fun x => v x.out) x := by
    intro x
    by_cases h : dosetOf K x = dosetOf K x₀
    · have h' := mem_dosetOf_iff.2 h
      have hx : x ∈ s := h
      simp [dosetInd, Set.indicator_of_mem h', Set.indicator_of_mem hx]
    · have h' : x.out ∉ DoubleCoset.doubleCoset x₀.out (K : Set G) (K : Set G) := fun h' => h (mem_dosetOf_iff.1 h')
      have hx : x ∉ s := h
      simp [dosetInd, Set.indicator_of_notMem h', Set.indicator_of_notMem hx]
  have hfin : s.Finite := Set.finite_coe_iff.1 (finite_dosetOf_fibre hK (dosetOf K x₀))
  rw [hAct, finsum_congr e, ← tsum_eq_finsum (L := SummationFilter.unconditional (G ⧸ K)) ((hfin.subset (Set.support_indicator_subset)))]
  rw [← tsum_subtype]
  rfl

end DosetSwapProof

theorem dosetSwap : DosetSwap := by
  intro G _ K hK F w φ Z hF hw hH hZ
  haveI : ∀ S : Set G, Finite {x : G ⧸ K // dosetOf K x = S} := finite_dosetOf_fibre hK
  let e := Equiv.sigmaFiberEquiv (dosetOf K)
  let f₁ : G ⧸ K → ℂ := fun x => F x.out * φ x.out
  let f₂ : G ⧸ K → ℂ := fun x => F x.out * w x.out
  have hs : ∀ S : Set G, ∑' y : {x : G ⧸ K // dosetOf K x = S}, f₂ y.1 =
      ∑' y : {x : G ⧸ K // dosetOf K x = S}, f₁ y.1 := by
    intro S
    by_cases h : ∃ x₀ : G ⧸ K, dosetOf K x₀ = S
    · obtain ⟨x₀, rfl⟩ := h
      have e₂ : ∀ y : {x : G ⧸ K // dosetOf K x = dosetOf K x₀}, f₂ y.1 = F x₀.out * w y.1.out :=
        fun y => by simp only [f₂, biInv_of_dosetOf_eq hF y.2]
      have e₁ : ∀ y : {x : G ⧸ K // dosetOf K x = dosetOf K x₀}, f₁ y.1 = F x₀.out * φ y.1.out :=
        fun y => by simp only [f₁, biInv_of_dosetOf_eq hF y.2]
      rw [tsum_congr e₂, tsum_congr e₁, tsum_mul_left, tsum_mul_left, ← hAct_dosetInd_eq hK,
        ← hAct_dosetInd_eq hK, hH]
    · haveI : IsEmpty {x : G ⧸ K // dosetOf K x = S} := ⟨fun y => h ⟨y.1, y.2⟩⟩
      simp [tsum_empty]
  have hn : ∀ S : Set G, ∑' y : {x : G ⧸ K // dosetOf K x = S}, ‖f₂ y.1‖ ≤
      ∑' y : {x : G ⧸ K // dosetOf K x = S}, ‖f₁ y.1‖ := by
    intro S
    by_cases h : ∃ x₀ : G ⧸ K, dosetOf K x₀ = S
    · obtain ⟨x₀, hx₀⟩ := h
      have c : ∀ y : {x : G ⧸ K // dosetOf K x = S}, f₂ y.1 = F x₀.out * w x₀.out := fun y => by
        have hy : dosetOf K y.1 = dosetOf K x₀ := y.2.trans hx₀.symm
        simp only [f₂, biInv_of_dosetOf_eq hF hy, biInv_of_dosetOf_eq hw hy]
      have key : ∑' y : {x : G ⧸ K // dosetOf K x = S}, ‖f₂ y.1‖ =
          ‖∑' y : {x : G ⧸ K // dosetOf K x = S}, f₂ y.1‖ := by
        rw [tsum_congr (fun y => congrArg norm (c y)), tsum_congr c, tsum_const, tsum_const, nsmul_eq_mul,
          nsmul_eq_mul]
        simp [norm_mul]
      rw [key, hs]
      exact norm_tsum_le_tsum_norm Summable.of_finite
    · haveI : IsEmpty {x : G ⧸ K // dosetOf K x = S} := ⟨fun y => h ⟨y.1, y.2⟩⟩
      simp [tsum_empty]
  have h₁ : HasSum (f₁ ∘ e) Z := (e.hasSum_iff).2 hZ
  have h₁n : Summable fun p => ‖(f₁ ∘ e) p‖ := summable_norm_iff.2 h₁.summable
  have h₂n : Summable fun p => ‖(f₂ ∘ e) p‖ := by
    rw [summable_sigma_of_nonneg (fun _ => norm_nonneg _)] at h₁n ⊢
    refine ⟨fun S => Summable.of_finite, ?_⟩
    exact h₁n.2.of_nonneg_of_le (fun _ => tsum_nonneg fun _ => norm_nonneg _) hn
  have h₂ : Summable (f₂ ∘ e) := summable_norm_iff.1 h₂n
  have A := h₂.hasSum.sigma (fun S => (Summable.of_finite).hasSum)
  have B := h₁.sigma (fun S => (Summable.of_finite).hasSum)
  have hZ' : ∑' p, (f₂ ∘ e) p = Z := by
    refine A.unique ?_
    have : (fun S => ∑' c : {x : G ⧸ K // dosetOf K x = S}, (f₂ ∘ e) ⟨S, c⟩) =
        fun S => ∑' c : {x : G ⧸ K // dosetOf K x = S}, (f₁ ∘ e) ⟨S, c⟩ := funext hs
    rw [this]
    exact B
  have := h₂.hasSum
  rw [hZ', e.hasSum_iff] at this
  exact this

end GlobalTheory.InertZeta

end
