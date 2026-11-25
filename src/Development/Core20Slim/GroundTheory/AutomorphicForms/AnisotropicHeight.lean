module

public import Mathlib
public import Development.Core20Slim.GroundTheory.AutomorphicForms.AnisotropicOrbit
public import Development.Core20Slim.GroundTheory.AutomorphicForms.AdelicUnitaryGroups
public import Development.Core20Slim.GroundTheory.AutomorphicForms.ReductionHeight
public import Init.Classical
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Group.WithOne.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Pi
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Notation.Support
public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.ZeroLEOne
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.WithAbs
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.MulAction
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.Analysis.Normed.Ring.WithAbs
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Lattice.Basic
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Lattice
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Logic.Function.Basic
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Filter.Cofinite
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.Filter.Finite
public import Mathlib.Order.Lattice
public import Mathlib.Order.MinMax
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Positivity.Core
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Valued.NormedValued
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.MetricSpace.Ultra.Basic

@[expose] public section

set_option maxSynthPendingDepth 1

open NumberField IsDedekindDomain Topology Set Matrix Filter
open scoped NumberField.AdeleRing

namespace GroundTheory.Automorphic

noncomputable section

namespace Anisotropic

section Local

variable {F : Type*} [NormedField F] {N m d : ℕ}

theorem norm_le_mul_pow_of_homogeneous (hd : 0 < d) (Φ : (Fin N → F) → Fin m → F)
    (hΦ : ∀ (t : F) y, Φ (t • y) = t ^ d • Φ y) {B : ℝ} (hB : ∀ y, ‖y‖ ≤ 1 → ‖Φ y‖ ≤ B)
    (y : Fin N → F) : ‖Φ y‖ ≤ B * ‖y‖ ^ d := by
  by_cases hy : y = 0
  · have h0 : Φ 0 = 0 := by
      have := hΦ 0 0
      rwa [zero_smul, zero_pow hd.ne', zero_smul] at this
    rw [hy, h0, norm_zero, norm_zero, zero_pow hd.ne', mul_zero]
  · obtain ⟨j, -⟩ := Function.ne_iff.1 hy
    have : Nonempty (Fin N) := ⟨j⟩
    obtain ⟨i, hi⟩ := Finite.exists_max fun i => ‖y i‖
    have hyi : ‖y‖ = ‖y i‖ :=
      le_antisymm ((pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 hi) (norm_le_pi_norm y i)
    have ht : y i ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at hyi
      exact hy (norm_eq_zero.1 hyi)
    have hy' : ‖(y i)⁻¹ • y‖ ≤ 1 := by
      rw [norm_smul, norm_inv, hyi, inv_mul_cancel₀ (norm_ne_zero_iff.2 ht)]
    have hyy : y = y i • ((y i)⁻¹ • y) := by rw [smul_smul, mul_inv_cancel₀ ht, one_smul]
    calc ‖Φ y‖ = ‖y i‖ ^ d * ‖Φ ((y i)⁻¹ • y)‖ := by
          conv_lhs => rw [hyy]
          rw [hΦ, norm_smul, norm_pow]
      _ ≤ ‖y i‖ ^ d * B := mul_le_mul_of_nonneg_left (hB _ hy') (pow_nonneg (norm_nonneg _) _)
      _ = B * ‖y‖ ^ d := by rw [hyi, mul_comm]

variable {K : Type*} [Field K] [Algebra K F]

theorem norm_aeval_le_sum (p : MvPolynomial (Fin N) K) (y : Fin N → F) (hy : ‖y‖ ≤ 1) :
    ‖MvPolynomial.aeval y p‖ ≤ ∑ s ∈ p.support, ‖algebraMap K F (p.coeff s)‖ := by
  rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun s _ => ?_)
  rw [norm_mul]
  refine mul_le_of_le_one_right (norm_nonneg _) ?_
  rw [norm_prod]
  refine Finset.prod_le_one₀ (fun i _ => norm_nonneg _) fun i _ => ?_
  rw [norm_pow]
  exact pow_le_one₀ (norm_nonneg _) ((norm_le_pi_norm y i).trans hy)

theorem norm_aeval_le_one [IsUltrametricDist F] (p : MvPolynomial (Fin N) K)
    (hp : ∀ s ∈ p.support, ‖algebraMap K F (p.coeff s)‖ ≤ 1) (y : Fin N → F) (hy : ‖y‖ ≤ 1) :
    ‖MvPolynomial.aeval y p‖ ≤ 1 := by
  rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun s hs => ?_
  rw [norm_mul, norm_prod]
  exact mul_le_one₀ (hp s hs) (Finset.prod_nonneg fun _ _ => norm_nonneg _)
    (Finset.prod_le_one₀ (fun i _ => norm_nonneg _) fun i _ => by
      rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) ((norm_le_pi_norm y i).trans hy))

end Local

variable {K : Type*} [Field K] [NumberField K] {N m d : ℕ}

theorem exists_adelicNorm_le_mul_pow (hd : 0 < d) (Φ : (Fin N → 𝔸[K]) → Fin m → 𝔸[K])
    (Φv : ∀ v : HeightOneSpectrum (𝓞 K), (Fin N → v.adicCompletion K) → Fin m → v.adicCompletion K)
    (Φw : ∀ w : InfinitePlace K, (Fin N → w.Completion) → Fin m → w.Completion)
    (hv : ∀ v y, Reduction.finComp v (Φ y) = Φv v (Reduction.finComp v y))
    (hw : ∀ w y, Reduction.infComp w (Φ y) = Φw w (Reduction.infComp w y))
    (hvh : ∀ v (t : v.adicCompletion K) y, Φv v (t • y) = t ^ d • Φv v y)
    (hwh : ∀ w (t : w.Completion) y, Φw w (t • y) = t ^ d • Φw w y)
    (hvB : ∀ v, ∃ B : ℝ, ∀ y, ‖y‖ ≤ 1 → ‖Φv v y‖ ≤ B)
    (hv1 : ∀ᶠ v in cofinite, ∀ y, ‖y‖ ≤ 1 → ‖Φv v y‖ ≤ 1)
    (hwB : ∀ w, ∃ B : ℝ, ∀ y, ‖y‖ ≤ 1 → ‖Φw w y‖ ≤ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ y, Reduction.HasFiniteContent y → Reduction.HasFiniteContent (Φ y) →
      Reduction.adelicNorm (Φ y) ≤ C * Reduction.adelicNorm y ^ d := by
  classical
  choose Bv hBv using hvB
  choose Bw hBw using hwB
  set S := (Filter.eventually_cofinite.1 hv1).toFinset with hS
  let Bf : HeightOneSpectrum (𝓞 K) → ℝ := fun v => if v ∈ S then max 1 (Bv v) else 1
  have hBf1 : ∀ v, 1 ≤ Bf v := fun v => by
    simp only [Bf]
    split_ifs
    · exact le_max_left _ _
    · exact le_rfl
  have hBf : ∀ v y, ‖y‖ ≤ 1 → ‖Φv v y‖ ≤ Bf v := by
    intro v y hy
    simp only [Bf]
    split_ifs with h
    · exact (hBv v y hy).trans (le_max_right _ _)
    · have : v ∉ {v | ¬∀ y, ‖y‖ ≤ 1 → ‖Φv v y‖ ≤ 1} := by
        rwa [hS, Set.Finite.mem_toFinset] at h
      simp only [Set.mem_ofPred_eq, not_not] at this
      exact this y hy
  let cw : InfinitePlace K → ℝ := fun w => max 1 √(m : ℝ) * max 1 (Bw w)
  have hcw1 : ∀ w, 1 ≤ cw w := fun w =>
    one_le_mul_of_one_le_of_one_le (le_max_left _ _) (le_max_left _ _)
  have hloc_w : ∀ w (z : Fin N → w.Completion),
      Reduction.euclidNorm (Φw w z) ≤ cw w * Reduction.euclidNorm z ^ d := by
    intro w z
    have h1 := norm_le_mul_pow_of_homogeneous hd (Φw w) (hwh w) (B := max 1 (Bw w))
      (fun y hy => (hBw w y hy).trans (le_max_right _ _)) z
    calc Reduction.euclidNorm (Φw w z) ≤ √(m : ℝ) * ‖Φw w z‖ := Reduction.euclidNorm_le_sqrt_mul _
      _ ≤ max 1 √(m : ℝ) * (max 1 (Bw w) * ‖z‖ ^ d) :=
          mul_le_mul (le_max_right _ _) h1 (norm_nonneg _) (by positivity)
      _ ≤ max 1 √(m : ℝ) * (max 1 (Bw w) * Reduction.euclidNorm z ^ d) := by
          gcongr
          exact Reduction.norm_le_euclidNorm_pi z
      _ = cw w * Reduction.euclidNorm z ^ d := by simp only [cw]; ring
  have hloc_v : ∀ v (z : Fin N → v.adicCompletion K), ‖Φv v z‖ ≤ Bf v * ‖z‖ ^ d :=
    fun v z => norm_le_mul_pow_of_homogeneous hd (Φv v) (hvh v) (hBf v) z
  refine ⟨(∏ w, cw w ^ w.mult) * ∏ v ∈ S, Bf v, ?_, ?_⟩
  · exact mul_pos (Finset.prod_pos fun w _ => pow_pos (zero_lt_one.trans_le (hcw1 w)) _)
      (Finset.prod_pos fun v _ => zero_lt_one.trans_le (hBf1 v))
  intro y hy hΦy
  set T := S ∪ hy.finite_mulSupport.toFinset ∪ hΦy.finite_mulSupport.toFinset with hT
  have hfinΦ : ∏ᶠ v, ‖Reduction.finComp v (Φ y)‖ = ∏ v ∈ T, ‖Reduction.finComp v (Φ y)‖ :=
    finprod_eq_prod_of_mulSupport_subset _ (by
      intro v hv'
      simp only [hT, Finset.coe_union, Set.Finite.coe_toFinset]
      exact Or.inr hv')
  have hfiny : ∏ᶠ v, ‖Reduction.finComp v y‖ = ∏ v ∈ T, ‖Reduction.finComp v y‖ :=
    finprod_eq_prod_of_mulSupport_subset _ (by
      intro v hv'
      simp only [hT, Finset.coe_union, Set.Finite.coe_toFinset]
      exact Or.inl (Or.inr hv'))
  have hST : ∏ v ∈ T, Bf v = ∏ v ∈ S, Bf v := by
    refine (Finset.prod_subset (fun v hv' => ?_) fun v _ hvS => ?_).symm
    · rw [hT, Finset.mem_union, Finset.mem_union]
      exact Or.inl (Or.inl hv')
    · simp only [Bf, if_neg hvS]
  have hfin_le : ∏ᶠ v, ‖Reduction.finComp v (Φ y)‖ ≤
      (∏ v ∈ S, Bf v) * (∏ᶠ v, ‖Reduction.finComp v y‖) ^ d := by
    rw [hfinΦ, hfiny, ← hST, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
    refine Finset.prod_le_prod₀ (fun v _ => norm_nonneg _) fun v _ => ?_
    rw [hv]
    exact hloc_v v _
  have hinf_le : ∏ w, Reduction.euclidNorm (Reduction.infComp w (Φ y)) ^ w.mult ≤
      (∏ w, cw w ^ w.mult) * (∏ w, Reduction.euclidNorm (Reduction.infComp w y) ^ w.mult) ^ d := by
    rw [← Finset.prod_pow, ← Finset.prod_mul_distrib]
    refine Finset.prod_le_prod₀ (fun w _ => pow_nonneg (Reduction.euclidNorm_nonneg _) _)
      fun w _ => ?_
    rw [hw]
    calc Reduction.euclidNorm (Φw w (Reduction.infComp w y)) ^ w.mult
        ≤ (cw w * Reduction.euclidNorm (Reduction.infComp w y) ^ d) ^ w.mult :=
          pow_le_pow_left₀ (Reduction.euclidNorm_nonneg _) (hloc_w w _) _
      _ = cw w ^ w.mult * (Reduction.euclidNorm (Reduction.infComp w y) ^ w.mult) ^ d := by ring
  unfold Reduction.adelicNorm
  calc _ ≤ ((∏ w, cw w ^ w.mult) *
          (∏ w, Reduction.euclidNorm (Reduction.infComp w y) ^ w.mult) ^ d) *
        ((∏ v ∈ S, Bf v) * (∏ᶠ v, ‖Reduction.finComp v y‖) ^ d) :=
        mul_le_mul hinf_le hfin_le (finprod_nonneg fun _ => norm_nonneg _)
          (mul_nonneg (Finset.prod_nonneg fun w _ => pow_nonneg (zero_le_one.trans (hcw1 w)) _)
            (pow_nonneg (Finset.prod_nonneg fun w _ =>
              pow_nonneg (Reduction.euclidNorm_nonneg _) _) _))
    _ = _ := by ring

theorem exists_adelicNorm_aeval_le (hd : 0 < d) (P : Fin m → MvPolynomial (Fin N) K)
    (hvh : ∀ (v : HeightOneSpectrum (𝓞 K)) (t : v.adicCompletion K)
      (y : Fin N → v.adicCompletion K) k,
      MvPolynomial.aeval (t • y) (P k) = t ^ d * MvPolynomial.aeval y (P k))
    (hwh : ∀ (w : InfinitePlace K) (t : w.Completion) (y : Fin N → w.Completion) k,
      MvPolynomial.aeval (t • y) (P k) = t ^ d * MvPolynomial.aeval y (P k)) :
    ∃ C : ℝ, 0 < C ∧ ∀ y : Fin N → 𝔸[K], Reduction.HasFiniteContent y →
      Reduction.HasFiniteContent (fun k => MvPolynomial.aeval y (P k)) →
      Reduction.adelicNorm (fun k => MvPolynomial.aeval y (P k)) ≤
        C * Reduction.adelicNorm y ^ d := by
  refine exists_adelicNorm_le_mul_pow hd _ (fun v y k => MvPolynomial.aeval y (P k))
    (fun w y k => MvPolynomial.aeval y (P k)) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro v y
    funext k
    show adeleFiniteEval K v (MvPolynomial.aeval y (P k)) = _
    rw [MvPolynomial.comp_aeval_apply]
    rfl
  · intro w y
    funext k
    show adeleInfiniteEval K w (MvPolynomial.aeval y (P k)) = _
    rw [MvPolynomial.comp_aeval_apply]
    rfl
  · intro v t y
    funext k
    simp only [Pi.smul_apply, smul_eq_mul]
    exact hvh v t y k
  · intro w t y
    funext k
    simp only [Pi.smul_apply, smul_eq_mul]
    exact hwh w t y k
  · intro v
    refine ⟨∑ k, ∑ s ∈ (P k).support, ‖algebraMap K (v.adicCompletion K) ((P k).coeff s)‖,
      fun y hy => (pi_norm_le_iff_of_nonneg (by positivity)).2 fun k => ?_⟩
    exact (norm_aeval_le_sum (P k) y hy).trans
      (Finset.single_le_sum (f := fun k => ∑ s ∈ (P k).support,
        ‖algebraMap K (v.adicCompletion K) ((P k).coeff s)‖)
        (fun k _ => by positivity) (Finset.mem_univ k))
  · have h : ∀ᶠ v : HeightOneSpectrum (𝓞 K) in cofinite, ∀ k, ∀ s ∈ (P k).support,
        ‖algebraMap K (v.adicCompletion K) ((P k).coeff s)‖ ≤ 1 :=
      Filter.eventually_all.2 fun k => (Filter.eventually_all_finset _).2 fun s _ =>
        Reduction.eventually_norm_le_one _
    filter_upwards [h] with v hv y hy
    exact (pi_norm_le_iff_of_nonneg zero_le_one).2 fun k => norm_aeval_le_one (P k) (hv k) y hy
  · intro w
    refine ⟨∑ k, ∑ s ∈ (P k).support, ‖algebraMap K w.Completion ((P k).coeff s)‖,
      fun y hy => (pi_norm_le_iff_of_nonneg (by positivity)).2 fun k => ?_⟩
    exact (norm_aeval_le_sum (P k) y hy).trans
      (Finset.single_le_sum (f := fun k => ∑ s ∈ (P k).support,
        ‖algebraMap K w.Completion ((P k).coeff s)‖)
        (fun k _ => by positivity) (Finset.mem_univ k))

end Anisotropic

end

end GroundTheory.Automorphic
