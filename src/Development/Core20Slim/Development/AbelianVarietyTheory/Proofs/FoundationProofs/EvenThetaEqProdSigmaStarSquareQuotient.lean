module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Formalism.PairingDivisors.StatementH
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OddThetaFunctionExistenceUniqueness
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.FoundationProofs.DifferentiableSqTh
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsEntireOfLocallyDvd
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsWpFEq
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Init.Classical
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Int.Lemmas
public import Init.Data.Int.Order
public import Init.Data.List.Basic
public import Init.Data.List.Perm
public import Init.Data.Nat.Basic
public import Init.Data.Order.Lemmas
public import Init.Data.Zero
public import Init.GetElem
public import Init.Omega.Coeffs
public import Init.Omega.Constraint
public import Init.Omega.Int
public import Init.Omega.LinearCombo
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Multiset.Defs
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Subsemigroup.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.ZLattice.Basic
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import Mathlib.Algebra.Polynomial.Degree.Operations
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Polynomial.Monic
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Polynomial.Splits
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.FDeriv.Pow
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Multiset.Defs
public import Mathlib.Data.Multiset.MapFold
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.Order.Basic
public import Mathlib.Order.Notation
public import Mathlib.Order.RelClasses
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Tactic.LinearCombination.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Closure
public import Mathlib.Topology.MetricSpace.Bounded
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

namespace GlobalTheory.EvenTheta

open Polynomial

variable {Λ : AddSubgroup ℂ}

theorem IsLat.wpF_add_of_mem (h : IsLat Λ) {ω : ℂ} (hω : ω ∈ Λ) (z : ℂ) :
    wpF Λ (z + ω) = wpF Λ z := by
  obtain ⟨L, hL⟩ := GlobalTheory.OddTheta.exists_periodPair Λ h
  rw [GlobalTheory.OddTheta.wpF_eq L Λ hL, GlobalTheory.OddTheta.wpF_eq L Λ hL]
  exact L.weierstrassP_add_coe z ⟨ω, (hL ω).1 hω⟩

theorem IsLat.entire_eq_of_periodic (h : IsLat Λ) {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    (hper : ∀ ω ∈ Λ, ∀ z, F (z + ω) = F z) (z : ℂ) : F z = F 0 := by
  obtain ⟨L, hL⟩ := GlobalTheory.OddTheta.exists_periodPair Λ h
  exact hF.apply_eq_apply_of_bounded
    (IsZLattice.isCompact_range_of_periodic L.lattice _ hF.continuous
      fun z w hw => hper w ((hL w).2 hw) z).isBounded z 0

theorem IsLat.sqTh_law (h : IsLat Λ) {v : ℂ} (hv : v ∉ Λ) {ω : ℂ} (hω : ω ∈ Λ) (z : ℂ) :
    sqTh Λ v (z + ω) * sgStar Λ z ^ 2 = sqTh Λ v z * sgStar Λ (z + ω) ^ 2 := by
  by_cases hz : z ∈ Λ
  · rw [(h.sg_eq_zero z).2 hz, (h.sg_eq_zero _).2 (add_mem hz hω)]
    simp
  · have hz' : z + ω ∉ Λ := fun h' => hz (by simpa using sub_mem h' hω)
    rw [h.sqTh_eq hv hz, h.sqTh_eq hv hz', h.wpF_add_of_mem hω]
    ring

theorem IsLat.exists_poly_wp (h : IsLat Λ) (k : ℕ) : ∀ F : ℂ → ℂ, Differentiable ℂ F →
    (∀ z, F (-z) = F z) →
    (∀ ω ∈ Λ, ∀ z, F (z + ω) * sgStar Λ z ^ (2 * k) = F z * sgStar Λ (z + ω) ^ (2 * k)) →
    ∃ P : ℂ[X], P.natDegree ≤ k ∧ P.coeff k = F 0 ∧
      ∀ z ∉ Λ, F z = sgStar Λ z ^ (2 * k) * P.eval (wpF Λ z) := by
  induction k with
  | zero =>
    intro F hF _ hlaw
    refine ⟨C (F 0), by simp, by simp, fun z _ => ?_⟩
    simpa using h.entire_eq_of_periodic hF (fun ω hω z => by simpa using hlaw ω hω z) z
  | succ k ih =>
    intro F hF he hlaw
    obtain ⟨v, hv⟩ := h.dense_compl.nonempty
    have hv : v ∉ Λ := hv
    have hd := h.differentiable_sqTh v
    obtain ⟨G, hG, hGe, hFG, hGl⟩ := GlobalTheory.EvenTheta.exists_eq_sg_sq_mul Λ h k
      (fun z => F z - F 0 * sqTh Λ v z ^ (k + 1)) (by fun_prop)
      (fun z => by simp only [he, sqTh_neg]) (by simp [h.sqTh_zero hv])
      (fun ω hω z => by
        have h1 := congrArg (· ^ (k + 1)) (h.sqTh_law hv hω z)
        simp only [mul_pow, ← pow_mul] at h1
        linear_combination hlaw ω hω z - F 0 * h1)
    obtain ⟨P, hP, -, hPG⟩ := ih G hG hGe hGl
    have hm : ((X - C (wpF Λ v)) ^ (k + 1) : ℂ[X]).Monic := (monic_X_sub_C _).pow _
    have hdeg : ((X - C (wpF Λ v)) ^ (k + 1) : ℂ[X]).natDegree = k + 1 := by
      rw [(monic_X_sub_C _).natDegree_pow, natDegree_X_sub_C, mul_one]
    refine ⟨C (F 0) * (X - C (wpF Λ v)) ^ (k + 1) + P, ?_, ?_, fun z hz => ?_⟩
    · refine natDegree_add_le_of_degree_le ((natDegree_C_mul_le _ _).trans hdeg.le) (by omega)
    · have h1 := hm.coeff_natDegree
      rw [hdeg] at h1
      rw [coeff_add, coeff_C_mul, h1, coeff_eq_zero_of_natDegree_lt (by omega : P.natDegree < k + 1)]
      simp
    · have h1 := hFG z
      simp only [hPG z hz, h.sqTh_eq hv hz, mul_pow, ← pow_mul] at h1
      simp only [eval_add, eval_mul, eval_C, eval_pow, eval_sub, eval_X]
      linear_combination h1

theorem exists_eval_eq_prod_fin {k : ℕ} {P : ℂ[X]} (hP : P.natDegree ≤ k) (h1 : P.coeff k = 1) :
    ∃ r : Fin k → ℂ, ∀ x, P.eval x = ∏ i, (x - r i) := by
  have hdeg : P.natDegree = k := natDegree_eq_of_le_of_coeff_ne_zero hP (by rw [h1]; exact one_ne_zero)
  have hm : P.Monic := by rw [Monic, leadingCoeff, hdeg, h1]
  have hs : P.Splits := IsAlgClosed.splits P
  have he := hs.eq_prod_roots_of_monic hm
  have hc := hs.natDegree_eq_card_roots
  obtain ⟨l, hl⟩ := Quotient.exists_rep P.roots
  have hl : (l : Multiset ℂ) = P.roots := hl
  rw [← hl] at he hc
  rw [hdeg, Multiset.coe_card] at hc
  subst hc
  refine ⟨fun i => l[i.1]'i.2, fun x => ?_⟩
  rw [he, eval_multiset_prod, Multiset.map_map, Multiset.map_coe, Multiset.prod_coe]
  simp only [Function.comp_def, eval_sub, eval_X, eval_C]
  exact (Fin.prod_univ_fun_getElem l fun a => x - a).symm

theorem exists_eq_prod_sqTh : ∀ Λ : AddSubgroup ℂ, IsLat Λ → ∀ (k : ℕ) (F : ℂ → ℂ), Differentiable ℂ F → (∀ z, F (-z) = F z) → F 0 = 1 → (∀ ω ∈ Λ, ∀ z, F (z + ω) * sgStar Λ z ^ (2 * k) = F z * sgStar Λ (z + ω) ^ (2 * k)) → ∃ Q : Fin k → ℂ, (∀ i, Q i ∉ Λ) ∧ ∀ z, F z = ∏ i, sqTh Λ (Q i) z := by
  intro Λ h k F hF he h0 hlaw
  obtain ⟨P, hP, hc, hPF⟩ := h.exists_poly_wp k F hF he hlaw
  obtain ⟨r, hr⟩ := exists_eval_eq_prod_fin hP (hc.trans h0)
  choose Q hQ hQr using fun i => GlobalTheory.EvenTheta.exists_wpF_eq Λ h (r i)
  refine ⟨Q, hQ, fun z => ?_⟩
  refine congrFun (Continuous.ext_on h.dense_compl hF.continuous
    (g := fun z => ∏ i, sqTh Λ (Q i) z)
    (continuous_finsetProd _ fun i _ => (h.differentiable_sqTh (Q i)).continuous) fun z hz => ?_) z
  have hz : z ∉ Λ := hz
  beta_reduce
  simp only [h.sqTh_eq (hQ _) hz, hQr, hPF z hz, hr, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, ← pow_mul]

end GlobalTheory.EvenTheta
