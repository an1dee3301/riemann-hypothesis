module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.HilbertSchurUnitaryIrreducibleScalar
public import Init.Classical
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.PropLemmas
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Spectrum.Basic
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.IsApply
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Ker
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Ring.Commute
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Algebra.Star.SelfAdjoint
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unital
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Analysis.Normed.Operator.LinearIsometry
public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import Mathlib.Analysis.Normed.Order.Lattice
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.Real.Star
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Subtype
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.Complex.Module
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Notation
public import Mathlib.Tactic.CancelDenoms.Core
public import Mathlib.Tactic.Linarith.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.Algebra.Star.Real
public import Mathlib.Topology.Algebra.UniformMulAction
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.ContinuousOn
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.GDelta.MetrizableSpace
public import Mathlib.Topology.MetricSpace.Algebra
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.MetricSpace.Defs
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Metrizable.Basic
public import Mathlib.Topology.Metrizable.Uniformity
public import Mathlib.Topology.Order.OrderClosed
public import Mathlib.Topology.Separation.GDelta
public import Mathlib.Topology.Separation.Regular
public import Mathlib.Topology.UniformSpace.Cauchy
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

namespace GlobalTheory

private theorem exists_real_scalar_of_selfAdjoint_commute_irreducible {G H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (σ : G → (H →L[ℂ] H))
    (hirr : ∀ S : Submodule ℂ H, IsClosed (S : Set H) → (∀ g, ∀ v ∈ S, σ g v ∈ S) →
      S = ⊥ ∨ S = ⊤)
    (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (hc : ∀ g, Commute A (σ g)) :
    ∃ c : ℝ, A = algebraMap ℝ (H →L[ℂ] H) c := by
  have key : ∀ x ∈ spectrum ℝ A, ∀ y ∈ spectrum ℝ A, x < y → False := by
    intro x hx y hy hxy
    obtain ⟨m, hxm, hmy⟩ : ∃ m : ℝ, x < m ∧ m < y := ⟨(x + y) / 2, by linarith, by linarith⟩
    have hfc : ContinuousOn (fun t : ℝ => max (t - m) 0) (spectrum ℝ A) :=
      (by fun_prop : Continuous fun t : ℝ => max (t - m) 0).continuousOn
    have hkc : ContinuousOn (fun t : ℝ => max (m - t) 0) (spectrum ℝ A) :=
      (by fun_prop : Continuous fun t : ℝ => max (m - t) 0).continuousOn
    have hprod : cfc (fun t : ℝ => max (t - m) 0) A * cfc (fun t : ℝ => max (m - t) 0) A = 0 := by
      rw [← cfc_mul _ _ A hfc hkc]
      have h0 : (fun t : ℝ => max (t - m) 0 * max (m - t) 0) = (0 : ℝ → ℝ) := by
        funext t
        rcases le_total t m with h | h
        · rw [max_eq_right (by linarith), zero_mul, Pi.zero_apply]
        · rw [max_eq_right (by linarith : m - t ≤ 0), mul_zero, Pi.zero_apply]
      rw [h0, cfc_zero]
    have hk0 : cfc (fun t : ℝ => max (m - t) 0) A ≠ 0 := by
      intro h0
      rw [← cfc_zero ℝ A] at h0
      have h1 := eqOn_of_cfc_eq_cfc h0 hkc continuousOn_const hA hx
      simp only [Pi.zero_apply] at h1
      have h2 : m - x ≤ max (m - x) 0 := le_max_left _ _
      linarith
    obtain ⟨w, hw⟩ : ∃ w, cfc (fun t : ℝ => max (m - t) 0) A w ≠ 0 := by
      by_contra hnot
      simp only [not_exists, not_not] at hnot
      exact hk0 (ContinuousLinearMap.ext hnot)
    let F := cfc (fun t : ℝ => max (t - m) 0) A
    let S : Submodule ℂ H := LinearMap.ker (F : H →ₗ[ℂ] H)
    have hS : IsClosed (S : Set H) := F.isClosed_ker
    have hinv : ∀ g, ∀ v ∈ S, σ g v ∈ S := by
      intro g v hv
      have hv' : F v = 0 := hv
      have hcg : F * σ g = σ g * F := ((hc g).cfc_real _).eq
      change F (σ g v) = 0
      have := congrArg (fun L : H →L[ℂ] H => L v) hcg
      simp only [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply] at this
      rw [this, hv', map_zero]
    have hmem : cfc (fun t : ℝ => max (m - t) 0) A w ∈ S := by
      change F (cfc (fun t : ℝ => max (m - t) 0) A w) = 0
      simpa [F] using congrArg (fun L : H →L[ℂ] H => L w) hprod
    rcases hirr S hS hinv with hbot | htop
    · rw [hbot, Submodule.mem_bot] at hmem
      exact hw hmem
    · have hF : F = 0 := by
        ext v
        have hv : v ∈ S := by rw [htop]; exact Submodule.mem_top
        exact hv
      rw [← cfc_zero ℝ A] at hF
      have h1 := eqOn_of_cfc_eq_cfc hF hfc continuousOn_const hA hy
      simp only [Pi.zero_apply] at h1
      have h2 : y - m ≤ max (y - m) 0 := le_max_left _ _
      linarith
  have hsub : ∃ c : ℝ, ∀ x ∈ spectrum ℝ A, x = c := by
    by_cases hne : (spectrum ℝ A).Nonempty
    · obtain ⟨c, hc'⟩ := hne
      refine ⟨c, fun x hx => ?_⟩
      rcases lt_trichotomy x c with h | h | h
      · exact (key x hx c hc' h).elim
      · exact h
      · exact (key c hc' x hx h).elim
    · exact ⟨0, fun x hx => (hne ⟨x, hx⟩).elim⟩
  obtain ⟨c, hc'⟩ := hsub
  refine ⟨c, ?_⟩
  calc A = cfc (id : ℝ → ℝ) A := (cfc_id ℝ A hA).symm
    _ = cfc (fun _ : ℝ => c) A := cfc_congr fun x hx => hc' x hx
    _ = algebraMap ℝ (H →L[ℂ] H) c := cfc_const c A hA

theorem hilbert_schur_of_adjoint_closed :
    ∀ (G H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : G → (H →L[ℂ] H)), (∀ g, ∃ g', σ g' = ContinuousLinearMap.adjoint (σ g)) → (∀ S : Submodule ℂ H, IsClosed (S : Set H) → (∀ g, ∀ v ∈ S, σ g v ∈ S) → S = ⊥ ∨ S = ⊤) → ∀ T : H →L[ℂ] H, (∀ g, T ∘L σ g = σ g ∘L T) → ∃ c : ℂ, T = c • (1 : H →L[ℂ] H) := by
  intro G H _ _ _ σ hadj hirr T hT
  have hcomm : ∀ g, Commute T (σ g) := fun g => hT g
  have hcomm' : ∀ g, Commute (star T) (σ g) := by
    intro g
    obtain ⟨g', hg'⟩ := hadj g
    have h1 := congrArg star (hcomm g').eq
    rw [star_mul, star_mul, hg', ← ContinuousLinearMap.star_eq_adjoint, star_star] at h1
    exact h1.symm
  obtain ⟨a, ha⟩ := exists_real_scalar_of_selfAdjoint_commute_irreducible σ hirr (realPart T : H →L[ℂ] H)
    (realPart T).prop fun g => by
      rw [realPart_apply_coe]
      exact ((hcomm g).add_left (hcomm' g)).smul_left _
  obtain ⟨b, hb⟩ := exists_real_scalar_of_selfAdjoint_commute_irreducible σ hirr (imaginaryPart T : H →L[ℂ] H)
    (imaginaryPart T).prop fun g => by
      rw [imaginaryPart_apply_coe]
      exact (((hcomm g).sub_left (hcomm' g)).smul_left _).smul_left _
  refine ⟨(a : ℂ) + Complex.I * b, ?_⟩
  calc T = (realPart T : H →L[ℂ] H) + Complex.I • (imaginaryPart T : H →L[ℂ] H) :=
        (realPart_add_I_smul_imaginaryPart T).symm
    _ = ((a : ℂ) + Complex.I * b) • (1 : H →L[ℂ] H) := by
        rw [ha, hb, Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, add_smul,
          mul_smul, ← Complex.coe_smul, ← Complex.coe_smul]

end GlobalTheory
