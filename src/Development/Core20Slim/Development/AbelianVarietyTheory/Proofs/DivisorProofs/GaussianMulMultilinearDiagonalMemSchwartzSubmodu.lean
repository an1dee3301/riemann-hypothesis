module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowForm
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GaussianIsSchwartzFunction
public import Init.Classical
public import Init.Core
public import Init.Data.Fin.Basic
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.NeZero
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Submodule.Basic
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.Ring.Unbundled.Basic
public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.Distribution.TemperateGrowth
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Complex.BigOperators
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.IsEmpty.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.Real.Star
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.BooleanAlgebra
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Empty
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Logic.Function.Defs
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Tactic.Linarith.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.Algebra.Module.Multilinear.Basic
public import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.Instances.RealVectorSpace
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Metrizable.Basic
public import Mathlib.Topology.Metrizable.Uniformity
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open MeasureTheory Filter Topology

noncomputable section
namespace GlobalTheory.ConvSeries

theorem exists_mem_prod_mul_gauss {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (M : Submodule ℂ (SchwartzMap E ℂ))
    (hM : ∀ (ℓ : E →L[ℝ] ℝ) (f f₁ : SchwartzMap E ℂ), f ∈ M → (∀ x, f₁ x = (ℓ x : ℂ) * f x) → f₁ ∈ M)
    (G : SchwartzMap E ℂ) (hG : G ∈ M) :
    ∀ (m : ℕ) (ℓ : Fin m → E →L[ℝ] ℝ), ∃ t ∈ M, ∀ y, t y = (∏ i, ((ℓ i y : ℝ) : ℂ)) * G y := by
  intro m
  induction m with
  | zero => intro ℓ; exact ⟨G, hG, fun y => by simp⟩
  | succ m ih =>
    intro ℓ
    obtain ⟨t, ht, hty⟩ := ih (fun i => ℓ i.succ)
    have hg : (fun x : E => ((ℓ 0 x : ℝ) : ℂ)).HasTemperateGrowth :=
      (Complex.ofRealCLM.comp (ℓ 0)).hasTemperateGrowth
    refine ⟨SchwartzMap.smulLeftCLM ℂ (fun x : E => ((ℓ 0 x : ℝ) : ℂ)) t,
      hM (ℓ 0) t _ ht (fun x => by rw [SchwartzMap.smulLeftCLM_apply_apply hg, smul_eq_mul]), fun y => ?_⟩
    rw [SchwartzMap.smulLeftCLM_apply_apply hg, smul_eq_mul, hty, Fin.prod_univ_succ, mul_assoc]

theorem gauss_mul_diag_mem : ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (M : Submodule ℂ (SchwartzMap E ℂ)),
    (∀ (ℓ : E →L[ℝ] ℝ) (f f₁ : SchwartzMap E ℂ), f ∈ M → (∀ x, f₁ x = (ℓ x : ℂ) * f x) → f₁ ∈ M) →
    ∀ (c : ℝ), 0 < c →
    (∀ g : SchwartzMap E ℂ, (∀ y, g y = Complex.exp (-((c * ‖y‖ ^ 2 : ℝ) : ℂ))) → g ∈ M) →
    ∀ (k : ℕ) (B : ContinuousMultilinearMap ℝ (fun _ : Fin k => E) ℂ),
      ∃ t ∈ M, ∀ y, t y = Complex.exp (-((c * ‖y‖ ^ 2 : ℝ) : ℂ)) * B (fun _ => y) := by
  intro E _ _ _ M hM c hc hGM k B
  have hin : ∀ x : E, innerSL ℝ x x = ‖x‖ ^ 2 := fun x => by
    first
    | rw [innerSL_apply_apply, real_inner_self_eq_norm_sq]
    | simp [real_inner_self_eq_norm_sq]
    | exact real_inner_self_eq_norm_sq x
  obtain ⟨G, hG⟩ := GlobalTheory.GaussSchwartz.exists_schwartz_exp_diag (-c • innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ)
    (fun x hx => by
      simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]; rw [hin]
      have : 0 < ‖x‖ ^ 2 := by positivity
      nlinarith)
  have hG' : ∀ y, G y = Complex.exp (-((c * ‖y‖ ^ 2 : ℝ) : ℂ)) := fun y => by
    rw [hG, Complex.ofReal_exp]
    congr 1
    simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]; rw [hin]
    push_cast; ring
  have hGmem := hGM G hG'
  let b := stdOrthonormalBasis ℝ E
  have key : ∀ r : Fin k → Fin (Module.finrank ℝ E), ∃ t ∈ M,
      ∀ y, t y = (∏ j, ((innerSL ℝ (b (r j)) y : ℝ) : ℂ)) * G y :=
    fun r => exists_mem_prod_mul_gauss M hM G hGmem k (fun j => innerSL ℝ (b (r j)))
  choose t ht hty using key
  refine ⟨∑ r, B (fun j => b (r j)) • t r, M.sum_mem fun r _ => M.smul_mem _ (ht r), fun y => ?_⟩
  have hy : (fun _ : Fin k => y) = fun _ : Fin k => ∑ i, (inner ℝ (b i) y) • b i := by
    funext _; exact (b.sum_repr' y).symm
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hy, ContinuousMultilinearMap.map_sum, Finset.mul_sum, SchwartzMap.sum_apply]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [B.map_smul_univ (fun j => inner ℝ (b (r j)) y) (fun j => b (r j)), SchwartzMap.smul_apply, hty, hG',
    Complex.real_smul, smul_eq_mul]
  have hi : ∀ v : E, innerSL ℝ v y = inner ℝ v y := fun v => rfl
  simp only [hi]
  push_cast
  ring

end GlobalTheory.ConvSeries
