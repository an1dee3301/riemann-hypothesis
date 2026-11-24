module

public import Mathlib
public import Batteries.Logic
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Submodule.Basic
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Module.Submodule.Map
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Ring.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Distribution.DerivNotation
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.Analysis.Distribution.TemperateGrowth
public import Mathlib.Analysis.Fourier.FourierTransform
public import Mathlib.Analysis.Fourier.Notation
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Analysis.Normed.Operator.LinearIsometry
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.Complex.Module
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.Order.Bounds.Defs
public import Mathlib.Order.CompleteLattice.Defs
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Tactic.FieldSimp.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Instances.RealVectorSpace
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Metrizable.Basic
public import Mathlib.Topology.Metrizable.Uniformity
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open FourierTransform MeasureTheory Filter Topology

namespace GlobalTheory

theorem exists_fourier_stable_gaussian_submodule :
    ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (N : Submodule ℂ (SchwartzMap E ℂ)) (G : SchwartzMap E ℂ),
    (∀ y, G y = Complex.exp (-((Real.pi * ‖y‖ ^ 2 : ℝ) : ℂ))) → G ∈ N →
    (∀ (v : E) (f f₁ : SchwartzMap E ℂ), f ∈ N → (∀ x, f₁ x = fderiv ℝ (⇑f) x v) → f₁ ∈ N) →
    (∀ (ℓ : E →L[ℝ] ℝ) (f f₁ : SchwartzMap E ℂ), f ∈ N → (∀ x, f₁ x = (ℓ x : ℂ) * f x) → f₁ ∈ N) →
    ∃ W : Submodule ℂ (SchwartzMap E ℂ), W ≤ N ∧ G ∈ W ∧
      (∀ (ℓ : E →L[ℝ] ℝ) (f f₁ : SchwartzMap E ℂ), f ∈ W → (∀ x, f₁ x = (ℓ x : ℂ) * f x) → f₁ ∈ W) ∧
      (∀ f ∈ W, 𝓕 f ∈ W) := by
  intro E _ _ _ _ _ N G hG hGN hD hL
  let S : Set (Submodule ℂ (SchwartzMap E ℂ)) := {K | G ∈ K ∧
    (∀ (v : E) (f f₁ : SchwartzMap E ℂ), f ∈ K → (∀ x, f₁ x = fderiv ℝ (⇑f) x v) → f₁ ∈ K) ∧
    (∀ (ℓ : E →L[ℝ] ℝ) (f f₁ : SchwartzMap E ℂ), f ∈ K → (∀ x, f₁ x = (ℓ x : ℂ) * f x) → f₁ ∈ K)}
  have hWG : G ∈ sInf S := Submodule.mem_sInf.2 fun K hK => hK.1
  have hWD : ∀ (v : E) (f f₁ : SchwartzMap E ℂ), f ∈ sInf S →
      (∀ x, f₁ x = fderiv ℝ (⇑f) x v) → f₁ ∈ sInf S := fun v f f₁ hf h =>
    Submodule.mem_sInf.2 fun K hK => hK.2.1 v f f₁ (Submodule.mem_sInf.1 hf K hK) h
  have hWL : ∀ (ℓ : E →L[ℝ] ℝ) (f f₁ : SchwartzMap E ℂ), f ∈ sInf S →
      (∀ x, f₁ x = (ℓ x : ℂ) * f x) → f₁ ∈ sInf S := fun v f f₁ hf h =>
    Submodule.mem_sInf.2 fun K hK => hK.2.2 v f f₁ (Submodule.mem_sInf.1 hf K hK) h
  have htemp : ∀ m : E, Function.HasTemperateGrowth (fun x : E => inner ℝ x m) := by
    intro m
    have : (fun x : E => inner ℝ x m) = (innerSL ℝ m : E →L[ℝ] ℝ) := by
      funext x; simp [real_inner_comm]
    rw [this]; exact (innerSL ℝ m).hasTemperateGrowth
  have hFG : 𝓕 G = G := by
    ext w
    have h1 : (⇑G) = fun v : E => Complex.exp (-(Real.pi : ℂ) * (‖v‖ : ℂ) ^ 2) := by
      funext v; rw [hG]; congr 1; push_cast; ring
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    rw [SchwartzMap.fourier_coe, h1,
      fourier_gaussian_innerProductSpace (by simpa using Real.pi_pos), div_self hpi,
      Complex.one_cpow, one_mul]
    congr 1
    field_simp
  have hK : (sInf S).comap (SchwartzMap.fourierTransformCLM ℂ (V := E) (E := ℂ)).toLinearMap ∈ S := by
    refine ⟨?_, ?_, ?_⟩
    · show 𝓕 G ∈ sInf S
      rw [hFG]; exact hWG
    · intro v f f₁ hf h
      have hf' : 𝓕 f ∈ sInf S := hf
      show 𝓕 f₁ ∈ sInf S
      have h1 : f₁ = LineDeriv.lineDerivOp v f := by
        ext x; rw [h, SchwartzMap.lineDerivOp_apply_eq_fderiv]
      rw [h1, SchwartzMap.fourier_lineDerivOp_eq]
      refine Submodule.smul_mem _ _ (hWL (innerSL ℝ v) _ _ hf' fun x => ?_)
      rw [SchwartzMap.smulLeftCLM_apply_apply (htemp v)]
      simp [real_inner_comm]
    · intro ℓ f f₁ hf h
      have hf' : 𝓕 f ∈ sInf S := hf
      show 𝓕 f₁ ∈ sInf S
      set u : E := (InnerProductSpace.toDual ℝ E).symm ℓ with hu
      have h1 : f₁ = SchwartzMap.smulLeftCLM ℂ (fun x => inner ℝ x u) f := by
        ext x
        rw [h, SchwartzMap.smulLeftCLM_apply_apply (htemp u), real_inner_comm, hu,
          InnerProductSpace.toDual_symm_apply]
        simp
      have h2 : LineDeriv.lineDerivOp u (𝓕 f) ∈ sInf S :=
        hWD u _ _ hf' fun x => SchwartzMap.lineDerivOp_apply_eq_fderiv _ _ _
      rw [SchwartzMap.lineDerivOp_fourier_eq, ← h1, ← SchwartzMap.fourierTransformCLM_apply ℂ,
        map_smul, SchwartzMap.fourierTransformCLM_apply] at h2
      have hc : (-(2 * (Real.pi : ℂ) * Complex.I)) ≠ 0 := by
        simp [Real.pi_ne_zero]
      exact (Submodule.smul_mem_iff _ hc).1 h2
  exact ⟨sInf S, sInf_le ⟨hGN, hD, hL⟩, hWG, hWL, fun f hf => sInf_le hK hf⟩

end GlobalTheory
