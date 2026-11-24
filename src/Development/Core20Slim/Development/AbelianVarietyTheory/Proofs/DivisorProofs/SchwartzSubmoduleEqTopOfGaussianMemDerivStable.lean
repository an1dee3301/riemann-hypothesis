module

public import Mathlib
public import Development.Core20Slim.GroundTheory.GlobalFields.TateThesis.GaussianSchwartz
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEquivEuclideanPiMulNormSqEqReStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzDensityTransportLinearEquivChirpStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFourierStableGaussianSubmoduleStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzClosureStableLinearFormFourierStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemOfClosedSubmoduleGaussianConvolutionStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemAllGaussianWidthsOfFourierStableSchwartzStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemClosureWideGaussianMulSchwartzStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.NarrowGaussConvolutionDenseStatement
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.IsApply
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.Analysis.Fourier.Notation
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.Analysis.Normed.Lp.WithLp
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.RCLike.Lemmas
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Countable.Defs
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.Order.BoundedOrder.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Module.Basic
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.Algebra.Module.Equiv.Basic
public import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.UniformMulAction
public import Mathlib.Topology.Closure
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.EMetricSpace.Defs
public import Mathlib.Topology.MetricSpace.Algebra
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open FourierTransform MeasureTheory Filter Topology

namespace GlobalTheory.SchwartzGaussDense

theorem dense_of_stdGaussian_mem : ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (N : Submodule ℂ (SchwartzMap E ℂ)) (G : SchwartzMap E ℂ),
    (∀ y, G y = Complex.exp (-((Real.pi * ‖y‖ ^ 2 : ℝ) : ℂ))) → G ∈ N →
    (∀ (v : E) (f f₁ : SchwartzMap E ℂ), f ∈ N → (∀ x, f₁ x = fderiv ℝ (⇑f) x v) → f₁ ∈ N) →
    (∀ (ℓ : E →L[ℝ] ℝ) (f f₁ : SchwartzMap E ℂ), f ∈ N → (∀ x, f₁ x = (ℓ x : ℂ) * f x) → f₁ ∈ N) →
    Dense (N : Set (SchwartzMap E ℂ)) := by
  intro E _ _ _ _ _ N G hG hGN hD hL
  obtain ⟨W, hWN, hGW, hLW, hFW⟩ := GlobalTheory.T.exists_fourier_stable_submodule_containing_gaussian E N G hG hGN hD hL
  obtain ⟨hLM, hFM⟩ := GlobalTheory.T.topologicalClosure_stable_linearForm_mul_and_fourier E W hLW hFW
  set M := W.topologicalClosure with hMdef
  have hcl : IsClosed (M : Set (SchwartzMap E ℂ)) := W.isClosed_topologicalClosure
  have hGM : G ∈ M := W.le_topologicalClosure hGW
  have hgauss := GlobalTheory.T.mem_all_gaussianWidths_of_fourierStable_schwartz E M hcl hLM hFM G hG hGM
  have key : ∀ (h f : SchwartzMap E ℂ), (∃ b : ℝ, 0 < b ∧ ∀ y, f y = Complex.exp (-((b * ‖y‖ ^ 2 : ℝ) : ℂ)) * h y) →
      f ∈ M := by
    rintro h f ⟨b, hb, hf⟩
    have hsub : {u : SchwartzMap E ℂ | ∃ (c : ℝ) (s : ℂ), 0 < c ∧
        ∀ y, u y = s * ∫ a, f a * Complex.exp (-((c * ‖y - a‖ ^ 2 : ℝ) : ℂ))} ⊆ (M : Set (SchwartzMap E ℂ)) := by
      rintro u ⟨c, s, hc, hu⟩
      by_cases hs : s = 0
      · have : u = 0 := by ext y; simp [hu y, hs]
        rw [this]; exact M.zero_mem
      · have hu' : ∀ y, (s⁻¹ • u) y = ∫ a, Complex.exp (-((b * ‖a‖ ^ 2 : ℝ) : ℂ)) * h a *
            Complex.exp (-((c * ‖y - a‖ ^ 2 : ℝ) : ℂ)) := by
          intro y
          rw [SchwartzMap.smul_apply, hu y, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hs, one_mul]
          congr 1; funext a; rw [hf a]
        have hmem := GlobalTheory.T.mem_of_closedSubmodule_gaussian_convolution E M hcl hLM b c hb hc (hgauss c hc) h (s⁻¹ • u) hu'
        have : u = s • (s⁻¹ • u) := by rw [smul_smul, mul_inv_cancel₀ hs, one_smul]
        rw [this]; exact M.smul_mem s hmem
    exact closure_minimal hsub hcl (GlobalTheory.T.mem_closure_gaussian_convolutions E f)
  have hall : ∀ h : SchwartzMap E ℂ, h ∈ M := by
    intro h
    exact closure_minimal (fun f hf => key h f hf) hcl (GlobalTheory.T.mem_closure_wideGaussian_mul_schwartz E h)
  have htop : N.topologicalClosure = ⊤ := by
    rw [eq_top_iff]
    intro h _
    exact Submodule.topologicalClosure_mono hWN (hall h)
  exact (Submodule.dense_iff_topologicalClosure_eq_top).2 htop

theorem dense_of_gaussian_mem : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (N : Submodule ℂ (SchwartzMap V ℂ))
    (g : SchwartzMap V ℂ) (Q : V →L[ℝ] V →L[ℝ] ℂ) (c : ℝ), 0 < c → (∀ x, c * ‖x‖ ^ 2 ≤ (Q x x).re) →
    (∀ x, g x = Complex.exp (-(Q x x))) → g ∈ N →
    (∀ (v : V) (f f₁ : SchwartzMap V ℂ), f ∈ N → (∀ x, f₁ x = fderiv ℝ (⇑f) x v) → f₁ ∈ N) →
    (∀ (ℓ : V →L[ℝ] ℝ) (f f₁ : SchwartzMap V ℂ), f ∈ N → (∀ x, f₁ x = (ℓ x : ℂ) * f x) → f₁ ∈ N) →
    Dense (N : Set (SchwartzMap V ℂ)) := by
  intro V _ _ _ N g Q c hc hQ hg hgN hD hL
  obtain ⟨A, hA⟩ := GlobalTheory.T.exists_euclidean_equiv_pi_mul_norm_sq_eq_re V Q c hc hQ
  obtain ⟨N₂, hD₂, hL₂, hG₂, hdense⟩ := GlobalTheory.T.schwartz_density_transport_linearEquiv_chirp V _ A Q N hA hD hL
  apply hdense
  let G := GroundTheory.Global.gaussianSchwartz (EuclideanSpace ℝ (Fin (Module.finrank ℝ V)))
  have hG : ∀ y, G y = Complex.exp (-((Real.pi * ‖y‖ ^ 2 : ℝ) : ℂ)) := by
    intro y
    simp only [G, GroundTheory.Global.gaussianSchwartz_apply, Complex.ofReal_exp]
    congr 1; push_cast; ring
  exact dense_of_stdGaussian_mem _ N₂ G hG (hG₂ g G hg hgN hG) hD₂ hL₂

end GlobalTheory.SchwartzGaussDense
