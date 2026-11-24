module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfInnerSmooth
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HilbertSchurOfAdjointClosed
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GelfandInvariantCommRightTranslation
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GardingVectorDerivativeEqGardingVectorStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothVectorWordActionContinuousStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SobolevContinuousFormSumLieWordInnerStatement
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedType
public import Formalism.RealPlaceAnalysis.Complexify
public import Formalism.RealPlaceAnalysis.InstMeasurableSpaceUJ
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Init.Classical
public import Init.Core
public import Init.Data.List.Basic
public import Init.Data.List.Lemmas
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.GroupWithZero.Action
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Mathlib.Analysis.CStarAlgebra.Module.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Continuous
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Complex.Module
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Cauchy
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR.Mult GlobalTheory.SmVec MeasureTheory Matrix Filter
open scoped TensorProduct ContDiff InnerProductSpace Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SobGarding

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {P G : Matrix (Fin n) (Fin n) ℂ}

theorem word_gard (hP : IsUnit P) (h : Pᴴ * Formalism.REAL.Jm ε * P = G) (hσ : IsURepOn (UJset ε) σ)
    {φ : Matrix (Fin n) (Fin n) ℂ → ℝ} (hφ : IsTest φ) (l : List (Matrix (Fin n) (Fin n) ℂ))
    (hl : ∀ X ∈ l, X ∈ lieG G) :
    ∃ φ', IsTest φ' ∧ ∀ w, word (trRep σ P) l (gard ε σ φ w) = gard ε σ φ' w := by
  induction l with
  | nil => exact ⟨φ, hφ, fun _ => rfl⟩
  | cons X l ih =>
    obtain ⟨φ', h1, h2⟩ := ih fun Y hY => hl Y (by simp [hY])
    obtain ⟨ψ, hψ⟩ := GlobalTheory.T.gardingVector_derivative_eq_gardingVector n ε H σ P G hP h hσ φ' h1
    exact ⟨ψ X, (hψ X).1, fun w => by rw [word_cons, h2, (hψ X).2 (hl X (by simp))]⟩

theorem inner_word_gard (hP : IsUnit P) (h : Pᴴ * Formalism.REAL.Jm ε * P = G) (hσ : IsURepOn (UJset ε) σ)
    {φ : Matrix (Fin n) (Fin n) ℂ → ℝ} (hφ : IsTest φ) (l : List (Matrix (Fin n) (Fin n) ℂ))
    (hl : ∀ X ∈ l, X ∈ lieG G) {w : H} (hw : w ∈ smSub G (trRep σ P)) (a : H) :
    ⟪a, word (trRep σ P) l (gard ε σ φ w)⟫_ℂ
      = ∫ g : Formalism.REAL.UJ ε, φ (umat g) • ⟪a, word (trRep σ P) l (σ (umat g) w)⟫_ℂ ∂(Formalism.REAL.muG ε) := by
  have hc := GlobalTheory.T.smooth_vector_word_action_continuous n ε H σ P G hP h hσ l hl w hw
  have key : ∀ y : H, ⟪y, ∫ g : Formalism.REAL.UJ ε, φ (umat g) • word (trRep σ P) l (σ (umat g) w) ∂(Formalism.REAL.muG ε)⟫_ℂ
      = ∫ g : Formalism.REAL.UJ ε, φ (umat g) • ⟪y, word (trRep σ P) l (σ (umat g) w)⟫_ℂ ∂(Formalism.REAL.muG ε) := by
    intro y
    rw [← integral_inner (hφ.integrable hc)]
    congr 1
    funext g
    rw [← Complex.coe_smul, inner_smul_right, Complex.real_smul]
  rw [← key]
  congr 1
  refine ext_inner_smooth hP h hσ fun u hu => ?_
  obtain ⟨u', -, h2⟩ := word_adjoint (gram_unit hP h) (isURepOn_trRep hP h hσ) hl hu
  rw [key, h2 _ (gard_mem hP h hσ hφ w), inner_gard hσ hφ]
  congr 1
  funext g
  rw [h2 _ (sigma_mem hP h hσ hw g.2)]

theorem sobCont_gard : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (P G : Matrix (Fin n) (Fin n) ℂ), IsUnit P → Pᴴ * Formalism.REAL.Jm ε * P = G → IsURepOn (UJset ε) σ → ∀ ℓ : H →ₗ[ℂ] ℂ, Sobolev₂ (lieG G) (trRep σ P) ℓ → (∀ φ, IsTest φ → ∃ C : ℝ, ∀ w, ‖ℓ (gard ε σ φ w)‖ ≤ C * ‖w‖) ∧ ∀ w ∈ smSub G (trRep σ P), (Continuous fun g : Formalism.REAL.UJ ε => ℓ (σ (umat g) w)) ∧ ∀ φ, IsTest φ → ℓ (gard ε σ φ w) = ∫ g : Formalism.REAL.UJ ε, φ (umat g) • ℓ (σ (umat g) w) ∂(Formalism.REAL.muG ε) := by
  intro n ε H _ _ _ σ P G hP h hσ ℓ hℓ
  obtain ⟨m, ls, a, hls, hrep⟩ := GlobalTheory.T.sobolevContinuousForm_sum_lieWord_inner n ε H σ P G hP h hσ ℓ hℓ
  refine ⟨fun φ hφ => ?_, fun w hw => ?_⟩
  · choose ψ _ hψ using fun i => word_gard hP h hσ hφ (ls i) (hls i)
    refine ⟨∑ i, ‖a i‖ * ∫ g : Formalism.REAL.UJ ε, |ψ i (umat g)| ∂(Formalism.REAL.muG ε), fun w => ?_⟩
    rw [hrep _ (gard_mem hP h hσ hφ w), Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [hψ, mul_assoc]
    exact (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left (norm_gard_le hσ _ w) (norm_nonneg _))
  · have e : ∀ g : Formalism.REAL.UJ ε, ℓ (σ (umat g) w) = ∑ i, ⟪a i, word (trRep σ P) (ls i) (σ (umat g) w)⟫_ℂ :=
      fun g => hrep _ (sigma_mem hP h hσ hw g.2)
    have hc : ∀ i, Continuous fun g : Formalism.REAL.UJ ε => ⟪a i, word (trRep σ P) (ls i) (σ (umat g) w)⟫_ℂ :=
      fun i => continuous_const.inner (GlobalTheory.T.smooth_vector_word_action_continuous n ε H σ P G hP h hσ (ls i) (hls i) w hw)
    simp only [e]
    refine ⟨continuous_finsetSum _ fun i _ => hc i, fun φ hφ => ?_⟩
    rw [hrep _ (gard_mem hP h hσ hφ w)]
    simp only [Finset.smul_sum]
    rw [integral_finsetSum _ fun i _ => hφ.integrable (hc i)]
    exact Finset.sum_congr rfl fun i _ => inner_word_gard hP h hσ hφ (ls i) (hls i) hw (a i)

end GlobalTheory.SobGarding
