module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPairingStdP
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousUnitaryOneParameterRealPlaceComponent
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneParamSubgroupGeneratorsExist
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Classical
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix RealInnerProductSpace
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open scoped Classical

noncomputable section

namespace GlobalTheory.RealLiftComp

open Matrix GlobalTheory.RealLiftGen

theorem exists_comp : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (β : Type) [Fintype β]
    [DecidableEq β] (R S : ℕ) (τ : ∀ w : InfinitePlace F, EmbOver E w) (J : Matrix β β (AE F E)) (b : ℂ)
    (C : InfinitePlace F → Matrix β (Ix R S) ℂ), IsCMExt F E σ → (∀ w, IsFrame (b • J.map (piInf (τ w))) (C w)) →
    ∃ k : UG (cA σ) J →* (InfinitePlace F → Mat R S), Continuous k ∧
      (∀ g w, (g.1 : Matrix β β (AE F E)).map (piInf (τ w)) * C w = C w * k g w) ∧
      (∀ g w, (k g w)ᴴ * Jm R S * k g w = Jm R S) ∧ ∀ w (M M' : Mat R S), C w * M = C w * M' → M = M' := by
  intro F E _ _ _ _ _ σ β _ _ R S τ J b C hcm hC
  choose A' hA' using fun w => (hC w).2
  set K : InfinitePlace F → Matrix β β ℂ := fun w => b • J.map (piInf (τ w)) with hK
  have hF : ∀ w, (C w)ᵀ * K w * (C w).map star = Jm R S := fun w => (hC w).1
  have hAC : ∀ w, A' w * C w = 1 := by
    intro w
    have h1 : (Jm R S * (C w)ᵀ * K w) * (C w).map star = 1 := by
      rw [Matrix.mul_assoc (Jm R S), Matrix.mul_assoc (Jm R S), hF, Jm_mul_Jm]
    have h2 : (Jm R S * (C w)ᵀ * K w).map star * C w = 1 := by
      have := congrArg (fun X => X.map star) h1
      rw [map_star_mul, map_star_star] at this
      rw [this]; ext i j; simp [Matrix.one_apply]
    calc A' w * C w = ((Jm R S * (C w)ᵀ * K w).map star * C w) * A' w * C w := by rw [h2, Matrix.one_mul]
      _ = (Jm R S * (C w)ᵀ * K w).map star * C w := by rw [Matrix.mul_assoc _ (C w), hA', Matrix.mul_one]
      _ = 1 := h2
  set M : UG (cA σ) J → InfinitePlace F → Matrix β β ℂ :=
    fun g w => (g.1 : Matrix β β (AE F E)).map (piInf (τ w)) with hM
  have hMmul : ∀ g h w, M (g * h) w = M g w * M h w := by
    intro g h w
    simp only [hM, Subgroup.coe_mul, Units.val_mul]
    exact Matrix.map_mul
  have hM1 : ∀ w, M 1 w = 1 := by
    intro w
    simp only [hM, OneMemClass.coe_one, Units.val_one]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  have hMu : ∀ g w, (M g w)ᵀ * K w * (M g w).map star = K w := by
    intro g w
    have hg := g.2
    change ((g.1 : Matrix β β (AE F E)))ᵀ * J * ((g.1 : Matrix β β (AE F E))).map (cA σ) = J at hg
    have h2 := congrArg (fun X => X.map (piInf (τ w))) hg
    simp only [Matrix.map_mul, Matrix.map_map] at h2
    have h3 : (piInf (τ w)) ∘ (cA σ) = star ∘ (piInf (τ w)) := funext fun x => piInf_cA hcm (τ w) x
    rw [h3, ← Matrix.map_map] at h2
    have h4 : (M g w)ᵀ * J.map (piInf (τ w)) * (M g w).map star = J.map (piInf (τ w)) := by
      simp only [hM]; rw [← Matrix.transpose_map]; exact h2
    simp only [hK, Matrix.mul_smul, Matrix.smul_mul]
    rw [h4]
  let k : UG (cA σ) J →* (InfinitePlace F → Mat R S) :=
    { toFun := fun g w => A' w * M g w * C w
      map_one' := by funext w; simp only [hM1, Matrix.mul_one, hAC, Pi.one_apply]
      map_mul' := by
        intro g h; funext w
        simp only [hMmul, Pi.mul_apply]
        calc A' w * (M g w * M h w) * C w = A' w * M g w * (C w * A' w) * M h w * C w := by
              rw [hA', Matrix.mul_one]; simp only [Matrix.mul_assoc]
          _ = _ := by simp only [Matrix.mul_assoc] }
  have hk : ∀ g w, k g w = A' w * M g w * C w := fun _ _ => rfl
  have hCk : ∀ g w, C w * k g w = M g w * C w := by
    intro g w; simp only [hk, ← Matrix.mul_assoc, hA', Matrix.one_mul]
  refine ⟨k, ?_, fun g w => (hCk g w).symm, fun g w => ?_, fun w X X' h => ?_⟩
  · have h1 : Continuous (fun g : UG (cA σ) J => ((g.1 : Matrix β β (AE F E)))) :=
      Units.continuous_val.comp continuous_subtype_val
    refine continuous_pi fun w => ?_
    exact (continuous_const.matrix_mul (h1.matrix_map (GlobalTheory.ContMapReal.continuous_piInf (τ w)))).matrix_mul
      continuous_const
  · have hT : (k g w)ᵀ * Jm R S * (k g w).map star = Jm R S := by
      rw [← hF w]
      calc (k g w)ᵀ * ((C w)ᵀ * K w * (C w).map star) * (k g w).map star
          = (C w * k g w)ᵀ * K w * (C w * k g w).map star := by
            simp only [Matrix.transpose_mul, map_star_mul, Matrix.mul_assoc]
        _ = (C w)ᵀ * ((M g w)ᵀ * K w * (M g w).map star) * (C w).map star := by
            simp only [hCk, Matrix.transpose_mul, map_star_mul, Matrix.mul_assoc]
        _ = _ := by rw [hMu]
    have h2 := congrArg (fun X => X.map star) hT
    simp only [map_star_mul, Jm_map_star, map_star_star] at h2
    exact h2
  · have := congrArg (fun Y => A' w * Y) h
    simpa only [← Matrix.mul_assoc, hAC, Matrix.one_mul] using this

end GlobalTheory.RealLiftComp
