module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfInnerSmooth
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HilbertSchurOfAdjointClosed
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GelfandInvariantCommRightTranslation
public import Formalism.FormalDegreeBessel.StatementBF
public import Formalism.RealPlaceAnalysis.Complexify
public import Formalism.RealPlaceAnalysis.InstMeasurableSpaceUJ
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Init.Tactics
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
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
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.MulAction
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.OuterMeasure.AE
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Order.Filter.AtTopBot.Defs
public import Mathlib.Order.Filter.Basic
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.Filter.Tendsto
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Group.Subgroup
public import Mathlib.Topology.Algebra.Group.Units
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
public import Mathlib.Topology.Neighborhoods
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.UniformSpace.Cauchy
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR.Mult GlobalTheory.SmVec MeasureTheory Matrix Filter
open scoped TensorProduct ContDiff InnerProductSpace Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SmVec

theorem closable_of_smoothing : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (P G : Matrix (Fin n) (Fin n) ℂ), IsUnit P → Pᴴ * Formalism.REAL.Jm ε * P = G → IsURepOn (UJset ε) σ → ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E] (A : H →ₗ[ℂ] E), (∀ g ∈ UJset ε, ∀ u ∈ smSub G (trRep σ P), ∀ w ∈ smSub G (trRep σ P), ⟪A (σ g u), A (σ g w)⟫_ℂ = ⟪A u, A w⟫_ℂ) → (∀ u ∈ smSub G (trRep σ P), ∀ f : E, Continuous fun g : Formalism.REAL.UJ ε => ⟪f, A (σ (umat g) u)⟫_ℂ) → (∀ φ, IsTest φ → Continuous fun w => A (gard ε σ φ w)) → (∀ φ, IsTest φ → ∀ w ∈ smSub G (trRep σ P), ∀ f : E, ⟪f, A (gard ε σ φ w)⟫_ℂ = ∫ g : Formalism.REAL.UJ ε, φ (umat g) • ⟪f, A (σ (umat g) w)⟫_ℂ ∂(Formalism.REAL.muG ε)) → (∀ (u : ℕ → H) (f : E), (∀ i, u i ∈ smSub G (trRep σ P)) → Tendsto u atTop (𝓝 0) → Tendsto (fun i => A (u i)) atTop (𝓝 f) → f = 0) := by
  intro n ε H _ _ _ σ P G hP hG hσ E _ _ A h1 h2 h3 h4 u f hu hu0 hA
  have hmul : ∀ (g : Formalism.REAL.UJ ε) (v : H), σ (umat g) (σ (umat g⁻¹) v) = v := by
    intro g v
    have e : σ (umat g * umat g⁻¹) = _ := hσ.1.2 _ g.2 _ (g⁻¹).2
    have e1 : umat g * umat g⁻¹ = 1 := by
      have : umat (g * g⁻¹) = umat (1 : Formalism.REAL.UJ ε) := by rw [mul_inv_cancel]
      exact this
    rw [e1, hσ.1.1] at e
    exact (congrArg (fun T : H →L[ℂ] H => T v) e).symm
  have key : ∀ v ∈ smSub G (trRep σ P), ⟪A v, f⟫_ℂ = 0 := by
    intro v hv
    have hmem : ∀ g : Formalism.REAL.UJ ε, σ (umat g⁻¹) v ∈ smSub G (trRep σ P) := fun g =>
      sigma_mem hP hG hσ hv (g⁻¹).2
    have hc : ∀ y : E, Continuous fun g : Formalism.REAL.UJ ε => ⟪A (σ (umat g⁻¹) v), y⟫_ℂ := by
      intro y
      have := Complex.continuous_conj.comp ((h2 v hv y).comp continuous_inv)
      simpa only [Function.comp_def, inner_conj_symm] using this
    have hnorm : ∀ g : Formalism.REAL.UJ ε, ‖A (σ (umat g⁻¹) v)‖ = ‖A v‖ := by
      intro g
      have := h1 _ (g⁻¹).2 v hv v hv
      rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), norm_eq_sqrt_re_inner (𝕜 := ℂ) (A v)]
      exact congrArg (fun z => √(RCLike.re z)) this
    have h0 := eq_zero_of_forall_test (F := fun g : Formalism.REAL.UJ ε => ⟪A (σ (umat g⁻¹) v), f⟫_ℂ) (hc f) (by
      intro φ hφ
      have hg0 : gard ε σ φ 0 = 0 := by simp [gard]
      have t1 : Tendsto (fun i => ⟪A v, A (gard ε σ φ (u i))⟫_ℂ) atTop (𝓝 0) := by
        have := (tendsto_const_nhds (x := A v)).inner (𝕜 := ℂ) (((h3 φ hφ).tendsto 0).comp hu0)
        simpa [hg0, Function.comp_def] using this
      have e : ∀ i, ⟪A v, A (gard ε σ φ (u i))⟫_ℂ
          = ∫ g : Formalism.REAL.UJ ε, φ (umat g) • ⟪A (σ (umat g⁻¹) v), A (u i)⟫_ℂ ∂(Formalism.REAL.muG ε) := by
        intro i
        rw [h4 φ hφ _ (hu i)]
        congr 1
        funext g
        rw [← h1 _ g.2 _ (hmem g) _ (hu i)]
        erw [hmul]
      have hψi : Integrable (fun g : Formalism.REAL.UJ ε => φ (umat g)) (Formalism.REAL.muG ε) := by
        simpa using hφ.integrable (F := fun _ : Formalism.REAL.UJ ε => (1 : ℝ)) continuous_const
      have t2 : Tendsto (fun i => ⟪A v, A (gard ε σ φ (u i))⟫_ℂ) atTop
          (𝓝 (∫ g : Formalism.REAL.UJ ε, φ (umat g) • ⟪A (σ (umat g⁻¹) v), f⟫_ℂ ∂(Formalism.REAL.muG ε))) := by
        rw [tendsto_iff_norm_sub_tendsto_zero]
        have t3 : Tendsto (fun i => (∫ g : Formalism.REAL.UJ ε, ‖φ (umat g)‖ ∂(Formalism.REAL.muG ε)) * (‖A v‖ * ‖A (u i) - f‖))
            atTop (𝓝 0) := by
          have := ((tendsto_iff_norm_sub_tendsto_zero.1 hA).const_mul ‖A v‖).const_mul
            (∫ g : Formalism.REAL.UJ ε, ‖φ (umat g)‖ ∂(Formalism.REAL.muG ε))
          simpa using this
        refine squeeze_zero (fun _ => norm_nonneg _) (fun i => ?_) t3
        rw [e, ← integral_sub (hφ.integrable (hc _)) (hφ.integrable (hc _)), ← integral_mul_const]
        refine norm_integral_le_of_norm_le (hψi.norm.mul_const _) (Eventually.of_forall fun g => ?_)
        rw [← smul_sub, norm_smul, ← inner_sub_right, ← hnorm g]
        exact mul_le_mul_of_nonneg_left (norm_inner_le_norm _ _) (norm_nonneg _)
      exact tendsto_nhds_unique t2 t1)
    have e : σ (umat (1 : Formalism.REAL.UJ ε)⁻¹) v = v := by
      rw [inv_one]
      show σ 1 v = v
      rw [hσ.1.1]; rfl
    simpa only [e] using h0
  have t := hA.inner (𝕜 := ℂ) (tendsto_const_nhds (x := f))
  simp only [key _ (hu _)] at t
  exact inner_self_eq_zero.1 (tendsto_nhds_unique t tendsto_const_nhds)

end GlobalTheory.SmVec
