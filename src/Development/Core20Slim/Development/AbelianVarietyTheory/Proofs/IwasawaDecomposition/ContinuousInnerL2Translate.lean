module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfInnerSmooth
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HilbertSchurOfAdjointClosed
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GelfandInvariantCommRightTranslation
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedType
public import Formalism.RealPlaceAnalysis.Complexify
public import Formalism.RealPlaceAnalysis.InstMeasurableSpaceUJ
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Init.Core
public import Init.Data.Function
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Algebra.Torsor.Defs
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
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Function.AEEqFun
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib.MeasureTheory.OuterMeasure.AE
public import Mathlib.Order.Basic
public import Mathlib.Order.Filter.Basic
public import Mathlib.Order.Filter.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Group.Torsor
public import Mathlib.Topology.Algebra.Group.Units
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.EMetricSpace.Defs
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Metrizable.Basic
public import Mathlib.Topology.Metrizable.Uniformity
public import Mathlib.Topology.Metrizable.Urysohn
public import Mathlib.Topology.Separation.Basic
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.Separation.Regular
public import Mathlib.Topology.UniformSpace.Cauchy
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR.Mult GlobalTheory.SmVec MeasureTheory Matrix Filter
open scoped TensorProduct ContDiff InnerProductSpace Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SmVec

theorem continuous_inner_l2_translate :
    ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (P G : Matrix (Fin n) (Fin n) ℂ), IsUnit P → Pᴴ * Formalism.REAL.Jm ε * P = G → IsURepOn (UJset ε) σ → ∀ (X : Type) [TopologicalSpace X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] (ν : Measure X) [IsFiniteMeasure ν] (act : Formalism.REAL.UJ ε → X → X), Continuous (Function.uncurry act) → ∀ (a : H →ₗ[ℂ] (X → ℂ)) (A : H →ₗ[ℂ] Lp ℂ 2 ν), (∀ w ∈ smSub G (trRep σ P), Continuous (a w) ∧ (∃ C : ℝ, ∀ x, ‖a w x‖ ≤ C) ∧ ∀ (g : Formalism.REAL.UJ ε) x, a (σ (umat g) w) x = a w (act g x)) → (∀ x, Sobolev₂ (lieG G) (trRep σ P) ((LinearMap.proj x).comp a)) → (∀ w ∈ smSub G (trRep σ P), (A w : X → ℂ) =ᵐ[ν] a w) → ∀ u ∈ smSub G (trRep σ P), ∀ f : Lp ℂ 2 ν, Continuous fun g : Formalism.REAL.UJ ε => ⟪f, A (σ (umat g) u)⟫_ℂ := by
  intro n ε H _ _ _ σ P G hP hG hσ X _ _ _ _ ν _ act hact a A ha _ hA u hu f
  obtain ⟨hc, ⟨C, hC⟩, heq⟩ := ha u hu
  have hfi : Integrable (f : X → ℂ) ν := (Lp.memLp f).integrable (by norm_num)
  have key : (fun g : Formalism.REAL.UJ ε => ⟪f, A (σ (umat g) u)⟫_ℂ)
      = fun g => ∫ x, ⟪f x, a u (act g x)⟫_ℂ ∂ν := by
    funext g
    rw [L2.inner_def]
    have hm : σ (umat g) u ∈ smSub G (trRep σ P) := by
      exact sigma_mem hP hG hσ hu g.2
    refine integral_congr_ae ?_
    filter_upwards [hA _ hm] with x hx
    rw [hx, heq]
  rw [key]
  refine continuous_of_dominated (bound := fun x => ‖f x‖ * C) ?_ ?_ (hfi.norm.mul_const C) ?_
  · intro g
    refine AEStronglyMeasurable.inner hfi.aestronglyMeasurable ?_
    exact (hc.comp (hact.comp (Continuous.prodMk_right g))).aestronglyMeasurable
  · intro g
    refine Eventually.of_forall fun x => ?_
    exact (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left (hC _) (norm_nonneg _))
  · refine Eventually.of_forall fun x => ?_
    exact continuous_const.inner (hc.comp (hact.comp (Continuous.prodMk_left x)))

end GlobalTheory.SmVec
