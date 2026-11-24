module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfInnerSmooth
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HilbertSchurOfAdjointClosed
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GelfandInvariantCommRightTranslation
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SobolevContinuousFormGardingVectorStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothVecLowKSub
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedType
public import Formalism.RealPlaceAnalysis.Complexify
public import Formalism.RealPlaceAnalysis.InstMeasurableSpaceUJ
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Init.Core
public import Init.Data.Function
public import Init.Data.Nat.Basic
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Countable.Defs
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.ENat.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Function.AEEqFun
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Function.LpSpace.Complete
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib.MeasureTheory.OuterMeasure.AE
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Order.Filter.AtTopBot.Defs
public import Mathlib.Order.Filter.AtTopBot.Tendsto
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.Filter.Tendsto
public import Mathlib.Order.Monotone.Defs
public import Mathlib.Order.Notation
public import Mathlib.Order.TypeTags
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.Support
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.EMetricSpace.Defs
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.UniformSpace.Cauchy
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR.Mult GlobalTheory.SmVec MeasureTheory Matrix Filter
open scoped TensorProduct ContDiff InnerProductSpace Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SmVec

theorem continuous_toL2_gard : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (P G : Matrix (Fin n) (Fin n) ℂ), IsUnit P → Pᴴ * Formalism.REAL.Jm ε * P = G → IsURepOn (UJset ε) σ → ∀ (X : Type) [TopologicalSpace X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] (ν : Measure X) [IsFiniteMeasure ν] (act : Formalism.REAL.UJ ε → X → X), Continuous (Function.uncurry act) → ∀ (a : H →ₗ[ℂ] (X → ℂ)) (A : H →ₗ[ℂ] Lp ℂ 2 ν), (∀ w ∈ smSub G (trRep σ P), Continuous (a w) ∧ (∃ C : ℝ, ∀ x, ‖a w x‖ ≤ C) ∧ ∀ (g : Formalism.REAL.UJ ε) x, a (σ (umat g) w) x = a w (act g x)) → (∀ x, Sobolev₂ (lieG G) (trRep σ P) ((LinearMap.proj x).comp a)) → (∀ w ∈ smSub G (trRep σ P), (A w : X → ℂ) =ᵐ[ν] a w) → ∀ φ, IsTest φ → Continuous fun w => A (gard ε σ φ w) := by
  intro n ε H _ _ _ σ P G hP hG hσ X _ _ _ _ ν _ act _ a A _ hs hA φ hφ
  let g := GlobalTheory.LowTypeRestriction.garding hσ hφ.continuous hφ.2
  have hg : ∀ w, gard ε σ φ w = g w := fun w => gard_eq hσ hφ w
  let L : H →ₗ[ℂ] Lp ℂ 2 ν := A.comp (g : H →ₗ[ℂ] H)
  have hL : ∀ w, L w = A (gard ε σ φ w) := fun w => rfl
  have hc : ∀ x, Continuous fun w => a (gard ε σ φ w) x := fun x => by
    obtain ⟨C, hC⟩ := (GlobalTheory.T.sobolevContinuous_form_gardingVector n ε H σ P G hP hG hσ _ (hs x)).1 φ hφ
    exact (LinearMap.mkContinuous (((LinearMap.proj x).comp a).comp (g : H →ₗ[ℂ] H)) C hC).continuous
  have key : Continuous L := by
    refine L.continuous_of_seq_closed_graph fun u w f hu hf => ?_
    obtain ⟨ns, hns, hae⟩ := (tendstoInMeasure_of_tendsto_Lp hf).exists_seq_tendsto_ae
    have h1 : ∀ᵐ x ∂ν, ∀ k, (L (u k) : X → ℂ) x = a (gard ε σ φ (u k)) x :=
      ae_all_iff.2 fun k => hA _ (gard_mem hP hG hσ hφ (u k))
    refine Lp.ext ?_
    filter_upwards [hae, h1, hA _ (gard_mem hP hG hσ hφ w)] with x hx h1x h2x
    have h3 : Tendsto (fun k => a (gard ε σ φ (u (ns k))) x) atTop (𝓝 (a (gard ε σ φ w) x)) :=
      ((hc x).tendsto w).comp (hu.comp hns.tendsto_atTop)
    have h4 : Tendsto (fun k => a (gard ε σ φ (u (ns k))) x) atTop (𝓝 (f x)) :=
      hx.congr fun k => h1x (ns k)
    exact (tendsto_nhds_unique h4 h3).trans h2x.symm
  exact key

end GlobalTheory.SmVec
