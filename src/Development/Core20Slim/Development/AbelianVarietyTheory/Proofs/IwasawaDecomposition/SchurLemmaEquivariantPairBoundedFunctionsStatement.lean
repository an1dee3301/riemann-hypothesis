module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SchurLemmaEquivariantPairBoundedFunctions
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfInnerSmooth
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HilbertSchurOfAdjointClosed
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GelfandInvariantCommRightTranslation
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedType
public import Formalism.RealPlaceAnalysis.Complexify
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Init.Core
public import Init.Data.Function
public import Init.Prelude
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Ring.CompTypeclasses
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
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Constructions.SumProd
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
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schurLemma_equivariant_pair_boundedFunctions_alt : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (P G : Matrix (Fin n) (Fin n) ℂ), IsUnit P → Pᴴ * Formalism.REAL.Jm ε * P = G → IsURepOn (UJset ε) σ → IsIrredOn (UJset ε) σ → ∀ (X : Type) [TopologicalSpace X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] (ν : Measure X) [IsFiniteMeasure ν] (act : Formalism.REAL.UJ ε → X → X), Continuous (Function.uncurry act) → ∀ (a a' : H →ₗ[ℂ] (X → ℂ)), (∀ w ∈ smSub G (trRep σ P), Continuous (a w) ∧ (∃ C : ℝ, ∀ x, ‖a w x‖ ≤ C) ∧ ∀ (g : Formalism.REAL.UJ ε) x, a (σ (umat g) w) x = a w (act g x)) → (∀ x, Sobolev₂ (lieG G) (trRep σ P) ((LinearMap.proj x).comp a)) → (∀ w ∈ smSub G (trRep σ P), Continuous (a' w) ∧ (∃ C : ℝ, ∀ x, ‖a' w x‖ ≤ C) ∧ ∀ (g : Formalism.REAL.UJ ε) x, a' (σ (umat g) w) x = a' w (act g x)) → (∀ x, Sobolev₂ (lieG G) (trRep σ P) ((LinearMap.proj x).comp a')) → (∀ g ∈ UJset ε, ∀ u ∈ smSub G (trRep σ P), ∀ w ∈ smSub G (trRep σ P), ∫ x, star (a (σ g u) x) * a (σ g w) x ∂ν = ∫ x, star (a u x) * a w x ∂ν) → (∀ g ∈ UJset ε, ∀ u ∈ smSub G (trRep σ P), ∀ w ∈ smSub G (trRep σ P), ∫ x, star (a' (σ g u) x) * a' (σ g w) x ∂ν = ∫ x, star (a' u x) * a' w x ∂ν) → (∀ g ∈ UJset ε, ∀ u ∈ smSub G (trRep σ P), ∀ w ∈ smSub G (trRep σ P), ∫ x, star (a (σ g u) x) * a' (σ g w) x ∂ν = ∫ x, star (a u x) * a' w x ∂ν) → ∃ c : ℂ, ∀ w ∈ smSub G (trRep σ P), ∀ w' ∈ smSub G (trRep σ P), ∫ x, star (a w x) * a' w' x ∂ν = c * ⟪w, w'⟫_ℂ := by
  first | exact @GlobalTheory.SmVec.schurLemma_equivariant_pair_boundedFunctions | exact GlobalTheory.SmVec.schurLemma_equivariant_pair_boundedFunctions | (intros; apply GlobalTheory.SmVec.schurLemma_equivariant_pair_boundedFunctions <;> assumption)
