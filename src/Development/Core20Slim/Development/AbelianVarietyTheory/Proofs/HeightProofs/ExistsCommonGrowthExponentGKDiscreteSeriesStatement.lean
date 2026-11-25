module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsCommonGrowthExponentGKDiscreteSeries
public import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
public import Development.Core20Slim.Development.AbelianVarietyTheory.BlockTheory.HeightDefect.FinitePartTypes
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqExistsIffDsExists
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqUniqueOfClassification
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasTypeAllAddOfEquiv
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OneAddHsConjLe
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnAtTau
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoefBoundOfCasselmanWallach
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedType
public import Formalism.RealPlaceAnalysis.Complexify
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Init.Core
public import Init.Data.List.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Cauchy
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_common_growth_exponent_gK_discreteSeries : GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach →
    ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Mx n → (H →L[ℂ] H)), Std ε σ → ∀ N : ℕ,
    ∃ S : List (List (Mx n)), Words (lieSet ε) S ∧ ∃ (m : List (List (Mx n)) → ℕ) (A : List (List (Mx n)) → ℝ),
    ∀ (p : ℕ) (ℓ : Fin p → (H →ₗ[ℂ] ℂ)) (x : Fin p → H), (∀ j, Sobolev₂ (lieSet ε) σ (ℓ j)) →
    (∀ j, IsKFin ε σ (x j)) → ∀ B : ℕ → ℝ,
    (∀ k (w : List (Mx n)), w.length ≤ k → (∀ X ∈ w, X ∈ lieSet ε ∧ Xᴴ = -X ∧ hs X ≤ 1) →
      ∀ y ∈ UJset ε, ‖∑ j, ℓ j (σ y (Dw σ w (x j)))‖ ≤ B k * (1 + hs y) ^ N) →
    ∃ (q : ℕ) (ℓ' : Fin q → (H →ₗ[ℂ] ℂ)) (x' : Fin q → H) (c : Fin q → ℝ),
      (∀ i, Sm ε σ (x' i)) ∧ (∀ i, 0 ≤ c i) ∧ (∀ i w, Sm ε σ w → ‖ℓ' i w‖ ≤ c i * sobNorm σ S w) ∧
      (∀ S', Words (lieSet ε) S' → ∑ i, c i * sobNorm σ S' (x' i) ≤ A S' * B (m S')) ∧
      ∀ y ∈ UJset ε, ∑ j, ℓ j (σ y (x j)) = ∑ i, ℓ' i (σ y (x' i)) := by
  first | exact @GlobalTheory.TypeSum.CoefRep.exists_rewrite | exact GlobalTheory.TypeSum.CoefRep.exists_rewrite | (intros; apply GlobalTheory.TypeSum.CoefRep.exists_rewrite <;> assumption)
