module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.HeightProofs.CompactUnitaryCasimirPowPairingModerateGrowthBou
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
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.HeightProofs.FiniteDimensionalPolyV
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm
public import Formalism.RealPlaceAnalysis.Complexify
public import Formalism.RealPlaceAnalysis.InstMeasurableSpaceUJ
public import Formalism.RealPlaceAnalysis.SmoothOnGVIff
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Init.Core
public import Init.Data.List.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.Logic.Function.Iterate
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KFourier MeasureTheory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compactUnitaryCasimir_pow_pairing_moderateGrowth_bound : ∀ {n : ℕ} (ε : Fin n → Bool) (N : ℕ) (F : List (Mx n) → Mx n → ℂ), IsDerFam ε F → FamGrowth ε N F → ContinuousOn (F []) (UJset ε) → ∀ {r : ℕ} (X : Fin r → Mx n), (∀ j, inK ε (X j)) → ∀ (M : ℕ) (u : List (Mx n)), (∀ Y ∈ u, inK ε Y) → ∃ C : ℝ, ∀ (d : ℕ) (p : KG ε → ℂ), p ∈ polyV ε d → ∀ y ∈ UJset ε, ‖∫ k, ((fun φ : KG ε → ℂ => ∑ j, rder ε [X j, X j] φ)^[M] p) k * F u (y * toMK k) ∂(muK ε)‖ ≤ C * (1 + hs y) ^ N * Real.sqrt (∫ k, ‖p k‖ ^ 2 ∂(muK ε)) := by
  first | exact @GlobalTheory.KFourier.CasimirMove.casimir_pow_bound | exact GlobalTheory.KFourier.CasimirMove.casimir_pow_bound | (intros; apply GlobalTheory.KFourier.CasimirMove.casimir_pow_bound <;> assumption)
