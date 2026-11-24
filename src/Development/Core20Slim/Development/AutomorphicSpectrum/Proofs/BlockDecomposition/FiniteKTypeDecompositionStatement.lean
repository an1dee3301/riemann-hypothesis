module

public import Mathlib
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteKTypeDecomposition
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousFrameEquivSymm
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.StripEntire
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Set.Operations
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.RgEis GlobalTheory.CompanionTheory.SiegelFrame
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_K_type_decomposition : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (Γ K P : Subgroup G) (c : G → ℂ) (η : G → ℝ), IsCh Γ P c → (∀ r ∈ P, r ∈ K → η r = 0) → (∀ p ∈ P, ∀ q ∈ P, η (p * q) = η p + η q) → ∀ (f : G → ℂ) (u : ℂ), Continuous f → (∀ p ∈ P, ∀ x, f (p * x) = c p * Complex.exp (u * η p) * f x) → FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : K => fun x => f (x * (k : G)))) → ∃ (d : ℕ) (ρ : K →* ((Fin d → ℂ) →L[ℂ] (Fin d → ℂ))) (w : Fin d → ℂ) (e : (Fin d → ℂ) →L[ℂ] ℂ), Continuous ρ ∧ w ∈ secSp K P c ρ ∧ ∀ k : K, e (ρ k⁻¹ w) = f k := by
  first | exact @GlobalTheory.CompanionTheory.SiegelRep.exists_rep | exact GlobalTheory.CompanionTheory.SiegelRep.exists_rep | (intros; apply GlobalTheory.CompanionTheory.SiegelRep.exists_rep <;> assumption)
