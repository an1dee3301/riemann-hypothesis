module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSmoothCuspFormFrechetModerateGrowthRep
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DifferentiableOneP
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedSmooth
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Function
public import Init.Prelude
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Normed.Module.Seminorm.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Notation
public import Mathlib.Topology.Algebra.IsUniformGroup.Defs
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.UniformSpace.Cauchy
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_smoothCuspForm_frechet_moderateGrowth_rep : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (A : GlobalTheory.ChainFr.Fr V) (U : Subgroup (GA D V)) (N : ℕ), IsOpen (U : Set (GA D V)) → ∃ (E : Type) (_ : AddCommGroup E) (_ : Module ℂ E) (_ : UniformSpace E) (_ : IsUniformAddGroup E) (_ : CompleteSpace E) (_ : T2Space E) (p : ℕ → Seminorm ℂ E) (ι : E →ₗ[ℂ] (GA D V → ℂ)), Function.Injective ι ∧ (∀ φ, φ ∈ Set.range ι ↔ Continuous φ ∧ (∀ γ ∈ GQ V, ∀ g, φ (γ * g) = φ g) ∧ (∀ k ∈ U, k ∈ GfC V → ∀ g, φ (g * k) = φ g) ∧ φ ∈ GlobalTheory.Mem.AutSpace.SmFun θ V ∧ IsCuspFun V φ ∧ ∀ d, GlobalTheory.Size.growthSob θ V d N φ ≠ ⊤) ∧ (∀ d x, p d x = (GlobalTheory.Size.growthSob θ V d N (ι x)).toReal) ∧ ∀ τ, ∃ π dπ : Matrix (Fin V.rank) (Fin V.rank) ℂ → (E →L[ℂ] E), GlobalTheory.SmoothGlob.IsSmoothModRep (A.ε τ) p π dπ ∧ (∀ g ∈ Formalism.MainNotions.S.UJset (A.ε τ), ∀ x, ι (π g x) = rTr V (A.elt θ τ g) (ι x)) ∧ ∀ X ∈ GlobalTheory.SmoothGlob.lieSet (A.ε τ), ∀ x, ι (dπ X x) = Rder θ V τ ((A.fr τ)⁻¹ * X * A.fr τ) (ι x) := by
  first | exact @GlobalTheory.CuspFrechet.exists_frechet | exact GlobalTheory.CuspFrechet.exists_frechet | (intros; apply GlobalTheory.CuspFrechet.exists_frechet <;> assumption)
