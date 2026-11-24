module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.GrowthSobolevCauchyTendstoSmoothLimit
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsGrowthSobNeTopOfIsAutFunSm
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.RWordRTrAdelic
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsModGrowthExpLeNormInfPow
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemSmoothFunctionsOfClosedRightDerivatives
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsCuspFunctionClosedUnderOperations
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DifferentiableOneP
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Nat.Basic
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Basic
public import Mathlib.Order.Filter.AtTopBot.Defs
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.Notation
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Order.Real
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.growthSobolev_cauchy_tendsto_smooth_limit : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (N : ℕ) (ψ : ℕ → GA D V → ℂ), (∀ n, Continuous (ψ n) ∧ ψ n ∈ GlobalTheory.Mem.AutSpace.SmFun θ V ∧ ∀ d, GlobalTheory.Size.growthSob θ V d N (ψ n) ≠ ⊤) → (∀ d, Filter.Tendsto (fun p : ℕ × ℕ => GlobalTheory.Size.growthSob θ V d N (ψ p.1 - ψ p.2)) Filter.atTop (nhds 0)) → ∃ f : GA D V → ℂ, Continuous f ∧ f ∈ GlobalTheory.Mem.AutSpace.SmFun θ V ∧ ∀ d, Filter.Tendsto (fun n => GlobalTheory.Size.growthSob θ V d N (ψ n - f)) Filter.atTop (nhds 0) := by
  first | exact @GlobalTheory.GrowthComplete.complete | exact GlobalTheory.GrowthComplete.complete | (intros; apply GlobalTheory.GrowthComplete.complete <;> assumption)
