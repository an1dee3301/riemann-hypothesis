module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ComplexDerivativeRightDerivativeCommutator
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsGrowthSobNeTopOfIsAutFunSm
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.RWordRTrAdelic
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsModGrowthExpLeNormInfPow
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemSmoothFunctionsOfClosedRightDerivatives
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsCuspFunctionClosedUnderOperations
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
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Prelude
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complexDerivative_rightDerivative_commutator : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (τ τ' : D.what₂.Tau) (Z : Matrix (Fin V.rank) (Fin V.rank) ℂ), ∀ X ∈ lieAt V τ, ∀ φ ∈ GlobalTheory.Mem.AutSpace.SmFun θ V, (RderC θ V τ Z (Rder θ V τ X φ) = Rder θ V τ X (RderC θ V τ Z φ) + RderC θ V τ (Z * X - X * Z) φ) ∧ (τ' ≠ τ → RderC θ V τ' Z (Rder θ V τ X φ) = Rder θ V τ X (RderC θ V τ' Z φ)) := by
  first | exact @GlobalTheory.DerBracket.RderC_Rder | exact GlobalTheory.DerBracket.RderC_Rder | (intros; apply GlobalTheory.DerBracket.RderC_Rder <;> assumption)
