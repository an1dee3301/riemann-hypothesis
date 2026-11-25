module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspidalGridNodeType
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.RangeSndRel
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsAllTiedNotStable
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesHermitianUniqueOfClassification
public import Development.Core20Slim.Development.AbelianVarietyTheory.BlockTheory.HeightDefect.FinitePartTypes
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.HeightProofs.AutomorphicFormUniformLimitDiscreteSeriesSeriesStatement
public import Batteries.Classes.RatCast
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HermitianOrthogonalExtensionData
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.HeightProofs.TypeAtOfDiscreteSeries
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqUniqueOfClassification
public import Formalism.FormalDegreeBessel.StatementDS
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Pi
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Filter
public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Multilinear.Basic
public import Mathlib.LinearAlgebra.PiTensorProduct.Basic
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Fin.Basic
public import Mathlib.Order.Monotone.Defs

@[expose] public section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
noncomputable section
namespace GlobalTheory.CuspValueType
section Model
open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum
variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
end Model
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Mult Matrix
open GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum
end GlobalTheory.CuspValueType
theorem GlobalTheory.CuspValueType.hasTypeAt_cusp_of_cusp_value_type : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {D : D7} (θ : InfFam D), IsInfFam (D := D) θ → ∀ (N : GlobalTheory.Grid.Node D), N.V.SigOK → ∀ F ∈ N.Cusp θ, ∀ (w : SmT N.M) (τ : D.what₂.Tau), GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.HasTypeAt θ N.V τ (N.S τ) (F w) := by
  intro hP D θ hθ N hN F hF w τ
  have hgood : GoodPar N.V.rank (N.V.sig (tauE D τ)).1 (N.V.sig (tauE D τ)).2 (N.S τ) :=
    ⟨N.M.lam τ, N.M.ε τ, N.M.enum τ, GlobalTheory.Published.HermitianUnique.isHCParam_of_isDS (N.M.enum τ).1 (N.M.ds τ),
      GlobalTheory.TypeAtCompare.card_eq_of_congr (N.M.fr_unit τ) (N.M.fr_gram τ) (hN (tauE D τ))⟩
  have key : ∀ T, Mult.IsMultMap θ N.M ∅ 1 T → ∀ v, T v ∈ GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.typeSub θ N.V τ (N.S τ) := fun T hT v =>
    GlobalTheory.SeriesToClosure.hasTypeAt_of_isTypeAt θ N.V τ (N.S τ) (T v) hP.discreteSeriesUpqExists
      (GlobalTheory.Published.discreteSeriesHermitianUnique_iff.1 hP.discreteSeriesHermitianUnique) hP.harishChandraModules
      hP.casselmanWallach hθ hN hgood (hT.aut v)
      (GlobalTheory.CuspValueType.isTypeAt_value θ hP.harishChandraModules N.M hT v τ)
  have main : ∀ T ∈ Mult.Mult θ N.M ∅ 1, ∀ w, PiTensorProduct.lift T w ∈ GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.typeSub θ N.V τ (N.S τ) := by
    intro T hT
    induction hT using Submodule.span_induction with
    | mem T hT =>
      intro w
      induction w using PiTensorProduct.induction_on with
      | smul_tprod r v =>
        rw [map_smul, PiTensorProduct.lift.tprod]
        exact Submodule.smul_mem _ r (key T hT v)
      | add a b ha hb =>
        rw [map_add (f := _)]
        exact Submodule.add_mem _ ha hb
    | zero =>
      intro w
      simp only [map_zero, LinearMap.zero_apply]
      exact Submodule.zero_mem _
    | add a b _ _ ha hb =>
      intro w
      rw [map_add (f := _), LinearMap.add_apply]
      exact Submodule.add_mem _ (ha w) (hb w)
    | smul c a _ ha =>
      intro w
      rw [map_smul, LinearMap.smul_apply]
      exact Submodule.smul_mem _ c (ha w)
  have hF' := (Mult.mem_multT θ N.M ∅ 1 F).1 hF
  have eF : F = PiTensorProduct.lift (PiTensorProduct.lift.symm F) := (LinearEquiv.apply_symm_apply _ F).symm
  rw [eF]
  exact main _ hF' w
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cusp_value_has_prescribed_type : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {D : D7} (θ : InfFam D), IsInfFam (D := D) θ → ∀ (N : GlobalTheory.Grid.Node D), N.V.SigOK → ∀ F ∈ N.Cusp θ, ∀ (w : SmT N.M) (τ : D.what₂.Tau), GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.HasTypeAt θ N.V τ (N.S τ) (F w) := by
  first | exact @_root_.GlobalTheory.CuspValueType.hasTypeAt_cusp_of_cusp_value_type | exact _root_.GlobalTheory.CuspValueType.hasTypeAt_cusp_of_cusp_value_type | (intros; apply _root_.GlobalTheory.CuspValueType.hasTypeAt_cusp_of_cusp_value_type <;> assumption)
end
