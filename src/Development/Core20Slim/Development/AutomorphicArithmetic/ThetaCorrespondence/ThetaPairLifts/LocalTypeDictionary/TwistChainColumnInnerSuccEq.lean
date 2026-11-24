module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalVectorDownEdgeInterior
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.TensorGiven
public import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
public import Development.AbelianVarietyTheory.Definitions.Divisors.BplusOfEquivariant
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsNotRelZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.InvVolConjLevelOne
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
public import Development.Core20Slim.Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
public import Development.Core20Slim.Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.StepUnfold
public import Formalism.LocalRingCardinality.DataParams₂
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.Divisibility.LiftLat
public import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.NumberTheory.NumberField.Basic

@[expose] public section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.ChainCol
noncomputable section
namespace GlobalTheory.ChainCol
attribute [local instance] Formalism.BasicNotions.Host.cmStar
theorem chainColumn_inner_succ : FunPr.ThetaLocalInputs → RowClaim.Big fun {D} _ _ _ _ {T} _ _ _ _ _ {R} ch => ∀ (t : T) (j : Fin D.R.m) (g : Sch ch.G (.down t 0 j)), (j : ℕ) + 1 < D.R.m → HEq g (R.vY t j) → ∃ c : ℂˣ, c ∈ xiVals R.toLevCh t ∧ ∀ e : AE D, IsIdemSum e (locPl ch.G t) → ∀ Φ : ch.G.Datum, IsLocVec ch.W (.mu t 0 j) e (ch.rm.vT 0 j) ((c : ℂ) • FlipStart.givenFn ch.S.B t Φ e (.down t 0 j)) g := by
  intro _
  refine ⟨0, fun ε CF _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F s ch hch _ => ?_⟩⟩
  intro t j g hj hg
  exact ⟨1, one_mem _, fun e he Φ => locVec_col s ch hch t j g hj hg e he Φ⟩
end GlobalTheory.ChainCol
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twist_chainColumn_inner_succ_eq : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.RowClaim.Big fun {D} _ _ _ _ {T} _ _ _ _ _ {R} ch => ∀ (t : T) (j : Fin D.R.m) (g : Sch ch.G (.down t 0 j)), (j : ℕ) + 1 < D.R.m → HEq g (R.vY t j) → ∃ c : ℂˣ, c ∈ xiVals R.toLevCh t ∧ ∀ e : AE D, IsIdemSum e (locPl ch.G t) → ∀ Φ : ch.G.Datum, IsLocVec ch.W (.mu t 0 j) e (ch.rm.vT 0 j) ((c : ℂ) • GlobalTheory.FlipStart.givenFn ch.S.B t Φ e (.down t 0 j)) g := by
  first | exact @_root_.GlobalTheory.ChainCol.chainColumn_inner_succ | exact _root_.GlobalTheory.ChainCol.chainColumn_inner_succ | (intros; apply _root_.GlobalTheory.ChainCol.chainColumn_inner_succ <;> assumption)
end
