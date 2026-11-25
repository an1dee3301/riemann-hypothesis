module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.FirstVertexWeilOrbitValue
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.StepUnfold
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairPtsClasses
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowMapVUpdateZero
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.EdgeFactorNeZero
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.StepType
public import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.InvVolConjLevelOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.Core20Slim.Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataParams₂
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Formalism.LocalToGlobal.Divisibility.LiftLat
public import Formalism.LocalToGlobal.HermitianColumns.InLocalDiscriminantKernel
public import Formalism.LocalToGlobal.IndefiniteReal.Bridge
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Notation.Pi.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Sets
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open Matrix ValuativeRel GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.RowVacScalar GlobalTheory.FirstRowTermLaw GlobalTheory.FirstRowEndLaw
noncomputable section
namespace GlobalTheory.FirstRowScalar
variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts}
variable {G : GridData L sc} {W : G.Weil} {U : Set T}
section Red
open GlobalTheory.FunObj.Comparison₂
variable {S κ K : Type} [CommRing S] [CommRing κ] [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] {φ : S →+* κ} {ψ : S →+* K} {r t j a : ℕ} {ea : Ix (Fin r) (Fin t) j ≃ Fin a}
end Red
theorem firstRow_scalar_multiple : FunPr.ThetaLocalInputs → SumOKK → Big fun {D} {_Γ} _ _ {_Pl0} {T} {_A} {_Ks} _ _ _ {R} ch =>
    ∀ (t : T) (k : FinPt ch.G (.grid 0 D.R.m)), finG (ch.G.V (.grid 0 D.R.m)) k ∈ ch.S.levRow t 0 (Nat.zero_le _) →
    ∀ (hk : toXf k ∈ (levEnv D.sp.X' R.βX (R.datXt t)).J) (c : ℂ),
      ch.W.om (.chi (FirstRowVertex.firstIx D) D.R.m : Pair T) (ch.G.toPair (.chi (FirstRowVertex.firstIx D) D.R.m : Pair T) ((ch.S.N.u (.grid 0 D.R.m))⁻¹ * k * ch.S.N.u (.grid 0 D.R.m)).1 1) (ch.S.Z.vac (.chi (FirstRowVertex.firstIx D) D.R.m : Pair T)) = c • ch.S.Z.vac (.chi (FirstRowVertex.firstIx D) D.R.m : Pair T) →
      (((levEnv D.sp.X' R.βX (R.datXt t)).χ ⟨toXf k, hk⟩ : ℂˣ) : ℂ) * c *
          ∏ w : locPl ch.G t, FirstRowEndLaw.endLam ch.G t w.1 (FirstRowTermLaw.kapAt ch.S.toGridChoice t w.1 k) =
        ∏ w : locPl ch.G t, (locGrid ch.G t w).edgeFactor .one
          (Pi.mulSingle (0, D.R.m) (FirstRowTermLaw.kapAt ch.S.toGridChoice t w k)) (.ex 0 D.R.m) :=
  fun _ _ => ⟨0, fun _ _ _ => ⟨0, fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s ch _ _ t k hk hk' c hc =>
    scalar_of_is ch.S.toGridChoice s.core.lev t k hk hk' c hc⟩⟩
end GlobalTheory.FirstRowScalar
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twist_firstRow_scalar_multiple : _root_.GlobalTheory.FunPr.ThetaLocalInputs → SumOKK → Big fun {D} {_Γ} _ _ {_Pl0} {T} {_A} {_Ks} _ _ _ {R} ch =>
    ∀ (t : T) (k : FinPt ch.G (.grid 0 D.R.m)), finG (ch.G.V (.grid 0 D.R.m)) k ∈ ch.S.levRow t 0 (Nat.zero_le _) →
    ∀ (hk : toXf k ∈ (levEnv D.sp.X' R.βX (R.datXt t)).J) (c : ℂ),
      ch.W.om (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) (ch.G.toPair (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) ((ch.S.N.u (.grid 0 D.R.m))⁻¹ * k * ch.S.N.u (.grid 0 D.R.m)).1 1) (ch.S.Z.vac (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T)) = c • ch.S.Z.vac (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) →
      (((levEnv D.sp.X' R.βX (R.datXt t)).χ ⟨toXf k, hk⟩ : ℂˣ) : ℂ) * c *
          ∏ w : locPl ch.G t, GlobalTheory.FirstRowEndLaw.endLam ch.G t w.1 (GlobalTheory.FirstRowTermLaw.kapAt ch.S.toGridChoice t w.1 k) =
        ∏ w : locPl ch.G t, (locGrid ch.G t w).edgeFactor .one
          (Pi.mulSingle (0, D.R.m) (GlobalTheory.FirstRowTermLaw.kapAt ch.S.toGridChoice t w k)) (.ex 0 D.R.m) := by
  first | exact @_root_.GlobalTheory.FirstRowScalar.firstRow_scalar_multiple | exact _root_.GlobalTheory.FirstRowScalar.firstRow_scalar_multiple | (intros; apply _root_.GlobalTheory.FirstRowScalar.firstRow_scalar_multiple <;> assumption)
end
