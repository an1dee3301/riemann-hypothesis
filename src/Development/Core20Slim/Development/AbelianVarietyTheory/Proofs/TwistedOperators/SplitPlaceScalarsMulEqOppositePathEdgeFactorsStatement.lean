module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPlaceScalarsMulEqOppositePathEdgeFactors
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairPtsClasses
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairPtsEqSum
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.MovFn
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.DetIdlVal
public import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.InvVolConjLevelOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Formalism.LocalToGlobal.HeckeThetaElements.IsHeckeElt
public import Formalism.LocalToGlobal.HermitianColumns.InLocalDiscriminantKernel
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.List.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Notation.Pi.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.RowVertexInv GlobalTheory.SplitFlip
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.RowVacScalar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlaceScalars_mul_eq_oppositePath_edgeFactors : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}
    (S : GridChoice W U) {t : T}, t ∈ U → ∀ (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.grid (j + 1) D.R.m)),
    finG (G.V (.grid (j + 1) D.R.m)) k ∈ S.levRow t (j + 1) hj.le → ∀ w ∈ locPl G t, (∃ e : AE D, Formalism.L2.NTheta.IsIdemAt e w) →
    GlobalTheory.RowVacScalar.splitScal G (.chi j D.R.m) w (G.toPair (.chi j D.R.m) 1 (moved S j k)).1
                 (G.toPair (.chi j D.R.m) 1 (moved S j k)).2 *
      GlobalTheory.RowVacScalar.splitScal G (.chi (j + 1) D.R.m) w (G.toPair (.chi (j + 1) D.R.m) (moved S j k) 1).1
        (G.toPair (.chi (j + 1) D.R.m) (moved S j k) 1).2 =
    ((oppositePath D.R.m).map ((locGrid G t w).edgeFactor .one (Pi.mulSingle (j + 1, D.R.m)
      (inBasis (rank_vertex G t w (X := (j + 1, D.R.m)) ⟨hj.le, le_rfl⟩) (S.B.β (j + 1) D.R.m) w
        (finG (G.V (.grid (j + 1) D.R.m)) k))))).prod := by
  first | exact @GlobalTheory.RowVacScalar.splitScal_mul_eq_oppositePath | exact GlobalTheory.RowVacScalar.splitScal_mul_eq_oppositePath | (intros; apply GlobalTheory.RowVacScalar.splitScal_mul_eq_oppositePath <;> assumption)
