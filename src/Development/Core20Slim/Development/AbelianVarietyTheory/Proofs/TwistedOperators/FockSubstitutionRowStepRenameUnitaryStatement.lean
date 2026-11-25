module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockSubstitutionRowStepRenameUnitary
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqConjOfInFrame
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.MinorOrderedEntries
public import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowSizesNR
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Fin.Basic
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Basic
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.Order.Basic
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries
open scoped TensorProduct Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockSubstitution_rowStep_rename_unitary : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (j : Fin D.R.m)
    (u : UG D.what₂.Tau ((GlobalTheory.RowReal.rowSizes D).nR j)) (v : UG D.what₂.Tau ((GlobalTheory.RowReal.rowSizes D).nR (j + 1)))
    (Q : PolF D (G.V (.top (j + 1))).rank (G.V (.top j)).rank),
    GlobalTheory.RowReal.trCol G j (GlobalTheory.RowReal.fockSubAll (fun _ => (G.V (.top j)).rank) (fun _ => (G.V (.top (j + 1))).rank)
      (fun τ => ((u τ : Matrix.unitaryGroup _ ℂ) : Matrix _ _ ℂ).submatrix (Fin.cast (GlobalTheory.RowReal.rank_top G (j := j) j.2.le))
        (Fin.cast (GlobalTheory.RowReal.rank_top G (j := j) j.2.le)))
      (fun τ => ((v τ : Matrix.unitaryGroup _ ℂ) : Matrix _ _ ℂ).submatrix (Fin.cast (GlobalTheory.RowReal.rank_top G (j := j + 1) j.2))
        (Fin.cast (GlobalTheory.RowReal.rank_top G (j := j + 1) j.2))) Q) =
      linSub (homMat _ _ (u, v)) (GlobalTheory.RowReal.trCol G j Q) := by
  first | exact @GlobalTheory.RowReal.trCol_fockSubAll_unitary | exact GlobalTheory.RowReal.trCol_fockSubAll_unitary | (intros; apply GlobalTheory.RowReal.trCol_fockSubAll_unitary <;> assumption)
