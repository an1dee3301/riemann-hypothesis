module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteBottomRowTransportContragredient
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinPt
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplTupBijective
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityReal
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdMinorsMemInv
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasInfExpDiv
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedSmooth
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Data.Cast
public import Init.Data.Rat.Basic
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.definite_bottom_row_transport_contragredient : ∀ (D : D7) (M M' X : HSp D) (A : GlobalTheory.ChainFr.Fr M) (A' : GlobalTheory.ChainFr.Fr M') (B : GlobalTheory.ChainFr.Fr X)
    (eS eS' : D.what₂.Tau → ℚ) (n₀ : D.what₂.Tau → ℕ) (Q : Type) [AddCommGroup Q] [Module ℂ Q]
    (q : PolF D X.rank M.rank →ₗ[ℂ] Q) (q' : PolF D X.rank M'.rank →ₗ[ℂ] Q),
    (∀ τ j, A.ε τ j = true) → (∀ τ j, A'.ε τ j = true) → (∀ τ i, B.ε τ i = true) →
    (∀ τ, (n₀ τ : ℚ) = eS τ - eS' τ - ((M.rank : ℚ) + (M'.rank : ℚ)) / 2) →
    (∀ P P', q P = q' P' → ∀ τ, ∀ Y ∈ lieAt X τ,
      q (GlobalTheory.RealQuot.actT true A B eS τ Y P) = q' (GlobalTheory.RealQuot.actT false A' B eS' τ Y P')) →
    ∀ (κ : D.what₂.Tau → Matrix.unitaryGroup (Fin X.rank) ℂ) (P : PolF D X.rank M.rank) (P' : PolF D X.rank M'.rank), q P = q' P' →
      q' (GlobalTheory.MinorFrame.rowSub (fun τ => (κ τ : Matrix (Fin X.rank) (Fin X.rank) ℂ)) P') =
        GlobalTheory.MinorFrame.detChar n₀ (fun τ => (κ τ : Matrix (Fin X.rank) (Fin X.rank) ℂ)) •
          q (GlobalTheory.MinorFrame.rowSub (fun τ => (κ τ : Matrix (Fin X.rank) (Fin X.rank) ℂ).map (starRingEnd ℂ)) P) := by
  first | exact @GlobalTheory.RowTransport.row_transport | exact GlobalTheory.RowTransport.row_transport | (intros; apply GlobalTheory.RowTransport.row_transport <;> assumption)
