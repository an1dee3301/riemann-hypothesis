module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitVacuumEqSmulProductArrowVacua
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMixModelB
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAwayUnitOfPowEqOne
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
public import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsNotRelZero
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsGLSubmatrix
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlkGLMem
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsGridFr
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta Formalism.L2.DIV IsDedekindDomain NumberField MeasureTheory Matrix
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SqTower GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.ChainFr GlobalTheory.SquareDict GlobalTheory.SquareComm GlobalTheory.BigNZ GlobalTheory.FlipMatch GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB incM)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep Acts SInf At piW psiLoc chrW)
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopFlip

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitVacuum_eq_smul_product_arrow_vacua : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc} {μ₀ : T}, L.Is μ₀ → ∀ (W : G.Weil) (ρ : RealMatch W) (i j : Fin D.R.m) (AV : Fr (spV G i j)) (AV₁ : Fr (spV₁ G i j)),
      IsGridFr W _ AV → IsGridFr W _ AV₁ → ∀ Λ : Submodule (𝓞 D.host.E) (Fin (spX G i j).rank → D.host.E), IsSelfDualC (spX G i j) Λ →
      (latO (spW₁ G i j) (spX G i j) (G.Λ (.grid i j)) Λ (fun _ => True) : Set _) = orderingsOnSpWOne G i j →
      ∀ f, IsVacO W.ψ W.θ (spW₁ G i j) (spX G i j) (W.cart (.grid i j)) (frSum AV AV₁).cart
        (G.Λ (.grid i j)) Λ f → ∃ c : ℂ, c ≠ 0 ∧ f = c • vacB ρ i j := by
  first | exact @GlobalTheory.TopFlipVacB.vac_eq_smul_vacB | exact GlobalTheory.TopFlipVacB.vac_eq_smul_vacB | (intros; apply GlobalTheory.TopFlipVacB.vac_eq_smul_vacB <;> assumption)
