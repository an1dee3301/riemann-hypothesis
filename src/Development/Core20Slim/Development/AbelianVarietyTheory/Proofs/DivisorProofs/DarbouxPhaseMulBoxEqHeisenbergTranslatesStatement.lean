module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.DarbouxPhaseMulBoxEqHeisenbergTranslates
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsINeZeroKind
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.RouteDatumMemAlgebraicVectorsGridFrames
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasDerivAtHeisenbergOpArchimedeanSumRealPlaces
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceSecondPos
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockCreationPreservesFockVectorsTwoFrames
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFockPolynomialOperatorHeisenbergDerivative
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
public import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
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
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Invertible.Defs
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Prod
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram blkU conjU UB)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple UAt ratU mat Acts SInf)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.darbouxPhase_mul_box_eq_heisenbergTranslates : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {i j : ℕ} (e : Num G i j) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j), Γ.V.J = (1 : D.host.E) • (spW G i j).gram → Γ.W.J = skewGram (spV G i j) (spV₁ G i j) e → ∀ (ψ : AddChar (AF D.host.F) ℂ) (F₁ : WO (negSp (spW G i j)) (spV G i j) → ℂ) (F₂ : WO (spV₁ G i j) (spW G i j) → ℂ) (v w : Matrix (Fin (spW G i j).rank) (Fin ((spW G i j).rank + (spW₁ G i j).rank)) (AE D)), ψ (⅟(2 : AF D.host.F) * ((Γ.M.co.e v).1 ⬝ᵥ (Γ.M.co.e w).2 - (Γ.M.co.e w).1 ⬝ᵥ (Γ.M.co.e v).2)) * (F₁ (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.mulG (negSp (spW G i j)) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.colV e (v + w))ᵀ) * F₂ (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.adjV₁ e (v + w))) = heisO ψ (negSp (spW G i j)) (spV G i j) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.mulG (negSp (spW G i j)) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.colV e w)ᵀ) F₁ (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.mulG (negSp (spW G i j)) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.colV e v)ᵀ) * heisO ψ (spV₁ G i j) (spW G i j) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.adjV₁ e w) F₂ (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.adjV₁ e v) := by
  first | exact @GlobalTheory.BoxPhase.phase_box_heis | exact GlobalTheory.BoxPhase.phase_box_heis | (intros; apply GlobalTheory.BoxPhase.phase_box_heis <;> assumption)
