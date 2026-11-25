module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
public import Mathlib
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.BottomExistsIntegrable
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottomTrianglePolynomialSurjection
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HypothesesAbsDet
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottomTriangleIntegralsNeZero
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
public import Development.Core20Slim.Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BottomTripleIntegralFactorizationOfReal
public import Development.Core20Slim.Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.FirstOccurrenceThetaLiftNeZero
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnitCharTriangle
public import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.MemHalfCosetSelf
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataParams₂
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Classical
public import Init.Core
public import Init.Data.Function
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Category.ModuleCat.Basic
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
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.MinMax
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.ConstRatio
theorem bottom_triple_integral_factorization (hPr : FunPr.ThetaLocalInputs) (hK : IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree)
    (hM : IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching) (hL : LNe) :
    GBig fun {D} T _ _ G _ _ _ _ => ∀ W : G.Weil, IsStdChar D W.ψ (-1) → ∀ (i j : Fin D.R.m) (A A' WW : HSp D)
      (X : IndefiniteRowSideFullHecke.UnitCharTriangle.Tri T A A' WW), IsBottomTri W i j X → ∃ lam : T → ℂ, Factor X W.ψ W.θ lam := by
  obtain ⟨c, h⟩ := _root_.GlobalTheory.T.bottom_triple_integral_factorization_of_real hPr hK hM
  obtain ⟨c', h'⟩ := _root_.GlobalTheory.T.first_occurrence_theta_lift_ne_zero hPr hK hM hL
  refine ⟨max c c', fun ε CF hCF => ?_⟩
  obtain ⟨C0, x0, h⟩ := h ε CF (le_of_max_le_left hCF)
  obtain ⟨C1, x1, h'⟩ := h' ε CF (le_of_max_le_right hCF)
  refine ⟨max C0 C1, max x0 x1, fun C hC D large₂ a b r T Lc μ hLc G W hW i j A A' WW X hX => ?_⟩
  obtain ⟨Pi, p, p', J, hs, hJ, hlam, hI'⟩ :=
    h C (le_of_max_le_left hC) D large₂ a (le_of_max_le_left b) r T Lc μ hLc G W hW i j A A' WW X hX
  have hnv := h' C (le_of_max_le_right hC) D large₂ a (le_of_max_le_right b) r T Lc μ hLc G W i j A A' WW X hX
  obtain ⟨P', g', hg'⟩ := (hnv μ).2
  have hP' : p' P' ≠ 0 := fun h0 => hg' (by rw [hI' μ P', h0]; simp)
  choose lam hlam using hlam
  have key : ∀ t, lam t ≠ 0 ∧ Function.Injective (J t) := fun t => by
    obtain ⟨P, g, hPg⟩ := (hnv t).1
    rw [hlam t P] at hPg
    refine ⟨fun h0 => hPg (by simp [h0]), (hJ t).resolve_left fun h0 => hPg (by simp [h0])⟩
  refine ⟨lam, fun t => (key t).1, Pi, p, p', J, hs, fun t => (key t).2, fun t P g => (hX.integrable t).1 P g,
    fun t P => hlam t P, fun t P' _ => hI' t P', P', hP', fun t g => (hX.integrable t).2 P' g⟩
end GlobalTheory.ConstRatio
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bottom_triple_integral_eq_const_mul_local : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching → LNe → GBig fun {D} T _ _ G _ _ _ _ => ∀ W : G.Weil, IsStdChar D W.ψ (-1) → ∀ (i j : Fin D.R.m) (A A' WW : HSp D) (X : GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.Tri T A A' WW), IsBottomTri W i j X → ∃ lam : T → ℂ, GlobalTheory.ConstRatio.Factor X W.ψ W.θ lam := by
  first | exact @_root_.GlobalTheory.ConstRatio.bottom_triple_integral_factorization | exact _root_.GlobalTheory.ConstRatio.bottom_triple_integral_factorization | (intros; apply _root_.GlobalTheory.ConstRatio.bottom_triple_integral_factorization <;> assumption)
end
