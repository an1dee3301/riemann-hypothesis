module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottomTriangleIntegralsNeZero
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
public import Development.Core20Slim.Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BigThetaNormEqRallisInnerProduct
public import Development.Core20Slim.Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BottomThetaNormEqProdLocalFactors
public import Mathlib
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.BottomExistsIntegrable
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnitCharTriangle
public import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
public import Development.AbelianVarietyTheory.Definitions.Divisors.EntireEqOfHalfPlane
public import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.MemHalfCosetSelf
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataParams₂
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.BinderNameHint
public import Init.Classical
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Function
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Subgroup.Actions
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Algebra.Order.ZeroLEOne
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Cast.Order.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.Tactic.Push

@[expose] public section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.NonVanBottom
theorem bottom_theta_lift_ne_zero : FunPr.ThetaLocalInputs → IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching → LNe →
    GBig fun {D} T _ _ G _ _ _ _ => ∀ (W : G.Weil) (i j : Fin D.R.m) (A A' WW : HSp D) (X : Tri T A A' WW),
      IsBottomTri W i j X → ∀ t : T, (∃ P h, X.I W.ψ W.θ t P h ≠ 0) ∧ ∃ P' h, X.I' W.ψ W.θ t P' h ≠ 0 := by
  intro hP hK hM hL
  obtain ⟨a1, h1⟩ := _root_.GlobalTheory.T.rallis_inner_product_big_theta_lift hP
  obtain ⟨a2, h2⟩ := _root_.GlobalTheory.T.bottom_theta_norm_eq_prod_local_factors hP.howeDualityReal hP hK hM hL
  obtain ⟨a3, h3⟩ := hL
  refine ⟨max (max a1 a2) a3, fun ε CF hCF => ?_⟩
  obtain ⟨C1, x1, k1⟩ := h1 ε CF (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hCF)
  obtain ⟨C2, x2, k2⟩ := h2 ε CF (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hCF)
  obtain ⟨C3, x3, k3⟩ := h3 ε CF (le_trans (le_max_right _ _) hCF)
  refine ⟨max (max C1 C2) C3, max (max x1 x2) x3, fun C hC D large₂ he hx hr T Lc μ₀ hμ G W i j A A' WW X hX t => ?_⟩
  have n1 := k1 C (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hC) D large₂ he
    (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx) hr T Lc μ₀ hμ G W i j A A' WW X hX t
  have n2 := k2 C (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hC) D large₂ he
    (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx) hr T Lc μ₀ hμ G W i j A A' WW X hX
  obtain ⟨Λ, hΛ, hne⟩ := ((k3 C (le_trans (le_max_right _ _) hC) D large₂ he (le_trans (le_max_right _ _) hx) hr T Lc μ₀ hμ G) i j).1 t
  have hh : ((h0 D i j : ℕ) : ℤ) ≤ (halfRank D i j : ℤ) := by exact_mod_cast squareBottomHalfRankSum_le_halfRank D i j
  obtain ⟨P, ν, 𝓕, c, hc, -, -, hf⟩ := n1
  obtain ⟨Pi, p, p', J, -, ⟨P', hP'⟩, hJ, hI, hI'⟩ := n2
  obtain ⟨y, hy⟩ := exists_ne_zero_of_norm_formula hc (fun s hs hs' => hne s hs (hs'.trans hh)) (hf Λ hΛ)
  refine ⟨⟨P, y, hy⟩, P', ?_⟩
  obtain ⟨lam, hlam⟩ := hI t
  have hinj : Function.Injective (J t) := by
    refine (hJ t).resolve_left fun h0 => hy ?_
    rw [hlam P, h0]
    simp
  by_contra hc'
  push_neg at hc'
  apply hP'
  apply hinj
  rw [← hI' t P', map_zero]
  exact funext hc'
end GlobalTheory.NonVanBottom
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.first_occurrence_theta_lift_ne_zero : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching → LNe → GBig fun {D} T _ _ G _ _ _ _ => ∀ (W : G.Weil) (i j : Fin D.R.m) (A A' WW : HSp D) (X : Tri T A A' WW), IsBottomTri W i j X → ∀ t : T, (∃ P h, X.I W.ψ W.θ t P h ≠ 0) ∧ ∃ P' h, X.I' W.ψ W.θ t P' h ≠ 0 := by
  first | exact @_root_.GlobalTheory.NonVanBottom.bottom_theta_lift_ne_zero | exact _root_.GlobalTheory.NonVanBottom.bottom_theta_lift_ne_zero | (intros; apply _root_.GlobalTheory.NonVanBottom.bottom_theta_lift_ne_zero <;> assumption)
end
