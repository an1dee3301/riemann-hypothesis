module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
public import Development.Core20Slim.Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralGoodFormValuesMemScaledDualWeylLattice
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseTupleGoodFormValuesBoundedByClassSum
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardLevelQuotientGroupLeProdAbsNormPowSq
public import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
public import Development.AbelianVarietyTheory.Definitions.Divisors.InvVolConjLevelOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.MemHalfCosetSelf
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousCoeffBlockAct
public import Development.Core20Slim.Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataParams₂
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.Divisibility.ClassSum
public import Formalism.LocalToGlobal.Divisibility.CoefMod
public import Formalism.LocalToGlobal.Divisibility.LiftLat
public import Formalism.LocalToGlobal.Divisibility.RowLat
public import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
public import Formalism.LocalToGlobal.IndefiniteReal.Bridge
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.QuotientMetricDivisors.Statement
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.SetTheory.Cardinal.Finite

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FormVal

theorem bigC_and {Q Q' : ChQ} (h : BigC Q) (h' : BigC Q') : BigC fun F ch C b => Q F ch C b ∧ Q' F ch C b := by
  obtain ⟨A0, hA⟩ := h
  obtain ⟨B0, hB⟩ := h'
  refine ⟨max A0 B0, fun CF hCF => ?_⟩
  obtain ⟨C1, hC1⟩ := hA CF (le_trans (le_max_left _ _) hCF)
  obtain ⟨C2, hC2⟩ := hB CF (le_trans (le_max_right _ _) hCF)
  refine ⟨max C1 C2, fun ε C hC => ?_⟩
  obtain ⟨x1, hx1⟩ := hC1 ε C (le_trans (le_max_left _ _) hC)
  obtain ⟨x2, hx2⟩ := hC2 ε C (le_trans (le_max_right _ _) hC)
  refine ⟨max x1 x2, ?_⟩
  intro D large₂ hε hx Γ _ _ Pl0 T A Ks _ _ _ R F hS ch hIs hAt hOK
  exact ⟨hx1 D large₂ hε (le_trans (le_max_left _ _) hx) Γ Pl0 T A Ks R F hS ch hIs hAt hOK,
    hx2 D large₂ hε (le_trans (le_max_right _ _) hx) Γ Pl0 T A Ks R F hS ch hIs hAt hOK⟩

theorem bigC_mono {Q Q' : ChQ} (h : BigC Q) (hQ : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type}
    {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}
    (F : Face D A) (ch : Choice R) (C b : ℝ), Q F ch C b → Q' F ch C b) : BigC Q' := by
  obtain ⟨a, h⟩ := h
  refine ⟨a, fun CF hCF => ?_⟩
  obtain ⟨c, h⟩ := h CF hCF
  refine ⟨c, fun ε C hC => ?_⟩
  obtain ⟨x, h⟩ := h ε C hC
  exact ⟨x, fun D large₂ e hx Γ _ _ Pl0 T A Ks _ _ _ R F s ch i j k => hQ F ch C large₂.sc.b (h D large₂ e hx Γ Pl0 T A Ks R F s ch i j k)⟩

set_option maxHeartbeats 1600000 in
theorem form_fin_inf_of (h1 : BigC fun {D} {_} _ _ {_} {_} {A} {_} _ _ _ {R} F ch _ _ => ∀ (t : _) (w : PlL D), ∀ x ∈ (A.fam.R t).Mt (A.fam.lvl F.P0 F.ψ0), ∀ y,
  InLat _ w 0 (latAt ch.S.toGridChoice (.grid 0 D.R.m) y) (rowVal ch.S.toGridChoice (ch.S.formC t (R.jX t (formOf F t x)) y))) (h2 : BigC fun {D} {_} _ _ {_} {_} {A} {_} _ _ _ {R} F ch _ _ => ∀ (σ : D.what₂.LL →+* ℂ) (x : Fin ((A.fam.R A.μ0).nV (A.fam.lvl F.P0 F.ψ0)) → D.what₂.LL),
  0 ≤ (star (fun i => σ (x i)) ⬝ᵥ (((A.fam.R A.μ0).HV (A.fam.lvl F.P0 F.ψ0)).map σ).mulVec fun i => σ (x i)).re ∧ ∀ y,
  NrmLe _ σ (rowVal ch.S.toGridChoice (ch.S.formC A.μ0 (R.jX A.μ0 (formOf F A.μ0 x)) y))
    ((Nat.card (A.fam.lvl F.P0 F.ψ0).P : ℝ) * ((A.fam.R A.μ0).S.DGam : ℝ) *
      (star (fun i => σ (x i)) ⬝ᵥ (((A.fam.R A.μ0).HV (A.fam.lvl F.P0 F.ψ0)).map σ).mulVec fun i => σ (x i)).re)) (h3 : BigC fun {D} {_} _ _ {_} {_} {A} {_} _ _ _ {R} F ch C b => 0 ≤ bOne ch.G C b ∧
  (Nat.card (A.fam.lvl F.P0 F.ψ0).P : ℝ) * ((A.fam.R A.μ0).S.DGam : ℝ) ≤ Real.exp (D.R.m * aOne ch.G C b)) : FinFormK ∧ InfFormK := by
  refine ⟨bigC_mono (bigC_and h1 h3) ?_, bigC_mono (bigC_and h2 h3) ?_⟩
  · rintro D Γ _ _ Pl0 T A Ks _ _ _ R F ch C b ⟨hv, hb, -⟩
    refine ⟨fun _ => 0, ⟨fun _ => le_rfl, by simp, fun s => by simpa using hb⟩, fun t w x hx y => ?_⟩
    exact hv t w x hx y
  · rintro D Γ _ _ Pl0 T A Ks _ _ _ R F ch C b ⟨hv, -, hK⟩ σ x y
    obtain ⟨hq, hy⟩ := hv σ x
    obtain ⟨u, e, hu⟩ := hy y
    exact ⟨u, e, hu.trans (mul_le_mul_of_nonneg_right hK hq)⟩

end GlobalTheory.FormVal

end
