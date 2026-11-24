module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ReprMemOfCoeff
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.CoeffCoefficientSpaceActionMemRangeStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.CovariantVectorToFunctionFormCoeffMemRangeStatement
public import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
public import Development.AbelianVarietyTheory.Definitions.Divisors.InvVolConjLevelOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.MemHalfCosetSelf
public import Formalism.FrobeniusOrbits.Statement
public import Formalism.GradedWeylDivisibility.StatementD
public import Formalism.LocalRingCardinality.DataCoeff
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataParams₂
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.Divisibility.CoefMod
public import Formalism.LocalToGlobal.Divisibility.LiftLat
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ZsmulGeneratorEqZeroOfProjection
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Finsupp.SMul
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Set.CoeSort
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest Formalism.IndefR.WeilFull GlobalTheory.RowClaim

noncomputable section

namespace GlobalTheory.RowRat
open Formalism.L2.DIV MvPolynomial

theorem embLL_labLL {D : D7} (τ : D.what₂.Tau) (x : D.host.E) : D.what₂.embLL (labLL D τ x) = tauE D τ x :=
  DFunLike.congr_fun D.embE_φ₀ (D.host.sigmaOf (D.eTau τ).1 x)

theorem rowMap_coeff_mem : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R) (large₂ : SizeData₂ D) (F : Face D A), HidaSetting large₂ R F → ch.Is → ch.FieldOK → ∀ (t : T) (Φ : ch.G.Datum), ch.S.SumOK t Φ → ∀ β ∈ ch.S.supp t Φ, ∀ τ, IsCosetExpansion ch.S.toGridChoice t Φ β (expDepth ch.S.toGridChoice t Φ β) τ → ∀ d ∈ τ.support, ∀ (c : ch.S.Classes t Φ β) (v : VV ℂ (listedWt ch.G (.grid 0 D.R.m))), (∀ m, AddMonoidAlgebra.coeff v.1 m ∈ Set.range D.what₂.embLL) → ∀ m, AddMonoidAlgebra.coeff (ch.S.rowMap d (ch.S.ptRow c) v).1 m ∈ Set.range D.what₂.embLL := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R ch large₂ F _ _ hF t Φ hSum β hβ τ hτ d hd c v hv
  have h0 := GlobalTheory.T.covariantVectorToFunctionForm_coeff_mem_range _ D.what₂.embLL hSum.read.1 v hv
  have h1 := GlobalTheory.T.coeff_coefficientSpaceAction_mem_range (tauE D) D.what₂.embLL (fun τ x => ⟨labLL D τ x, embLL_labLL τ x⟩) _
    (ch.S.N.fr (.grid 0 D.R.m))⁻¹ _ h0
  have gen : ∀ (k : ∀ i, VV ℂ (wt ch.G (.grid i D.R.m)) →ₗ[ℂ] VV ℂ (wt ch.G (.grid (i + 1) D.R.m))),
      (∀ i (w : VV ℂ (wt ch.G (.grid i D.R.m))), (∀ m, AddMonoidAlgebra.coeff w.1 m ∈ Set.range D.what₂.embLL) →
        ∀ m, AddMonoidAlgebra.coeff (k i w).1 m ∈ Set.range D.what₂.embLL) →
      ∀ j (w : VV ℂ (wt ch.G (.grid 0 D.R.m))), (∀ m, AddMonoidAlgebra.coeff w.1 m ∈ Set.range D.what₂.embLL) →
        ∀ m, AddMonoidAlgebra.coeff (chainTo (V := fun i => VV ℂ (wt ch.G (.grid i D.R.m))) k j w).1 m ∈ Set.range D.what₂.embLL := by
    intro k hk j
    induction j with
    | zero => intro w hw; exact hw
    | succ j ih => intro w hw; exact hk j _ (ih w hw)
  simp only [GlobalTheory.FunObj.GridChoice.rowMap, LinearMap.comp_apply]
  refine gen _ (fun i w hw m => ?_) D.R.m _ h1
  split_ifs with h
  · refine coeff_map_mem _ _ ?_ w hw m
    intro a b
    have := (hF.isRatAt hβ hτ hd c).2 ⟨i, h⟩ a b
    simpa [GlobalTheory.FunObj.Normal.IsRatAt, GlobalTheory.FunObj.Normal.IsRatIn, GlobalTheory.FunObj.Normal.kkIn, LinearMap.toMatrix_apply] using this
  · exact ⟨0, by simp⟩

end GlobalTheory.RowRat

end
