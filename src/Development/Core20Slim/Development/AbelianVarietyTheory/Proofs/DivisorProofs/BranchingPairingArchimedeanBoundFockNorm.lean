module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.BrPairFApply
public import Development.Core20Slim.Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueIsFunForm
public import Formalism.SharpRestriction.Divisibility.PrimeDegreeVariant
public import Development.Core20Slim.Formalism.PieriBlockIdeals.StatementLA
public import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.RamBasic
public import Development.Core20Slim.Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.BranchingPairingMapExtendScalarsEmbeddingStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.BilinearFockPairingSqLeHermitianNormsStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.BranchingMapHermitianNormLeProdBoundsStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianFockNormAdjugateSubstSymmLeStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousCoeffBlockAct
public import Formalism.LocalRingCardinality.DataCoeff
public import Formalism.LocalToGlobal.Columns.CoefModB
public import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
public import Formalism.LocalToGlobal.Divisibility.CoefMod
public import Init.Classical
public import Init.Core
public import Init.Data.Order.Lemmas
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.Ring.Unbundled.Basic
public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.Real.Star
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.RelClasses
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.BrPairBound

theorem pairK_one_re_nonneg {ι : Type} [Fintype ι] {m : ℕ} (w : ι → DomWeight m) (x : VV ℂ w) :
    0 ≤ (pairK w (fun _ => (1 : Matrix (Fin m) (Fin m) ℂ)) x x).re := by
  by_cases h : x = 0
  · simp [h]
  · exact (Complex.lt_def.1 (GlobalTheory.CoefModel.pairK_pos w (G := fun _ => (1 : Matrix (Fin m) (Fin m) ℂ))
      (fun _ => Matrix.PosDef.one) x h)).1.le

theorem inf_bound : ∀ {K ι : Type} [Field K] [CharZero K] [Fintype ι] (φ : K →+* ℂ) {n N : ℕ} (hN : N = n + 1) (Λ : ι → DomWeight N)
    (σ : ι → DomWeight n), (∀ τ, Formalism.L2.Col.Br.Interlace hN (Λ τ) (σ τ)) → (∀ τ, Formalism.L2.Col.Br.SameShift (Λ τ) (σ τ)) →
    ∀ (u : VV K Λ) (v : VV K fun τ => (σ τ).dual),
    0 ≤ (pairK Λ (fun _ => (1 : Matrix (Fin N) (Fin N) ℂ)) (GlobalTheory.CoefModel.mapVV φ Λ u) (GlobalTheory.CoefModel.mapVV φ Λ u)).re ∧
    0 ≤ (pairK (fun τ => (σ τ).dual) (fun _ => (1 : Matrix (Fin n) (Fin n) ℂ)) (GlobalTheory.CoefModel.mapVV φ _ v)
      (GlobalTheory.CoefModel.mapVV φ _ v)).re ∧
    ‖φ (GlobalTheory.BrPairF.brPairF σ hN Λ u v)‖ ^ 2 ≤ (∏ τ, Formalism.MainNotions.PrimeDegreeVariant.brBd hN.symm (Λ τ) (σ τ) ^ 2) *
      (pairK Λ (fun _ => (1 : Matrix (Fin N) (Fin N) ℂ)) (GlobalTheory.CoefModel.mapVV φ Λ u) (GlobalTheory.CoefModel.mapVV φ Λ u)).re *
      (pairK (fun τ => (σ τ).dual) (fun _ => (1 : Matrix (Fin n) (Fin n) ℂ)) (GlobalTheory.CoefModel.mapVV φ _ v)
        (GlobalTheory.CoefModel.mapVV φ _ v)).re := by
  intro K ι _ _ _ φ n N hN Λ σ hI hS u v
  refine ⟨pairK_one_re_nonneg _ _, pairK_one_re_nonneg _ _, ?_⟩
  rw [GlobalTheory.T.branchingPairing_map_extendScalars_embedding φ hN Λ σ u v, GlobalTheory.BrPairF.brPairF_apply]
  set u' := GlobalTheory.CoefModel.mapVV φ Λ u
  set v' := GlobalTheory.CoefModel.mapVV φ _ v
  have h1 := GlobalTheory.T.bilinearFockPairing_sq_le_hermitianNorms σ (Formalism.L2.Col.Br.brStd hN Λ σ u') ((GlobalTheory.FunObj.funEquiv σ).symm v')
  have h2 := GlobalTheory.T.branchingMap_hermitianNorm_le_prod_bounds hN Λ σ hI hS u'
  have h3 := GlobalTheory.T.hermitianFockNorm_adjugateSubst_symm_le σ v'
  have p2 := pairK_one_re_nonneg σ ((GlobalTheory.FunObj.funEquiv σ).symm v')
  have p3 := pairK_one_re_nonneg Λ u'
  calc _ ≤ _ := h1
    _ ≤ _ := mul_le_mul h2 h3 p2 (mul_nonneg (Finset.prod_nonneg fun _ _ => sq_nonneg _) p3)
    _ = _ := by ring

end GlobalTheory.BrPairBound

end
