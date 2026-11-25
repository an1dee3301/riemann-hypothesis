module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.BrPairFApply
public import Development.Core20Slim.Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueIsFunForm
public import Formalism.SharpRestriction.Divisibility.PrimeDegreeVariant
public import Development.Core20Slim.Formalism.PieriBlockIdeals.StatementLA
public import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.RamBasic
public import Development.Core20Slim.Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.LastMapNorm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousCoeffBlockAct
public import Formalism.LocalRingCardinality.DataCoeff
public import Formalism.LocalToGlobal.Columns.CoefModB
public import Formalism.LocalToGlobal.Divisibility.CoefMod
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
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
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Mathlib.Analysis.CStarAlgebra.Module.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open scoped ComplexOrder

namespace GlobalTheory.FockCauchySchwarz

variable {ι : Type} [Fintype ι] {m : ℕ} (w : ι → DomWeight m)

theorem pairK_one (x y : VV ℂ w) :
    pairK w (fun _ => (1 : Matrix (Fin m) (Fin m) ℂ)) x y = pairBK w (GlobalTheory.BranchNorm.cV w x) y := by
  have h := GlobalTheory.BranchNorm.pairK_eq w (1 : ι → GL (Fin m) ℂ) x y
  rw [map_one] at h
  exact h

theorem pairK_cs (x y : VV ℂ w) :
    ‖pairK w (fun _ => (1 : Matrix (Fin m) (Fin m) ℂ)) x y‖ ^ 2 ≤
      (pairK w (fun _ => (1 : Matrix (Fin m) (Fin m) ℂ)) x x).re *
        (pairK w (fun _ => (1 : Matrix (Fin m) (Fin m) ℂ)) y y).re := by
  have hG : ∀ _ : ι, (1 : Matrix (Fin m) (Fin m) ℂ).PosDef := fun _ => Matrix.PosDef.one
  rw [← GlobalTheory.CoefModel.inner_toHilb w hG, ← GlobalTheory.CoefModel.inner_toHilb w hG, ← GlobalTheory.CoefModel.inner_toHilb w hG]
  have h := inner_mul_inner_self_le (𝕜 := ℂ) (GlobalTheory.CoefModel.toHilb w hG x) (GlobalTheory.CoefModel.toHilb w hG y)
  rw [norm_inner_symm (GlobalTheory.CoefModel.toHilb w hG y), ← sq] at h
  exact h

theorem pairBK_sq_le : ∀ {ι : Type} [Fintype ι] {m : ℕ} (w : ι → DomWeight m) (x y : VV ℂ w),
    ‖pairBK w x y‖ ^ 2 ≤ (pairK w (fun _ => (1 : Matrix (Fin m) (Fin m) ℂ)) x x).re *
      (pairK w (fun _ => (1 : Matrix (Fin m) (Fin m) ℂ)) y y).re := by
  intro ι _ m w x y
  have h := pairK_cs w (GlobalTheory.BranchNorm.cV w x) y
  rw [pairK_one, pairK_one w (GlobalTheory.BranchNorm.cV w x), GlobalTheory.BranchNorm.cV_cV] at h
  rw [pairK_one w x x, pairBK_apply w (GlobalTheory.BranchNorm.cV w x), pairingBSymm_holds, ← pairBK_apply]
  exact h

end GlobalTheory.FockCauchySchwarz
