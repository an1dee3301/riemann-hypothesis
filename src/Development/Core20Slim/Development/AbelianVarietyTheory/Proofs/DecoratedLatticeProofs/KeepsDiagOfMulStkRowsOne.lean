module

public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.LatticeFrames.HeckeFormNSOfHeckeForm
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingSiegelEqLeviMulUnipotent
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingSiegelLeviDetHomLeviMulUnipotent
public import Development.AbelianVarietyTheory.Definitions.Foundations.MemSiegelOfIffRightAct
public import Init.ByCases
public import Init.Core
public import Init.Data.Sum.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Analysis.CStarAlgebra.CStarMatrix
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Logic.Equiv.Fin.Basic

@[expose] public section

open scoped ComplexConjugate Matrix NNReal ENNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP GlobalTheory.Core.Rk.SWLaw
open GlobalTheory.Core.Rk.SW

open GlobalTheory.MixModel Matrix

noncomputable section

namespace GlobalTheory.Core.Rk.SW

theorem keepsDiag_of_mul_stkRows_one {R : Type} [CommRing R] {n : ℕ} {M : Matrix (Fin (n + n)) (Fin (n + n)) R}
    {β : Matrix (Fin n) (Fin n) R} (h : M * stkRows 1 1 = stkRows β β) : KeepsDiag finSumFinEquiv M := by
  rw [keepsDiag_iff]
  have key : ∀ s : Fin n ⊕ Fin n, ∀ j, M (finSumFinEquiv s) (finSumFinEquiv (Sum.inl j)) +
      M (finSumFinEquiv s) (finSumFinEquiv (Sum.inr j)) = β (s.elim id id) j := by
    intro s j
    have h1 : ∑ k, M (finSumFinEquiv s) k * stkRows (1 : Matrix (Fin n) (Fin n) R) 1 k j =
        stkRows β β (finSumFinEquiv s) j := congrFun (congrFun h _) j
    rw [← finSumFinEquiv.sum_comp, Fintype.sum_sum_type] at h1
    simp only [stkRows, Matrix.submatrix_apply, id, Equiv.symm_apply_apply, Matrix.fromRows_apply_inl,
      Matrix.fromRows_apply_inr, Matrix.one_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true] at h1
    rw [h1]
    rcases s with s | s <;> rfl
  intro i j
  rw [key (Sum.inr i), key (Sum.inl i)]
  rfl

variable {D : D7}

section Core

variable {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ)

end Core

end GlobalTheory.Core.Rk.SW
