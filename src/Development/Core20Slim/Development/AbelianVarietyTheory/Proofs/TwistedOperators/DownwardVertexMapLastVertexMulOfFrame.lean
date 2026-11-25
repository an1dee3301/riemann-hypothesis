module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ValuationGdetKapAt
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteUnfSupportOfNeOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Definitions.Foundations.SimpleSum
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Fin.Basic
public import Init.Data.Fin.Lemmas
public import Init.Data.Int.Basic
public import Init.Data.Int.Lemmas
public import Init.Data.Int.Order
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Omega.Coeffs
public import Init.Omega.Constraint
public import Init.Omega.Int
public import Init.Omega.LinearCombo
public import Init.Prelude
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Data.Fin.SuccPred
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.RingTheory.Valuation.ValuativeRel.Basic
public import Mathlib.Topology.Defs.Basic

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv
open GlobalTheory.FunObj.FiniteSupport

noncomputable section

namespace GlobalTheory.TopLevelInv

theorem frame_symm_of_zero {a c b : ℕ} (h : a + c = b) (hc : c = 0) (p : Fin b) :
    (frame h).symm p = Sum.inl ⟨p.val, by omega⟩ := by
  subst hc
  rw [Equiv.symm_apply_eq]
  ext
  simp only [frame, Equiv.trans_apply, finCongr_apply, Fin.val_cast]
  rfl

theorem downMap_last_mul_of_toFrame_eq : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] {Γ : Grid k} (hs : 1 ≤ Γ.s) (j : ℕ) (hj : j + 1 < Γ.m) (hB : j + 2 = Γ.m)
    (g : GL (Fin (Γ.rank (Γ.m, j + 1))) k) (κ : GL (Fin (topRank Γ (j + 1))) k),
    toFrame hs hj g = embX (Γ.m - 1 - (j + 1)) κ → ∀ (x x' : ColArgs Γ) (e e' : Vars Γ), x' (j + 1) = x (j + 1) * κ.val →
    downMap hs x' e' (j + 1) = downMap hs x e (j + 1) * g.val := by
  intro k _ _ _ _ _ _ Γ hs j hj hB g κ hg x x' e e' hx
  have hr : Γ.rank (Γ.m, j + 1) = topRank Γ (j + 1) := by have := topRank_add hs (j + 1); omega
  have hval : ∀ p q, g.val p q = κ.val (Fin.cast hr p) (Fin.cast hr q) := by
    intro p q
    have h1 : g = (toFrame hs hj).symm (embX _ κ) := by rw [← hg, MulEquiv.symm_apply_apply]
    rw [h1]
    unfold toFrame
    rw [frameGL_symm_val, submatrix_apply, frame_symm_of_zero _ (by omega), frame_symm_of_zero _ (by omega)]
    rfl
  unfold downMap
  rw [dite_eq_right (by omega), dite_eq_left (by omega), dite_eq_right (by omega), dite_eq_left (by omega), hx]
  ext r q
  simp only [submatrix_apply, Matrix.mul_apply, hval]
  exact (Fintype.sum_equiv (finCongr hr) _ _ (fun p => rfl)).symm

end GlobalTheory.TopLevelInv

end
