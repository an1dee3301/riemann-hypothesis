module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.SiegelEisenstein.DoubledUnramifiedFrames
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CombAtSingleZero
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLocalGroupElementsJacobiBessel
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Fin.Basic
public import Init.Data.Fin.Lemmas
public import Init.Data.Int.Basic
public import Init.Data.Int.Lemmas
public import Init.Data.Int.Order
public import Init.Data.Nat.Basic
public import Init.Omega.Coeffs
public import Init.Omega.Constraint
public import Init.Omega.Int
public import Init.Omega.LinearCombo
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Data.Fin.SuccPred
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Filter
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Sets
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Logic.Equiv.Sum

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel IsLocalRing
open GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.StepData (XIx Ix latOf box LatFrame)
open GlobalTheory.LocMod (GAt PinGBy ofSplit MovedTo)
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (CharUnramAt)
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastPair lastKer)
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedLocalFrameSequences (IsFockOver StepsAll vec atW IsMoved InAt InvOnUnits IsBesFrame IsJacFrame FrameMapsPrefix jacLat ptBF ptFB)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FockOrder

variable {D : D7}

theorem exists_sortPerm {n : ℕ} (ε : Fin n → Bool) :
    ∃ π : Equiv.Perm (Fin n), ∀ a, ε (π a) = decide (a.val < (Finset.univ.filter fun a => ε a = true).card) := by
  classical
  set p := (Finset.univ.filter fun a => ε a = true).card with hp
  set q := (Finset.univ.filter fun a => ¬ ε a = true).card with hq
  have hpq : p + q = n := by
    rw [hp, hq, Finset.card_filter_add_card_filter_not]; simp
  have e1 : {a // ε a = true} ≃ Fin p := Fintype.equivFinOfCardEq (by rw [Fintype.card_subtype])
  have e2 : {a // ¬ ε a = true} ≃ Fin q := Fintype.equivFinOfCardEq (by rw [Fintype.card_subtype])
  refine ⟨(finCongr hpq.symm).trans (finSumFinEquiv.symm.trans ((Equiv.sumCongr e1.symm e2.symm).trans
    (Equiv.sumCompl _))), fun a => ?_⟩
  by_cases ha : a.val < p
  · have h : finCongr hpq.symm a = Fin.castAdd q ⟨a.val, ha⟩ := Fin.ext rfl
    simp only [Equiv.trans_apply, h, finSumFinEquiv_symm_apply_castAdd, Equiv.sumCongr_apply, Sum.map_inl,
      Equiv.sumCompl_apply_inl]
    rw [(e1.symm _).2]; simp [ha]
  · have h : finCongr hpq.symm a = Fin.natAdd p ⟨a.val - p, by omega⟩ := Fin.ext (by simp; omega)
    simp only [Equiv.trans_apply, h, finSumFinEquiv_symm_apply_natAdd, Equiv.sumCongr_apply, Sum.map_inr,
      Equiv.sumCompl_apply_inr]
    have h2 := (e2.symm ⟨a.val - p, by omega⟩).2
    simp only [Bool.not_eq_true] at h2
    rw [h2]; simp [ha]

variable {V : HSp D} {S : D.what₂.Tau → SPar}

section Main

variable {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {V W : HSp D} {S S' : D.what₂.Tau → SPar}

end Main

end GlobalTheory.FockOrder

end
