module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChLApply
public import Development.AbelianVarietyTheory.Definitions.Foundations.SecondCountableAndT2LocalField
public import Development.AbelianVarietyTheory.Definitions.Foundations.SimpleSum
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ContrFactor
public import Init.Classical
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Fin.Basic
public import Init.Data.Fin.Lemmas
public import Init.Data.Int.Basic
public import Init.Data.Int.Lemmas
public import Init.Data.Int.Order
public import Init.Data.Nat.Basic
public import Init.Data.Nat.Lemmas
public import Init.Data.NeZero
public import Init.Data.Sum.Basic
public import Init.Data.Zero
public import Init.Omega.Coeffs
public import Init.Omega.Constraint
public import Init.Omega.Int
public import Init.Omega.LinearCombo
public import Init.Omega.Logic
public import Init.Prelude
public import Init.PropLemmas
public import Init.SimpLemmas
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Order.SuccPred
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.UnitBall
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.IsEmpty.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Filter
public import Mathlib.Data.Finset.Lattice.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Sets
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.Logic.Equiv.Basic
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.MeasurableSpace.Embedding
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
public import Mathlib.MeasureTheory.OuterMeasure.AE
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Filter.Basic
public import Mathlib.Order.Lattice
public import Mathlib.Order.Nat
public import Mathlib.Order.SuccPred.Nat
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.Valuation.ValuativeRel.Basic
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Compactness.LocallyCompact
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Separation.Hausdorff

@[expose] public section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData

noncomputable section
namespace GlobalTheory.RedFlatRow
open GlobalTheory.PartRed GlobalTheory.LocFlat

variable {k : Type} [Field k] {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}

theorem mem_transSet_union_upSet (ρ : ℕ) (e : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1))) :
    e ∈ (transSet ρ ∪ upSet ρ : Finset ((n ⊕ Fin c) × (n' ⊕ Fin (c + 1)))) ↔ Free (ρ + 1) e := by
  rcases e with ⟨r | l, s | i⟩ <;> simp only [transSet, upSet, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] <;> simp [Free] <;> omega

def freeEquiv (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c ρ : ℕ) :
    {e // e ∈ (transSet ρ ∪ upSet ρ : Finset ((n ⊕ Fin c) × (n' ⊕ Fin (c + 1))))} ≃
      {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free (ρ + 1) rs} :=
  Equiv.subtypeEquivRight (mem_transSet_union_upSet ρ)

theorem fill_eq (ρ : ℕ) (lρ : Fin c) (hl : lρ.val = ρ) (x : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)
    (y : {e // e ∈ (transSet ρ ∪ upSet ρ : Finset ((n ⊕ Fin c) × (n' ⊕ Fin (c + 1))))} → k) :
    fillAt (basePt c (0 : Matrix n n' k)) (fixSet ρ ∪ lowSet ρ) (transSet ρ ∪ upSet ρ) x y =
      affPt (ρ + 1) (fun r s => x (Sum.inl r) (Sum.inl s)) (fun rs => y ((freeEquiv n n' c ρ).symm rs)) +
        rowAt n c (ρ + 1) (fun s => x (Sum.inr lρ) (Sum.inl s)) := by
  ext r q
  simp only [fillAt, affPt, Matrix.add_apply, Matrix.of_apply]
  by_cases hI : (r, q) ∈ (transSet ρ ∪ upSet ρ : Finset ((n ⊕ Fin c) × (n' ⊕ Fin (c + 1))))
  · have hF : Free (ρ + 1) (r, q) := (mem_transSet_union_upSet ρ _).1 hI
    rw [dite_eq_left hI, dite_eq_left hF]
    have h1 : (freeEquiv n n' c ρ).symm ⟨(r, q), hF⟩ = ⟨(r, q), hI⟩ := rfl
    rw [h1]
    rcases r with r | l <;> rcases q with s | i <;> simp [basePt, rowAt, Free, Matrix.fromBlocks] at hF ⊢ <;> (try split_ifs) <;> first | rfl | (exfalso; omega) | (have hl' : l = lρ := Fin.ext (by omega); subst hl'; simp) | simp | omega | trace_state
  · have hF : ¬ Free (ρ + 1) (r, q) := fun hF => hI ((mem_transSet_union_upSet ρ _).2 hF)
    rw [dite_eq_right hI, dite_eq_right hF]
    by_cases hE : (r, q) ∈ (fixSet ρ ∪ lowSet ρ : Finset ((n ⊕ Fin c) × (n' ⊕ Fin (c + 1))))
    · rw [if_pos hE]
      simp only [fixSet, lowSet, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at hE
      rcases r with r | l <;> rcases q with s | i <;> simp [basePt, rowAt, Free, Matrix.fromBlocks] at hF hE ⊢ <;> (try split_ifs) <;> first | rfl | (exfalso; omega) | (have hl' : l = lρ := Fin.ext (by omega); subst hl'; simp) | simp | omega | trace_state
    · rw [if_neg hE]
      simp only [fixSet, lowSet, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at hE
      rcases r with r | l <;> rcases q with s | i <;> simp [basePt, rowAt, Free, Matrix.fromBlocks] at hF hE ⊢ <;> (try split_ifs) <;> first | rfl | (exfalso; omega) | (have hl' : l = lρ := Fin.ext (by omega); subst hl'; simp) | simp | omega | trace_state

theorem ch_add_rowAt (p : ℕ) (A : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) (u : n' → k) :
    ch (A + rowAt n c p u) = ch A := by
  simp [ch, rowAt, Matrix.fromBlocks]

theorem piCongrLeft_freeEquiv [MeasurableSpace k] (ρ : ℕ)
    (y : {e // e ∈ (transSet ρ ∪ upSet ρ : Finset ((n ⊕ Fin c) × (n' ⊕ Fin (c + 1))))} → k) :
    MeasurableEquiv.piCongrLeft (fun _ => k) (freeEquiv n n' c ρ) y =
      fun rs => y ((freeEquiv n n' c ρ).symm rs) := by
  funext rs
  simp [MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft_apply]

end GlobalTheory.RedFlatRow


open GlobalTheory.RedFlatRow in
theorem GlobalTheory.RedFlatRow.red_eq_flRow : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k), ν.IsAddHaarMeasure → ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c ρ : ℕ), c = 2 * ρ + 1 → ∀ (lρ : Fin c), lρ.val = ρ → ∀ (Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ) (x : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k), GlobalTheory.PartRed.red ψ ν GlobalTheory.PartRed.chL (basePt c (0 : Matrix n n' k)) (GlobalTheory.PartRed.fixSet ρ ∪ GlobalTheory.PartRed.lowSet ρ) (GlobalTheory.PartRed.transSet ρ ∪ GlobalTheory.PartRed.upSet ρ) Φ x = GlobalTheory.LocFlat.flRow ψ ν (ρ + 1) Φ (Matrix.of fun r s => Sum.elim (fun r => x (Sum.inl r) (Sum.inl s)) (fun _ => x (Sum.inr lρ) (Sum.inl s)) r) := by
  intro k _ _ _ _ _ _ ψ ν hν n n' _ _ _ _ c ρ _ lρ hl Φ x
  classical
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  haveI : SigmaFinite ν := sigmaFinite_of_locallyFinite
  have hmp := MeasureTheory.measurePreserving_piCongrLeft (α := fun _ => k)
    (fun _ : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free (ρ + 1) rs} => ν) (freeEquiv n n' c ρ)
  simp only [GlobalTheory.PartRed.red, GlobalTheory.LocFlat.flRow, opE]
  refine Eq.trans ?_ (hmp.integral_comp' _)
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only [piCongrLeft_freeEquiv, fill_eq ρ lρ hl x y, GlobalTheory.PartRed.chL_apply, ch_add_rowAt]
  rfl
