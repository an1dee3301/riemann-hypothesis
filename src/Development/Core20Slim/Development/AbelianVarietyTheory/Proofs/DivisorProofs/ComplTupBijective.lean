module

public import Mathlib
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinPt
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Init.Classical
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Function
public import Init.Data.Int.Basic
public import Init.Data.Int.DivMod.Lemmas
public import Init.Data.Int.Lemmas
public import Init.Data.Int.Order
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Omega.Coeffs
public import Init.Omega.Constraint
public import Init.Omega.Int
public import Init.Omega.LinearCombo
public import Init.Prelude
public import Init.PropLemmas
public import Init.SimpLemmas
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.IsEmpty.Defs
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.BooleanAlgebra
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Basic
public import Mathlib.Data.Int.Cast.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Int.Cast.Lemmas
public import Mathlib.Data.Int.Order.Units
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Image
public import Mathlib.Data.Set.Operations
public import Mathlib.Logic.Function.Basic
public import Mathlib.Logic.Function.Defs
public import Mathlib.Order.BooleanAlgebra.Basic
public import Mathlib.Order.BooleanAlgebra.Defs
public import Mathlib.Order.BooleanAlgebra.Set
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Fin.Basic
public import Mathlib.Order.Hom.Basic
public import Mathlib.Order.Lattice
public import Mathlib.Order.Monotone.Basic
public import Mathlib.Order.Monotone.Defs
public import Mathlib.Order.Notation
public import Mathlib.Order.RelClasses
public import Mathlib.Order.WellFounded

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.BotMatch

def complSub {a a' d : ℕ} (h : a + a' = d) (s : {s : Fin a → Fin d // StrictMono s}) : {s : Fin a' → Fin d // StrictMono s} :=
  ⟨Finset.orderEmbOfFin (Finset.univ.image s.1)ᶜ (by
      rw [Finset.card_compl, Finset.card_image_of_injective _ s.2.injective, Finset.card_univ, Fintype.card_fin,
        Fintype.card_fin]; omega), (Finset.orderEmbOfFin _ _).strictMono⟩

theorem range_complSub {a a' d : ℕ} (h : a + a' = d) (s : {s : Fin a → Fin d // StrictMono s}) :
    Set.range (complSub h s).1 = (Set.range s.1)ᶜ := by
  simp only [complSub, Finset.range_orderEmbOfFin, Finset.coe_compl, Finset.coe_image, Finset.coe_univ, Set.image_univ]

theorem complSub_complSub {a a' d : ℕ} (h : a + a' = d) (h' : a' + a = d) (s : {s : Fin a → Fin d // StrictMono s}) :
    complSub h' (complSub h s) = s := by
  apply Subtype.ext
  apply (StrictMono.range_inj (complSub h' (complSub h s)).2 s.2).1
  rw [range_complSub, range_complSub, compl_compl]

def complTup (D : D7) {a a' d : ℕ} {n : D.what₂.Tau → ℕ} (h : a + a' = d) (T : Tup D a d n) : Tup D a' d n :=
  fun τ k => complSub h (T τ k)

theorem complTup_bijective (D : D7) {a a' d : ℕ} {n : D.what₂.Tau → ℕ} (h : a + a' = d) :
    Function.Bijective (complTup D (n := n) h) := by
  refine Function.bijective_iff_has_inverse.2 ⟨complTup D (a := a') (a' := a) (by omega), fun T => ?_, fun T => ?_⟩ <;>
    funext τ k <;> simp only [complTup, complSub_complSub]

theorem exists_signed_perm {α β : Type} [Fintype α] [Fintype β] (c : α → β) (hc : Function.Bijective c) (ε : α → ℤˣ) :
    ∃ (M : α → β → ℤ) (M' : β → α → ℤ), (∀ T₁ T₂, ∑ T, M' T₁ T * M T T₂ = if T₁ = T₂ then 1 else 0) ∧
      ∀ T (f : β → ℂ), ∑ T', (M T T' : ℂ) * f T' = ((ε T : ℤ) : ℂ) * f (c T) := by
  classical
  refine ⟨fun T T' => if T' = c T then (ε T : ℤ) else 0, fun T' T => if T' = c T then (ε T : ℤ) else 0, fun T₁ T₂ => ?_,
    fun T f => ?_⟩
  · obtain ⟨T, rfl⟩ := hc.2 T₁
    rw [Finset.sum_eq_single T]
    · by_cases h : c T = T₂
      · subst h; simp [← Units.val_mul]
      · simp [h, Ne.symm h]
    · intro b _ hb
      have : c T ≠ c b := fun e => hb (hc.1 e).symm
      simp [this]
    · simp
  · rw [Finset.sum_eq_single (c T)]
    · simp
    · intro b _ hb; simp [hb]
    · simp

end GlobalTheory.BotMatch

end
