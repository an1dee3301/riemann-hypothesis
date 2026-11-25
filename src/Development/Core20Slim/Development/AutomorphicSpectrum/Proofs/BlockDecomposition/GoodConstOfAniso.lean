module

public import Mathlib
public import Development.Core20Slim.Development.WeilBound.ThetaLifts.Reductions.SiegelCore
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
public import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsAuxiliaryPlaceNotMemFinset
public import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
public import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Core
public import Init.Data.Fin.Basic
public import Init.Data.List.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.WithAbs
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.Normed.Ring.WithAbs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Empty
public import Mathlib.Data.Finset.Fold
public import Mathlib.Data.Finset.Insert
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Lattice
public import Mathlib.Order.MinMax
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.CompanionTheory.RapidDecay

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) {r : ℕ}

structure Good (U : Subgroup (GAd σ J)) (A : ℕ) (φ : GAd σ J → ℂ) : Prop where
  left : ∀ γ ∈ ratPts σ J, ∀ g, φ (γ * g) = φ g
  level : ∀ k ∈ U, k ∈ finPts σ J → ∀ g, φ (g * k) = φ g
  cont : Continuous φ
  smooth : GlobalTheory.UAut.IsSm σ J φ
  growth : ∀ l : List (ℝ → GAd σ J), (∀ γ ∈ l, IsRealLine σ J γ) →
    ∃ C : ℝ, ∀ g, ‖l.foldr lineDer φ g‖ ≤ C * (height σ J g : ℝ) ^ A
  cusp : IsCuspidal σ J φ

def CloseInf (u : GAd σ J) (δ : ℝ) : Prop :=
  u ∈ infPts σ J ∧ ∀ (w : InfinitePlace F) (τ : EmbOver E w) (i j : Fin n),
    ‖(archMat σ J τ (projArch σ J w u) - 1) i j‖ ≤ δ

variable {σ J}

def pre (X : Matrix (Fin n) (Fin r) E) (s : Fin r) : Matrix (Fin n) (Fin (s.val + 1)) E :=
  X.submatrix id (Fin.castLE s.2)

def ratio (t : Fin r → ℝ) (s : Fin r) : ℝ :=
  if h : s.val + 1 < r then t s / t ⟨s.val + 1, h⟩ else t s

def rbar (t : Fin r → ℝ) : ℝ := Finset.univ.fold max 1 (ratio t)

theorem one_le_rbar (t : Fin r → ℝ) : 1 ≤ rbar t := Finset.le_fold_max _ |>.2 (Or.inl le_rfl)

theorem ratio_le_rbar (t : Fin r → ℝ) (s : Fin r) : ratio t s ≤ rbar t :=
  (Finset.le_fold_max _).2 (Or.inr ⟨s, Finset.mem_univ s, le_rfl⟩)

theorem rbar_eq (t : Fin r → ℝ) : rbar t = 1 ∨ ∃ s, rbar t = ratio t s := by
  have key : ∀ S : Finset (Fin r), S.fold max 1 (ratio t) = 1 ∨ ∃ s, S.fold max 1 (ratio t) = ratio t s := fun S => by
    induction S using Finset.induction_on with
    | empty => exact Or.inl (by simp)
    | insert a S ha ih =>
      rw [Finset.fold_insert ha]
      rcases max_choice (ratio t a) (S.fold max 1 (ratio t)) with e | e
      · exact Or.inr ⟨a, e⟩
      · rw [e]; exact ih
  exact key _

theorem ratio_pos {c : ℝ} {t : Fin r → ℝ} (ht : t ∈ cone r c) (s : Fin r) : 0 < ratio t s := by
  unfold ratio
  split_ifs with h
  · exact div_pos (ht.1 _) (ht.1 _)
  · exact ht.1 _

end GlobalTheory.CompanionTheory.RapidDecay

end
