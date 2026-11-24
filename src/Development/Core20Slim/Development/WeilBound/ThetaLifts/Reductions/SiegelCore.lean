module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
public import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
public import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
public import Formalism.SatakeDualWeyl.Statement
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Fin.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Topology.Defs.Filter

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal

namespace PositivityTheory.ThKR

open GlobalTheory.SiegelSet

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) {r : ℕ}

def minPar (X : Matrix (Fin n) (Fin r) E) : Set (GAd σ J) :=
  {p | ∃ B : Matrix (Fin r) (Fin r) (AF F ⊗[F] E), B.BlockTriangular id ∧
    (matHom _ σ J p).1 * adMat F X = adMat F X * B}

def leviMin (X Y : Matrix (Fin n) (Fin r) E) : Set (GAd σ J) :=
  {m | ∃ d d' : Fin r → AF F ⊗[F] E, (matHom _ σ J m).1 * adMat F X = adMat F X * diagonal d ∧
    (matHom _ σ J m).1 * adMat F Y = adMat F Y * diagonal d'}

def unipMin (X : Matrix (Fin n) (Fin r) E) : Set (GAd σ J) :=
  {u | ∃ B : Matrix (Fin r) (Fin r) (AF F ⊗[F] E), B.BlockTriangular id ∧ (∀ i, B i i = 1) ∧
    (matHom _ σ J u).1 * adMat F X = adMat F X * B ∧
    ∀ z : Fin n → E, (cT (σ : E →+* E) X * J) *ᵥ z = 0 →
      ∃ a : Fin r → AF F ⊗[F] E,
        ((matHom _ σ J u).1 - 1) *ᵥ (fun i => inclR (F := F) (AF F) (z i)) = adMat F X *ᵥ a}

def GoodPosition (X Y : Matrix (Fin n) (Fin r) E) (K : Subgroup (GAd σ J)) : Prop :=
  ∀ p ∈ minPar σ J X, p ∈ K →
    ∃ m ∈ leviMin σ J X Y, m ∈ K ∧ ∃ u ∈ unipMin σ J X, u ∈ K ∧ p = m * u

def SiegelCore : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
      ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y →
        ∃ (K : Subgroup (GAd σ J)) (Ω : Set (GAd σ J)) (c : ℝ),
          IsCompact (K : Set (GAd σ J)) ∧ IsCompact Ω ∧ Ω ⊆ minParOne σ J X ∧ 0 < c ∧
          (∀ g, ∃ p ∈ minPar σ J X, ∃ k ∈ K, g = p * k) ∧
          GoodPosition σ J X Y K ∧
          (∀ g, ∃ γ ∈ ratPts σ J, ∃ s ∈ siegelSet σ J X Y Ω c K, g = γ * s) ∧
          (∃ C : Set (GAd σ J), IsCompact C ∧ ∀ p ∈ Ω, ∀ t ∈ cone r c, ∀ a, IsTorusElt σ J X Y t a → a⁻¹ * p * a ∈ C) ∧
          (∃ (C : ℝ≥0) (A : ℕ), ∀ g ∈ siegelSet σ J X Y Ω c K, ∀ γ ∈ ratPts σ J,
            height σ J g ≤ C * height σ J (γ * g) ^ A) ∧
          ∀ φ : GAd σ J → ℂ, IsSmoothModerate σ J φ → IsCuspidal σ J φ →
            ∀ N : ℕ, ∃ C : ℝ, ∀ g ∈ siegelSet σ J X Y Ω c K, ‖φ g‖ * (height σ J g : ℝ) ^ N ≤ C

theorem one_mem_minPar (X : Matrix (Fin n) (Fin r) E) : (1 : GAd σ J) ∈ minPar σ J X :=
  ⟨1, Matrix.blockTriangular_one, by simp⟩

theorem one_mem_leviMin (X Y : Matrix (Fin n) (Fin r) E) : (1 : GAd σ J) ∈ leviMin σ J X Y :=
  ⟨1, 1, by simp, by simp⟩

end PositivityTheory.ThKR

end
