module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedSmooth
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedType
public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Formalism.RealPlaceAnalysis.Complexify
public import Formalism.SatakeDualWeyl.Statement
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Classical
public import Init.Core
public import Init.Data.Bool
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Rat.Basic
public import Init.Data.Sum.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Operator.LinearIsometry
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Embedding
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Matrix.Block
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.Multilinear.Basic
public import Mathlib.LinearAlgebra.PiTensorProduct.Basic
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Logic.Function.Basic
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Links Formalism.IndefR.Mult Matrix

namespace GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def SignCompat {p q n : ℕ} (ε : Fin n → Bool) (e : Ix p q ≃ Fin n) : Prop := ∀ a, ε (e a) = a.isLeft

def plainMat {p q n : ℕ} (e : Ix p q ≃ Fin n) (g : Mat p q) : Matrix (Fin n) (Fin n) ℂ := Matrix.reindex e e g

def barMat {p q n : ℕ} (e : Ix p q ≃ Fin n) (g : Mat p q) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.reindex e e (g.map (starRingEnd ℂ))

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}

def toFrame (M : DSModel V S) (τ : D.what₂.Tau) (Y : Matrix (Fin V.rank) (Fin V.rank) ℂ) :
    Matrix (Fin V.rank) (Fin V.rank) ℂ := (M.fr τ)⁻¹ * Y * M.fr τ


open Classical in
structure Matches {p q : ℕ} {T : GrpData p q} (R : DSRep T) (M : DSModel V S) (τ : D.what₂.Tau)
    (φ : Mat p q → Matrix (Fin V.rank) (Fin V.rank) ℂ) (m : ℤ) (U : M.H τ → R.U.H) : Prop where

  grp : ∀ (g : T.G) (x : M.H τ),
    R.U.π g (U x) = ((T.sq g : ℂˣ) : ℂ) ^ (-m) • U (M.σ τ (φ ((T.cov g : GL (Ix p q) ℂ) : Mat p q)) x)

  kfin : ∀ x : M.H τ, Formalism.MainNotions.S.IsKFin (M.ε τ) (M.σ τ) x ↔ U x ∈ Set.range R.ι

  smooth : ∀ x : M.H τ, U x ∈ Set.range R.ι → SmoothVec (lieAt V τ) (M.rep τ) x

  lie : (fun Z => toFrame M τ (φ Z)) '' upq p q = lieAt V τ

  der : ∀ Z ∈ upq p q, ∀ (v : R.HK.V) (x : M.H τ), U x = R.ι v →
    U (dRep (M.rep τ) (toFrame M τ (φ Z)) x) = R.ι (R.HK.act Z v + ((m : ℂ) / 2 * Z.trace) • v)

  derT : ∀ Z ∈ upq p q, ∀ (v : R.HK.V) (x : M.Vec) (y : M.sm τ), U (x τ : M.H τ) = R.ι v →
    U (y : M.H τ) = R.ι (R.HK.act Z v + ((m : ℂ) / 2 * Z.trace) • v) →
    DerT M τ (toFrame M τ (φ Z)) (PiTensorProduct.tprod ℂ x) (PiTensorProduct.tprod ℂ (Function.update x τ y))

def HidaSetting (X : ProvA) (p q : ℕ) (l₁ l₂ : List ℚ) (c : ℚ) (S : D.what₂.Tau → SPar) (τ : D.what₂.Tau) : Prop :=
  1 ≤ p + q ∧ l₁.length = p ∧ l₂.length = q ∧ IsParam (ofBlocks l₁ l₂ : Ix p q → ℚ) ∧
    HasParam (X.ds p q (ofBlocks l₁ l₂)) (ofBlocks l₁ l₂) ∧ S τ = dualPar (GlobalTheory.Chain.signed l₁ l₂ c)

def SourceBridge (D : D7) : Prop :=
  ∀ (X : ProvA) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (τ : D.what₂.Tau)
    (p q : ℕ) (l₁ l₂ : List ℚ) (c : ℚ), HidaSetting X p q l₁ l₂ c S τ →
    (∃ e : Ix p q ≃ Fin V.rank, SignCompat (M.ε τ) e) ∧
    ∃ m : ℤ, (m : ℚ) = 2 * c ∧ ∀ e : Ix p q ≃ Fin V.rank, SignCompat (M.ε τ) e →
      ∃ U : M.H τ ≃ₗᵢ[ℂ] (X.ds p q (ofBlocks l₁ l₂)).U.H,
        Matches (X.ds p q (ofBlocks l₁ l₂)) M τ (barMat e) m U

def TargetBridge (D : D7) : Prop :=
  ∀ (X : ProvA) (W : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel W S) (τ : D.what₂.Tau)
    (r s : ℕ) (l₁ l₂ : List ℚ) (c : ℚ), HidaSetting X r s l₁ l₂ c S τ →
    (∃ e : Ix r s ≃ Fin W.rank, SignCompat (M.ε τ) e) ∧
    ∃ m : ℤ, (m : ℚ) = 2 * c ∧ ∀ e : Ix r s ≃ Fin W.rank, SignCompat (M.ε τ) e →
      ∃ U : M.H τ ≃ₗᵢ⋆[ℂ] (X.ds r s (ofBlocks l₁ l₂)).U.H,
        Matches (X.ds r s (ofBlocks l₁ l₂)) M τ (plainMat e) m U

def ModelsAreCoverSeries (D : D7) : Prop := SourceBridge D ∧ TargetBridge D

theorem reindex_form {p q n : ℕ} {ε : Fin n → Bool} {e : Ix p q ≃ Fin n} (h : SignCompat ε e) :
    Matrix.reindex e e (Formalism.UG.Jpq p q) = Formalism.REAL.Jm ε := by
  ext a b
  obtain ⟨a, rfl⟩ := e.surjective a
  obtain ⟨b, rfl⟩ := e.surjective b
  have ha := h a
  rcases a with a | a <;> rcases b with b | b <;>
    simp_all [Formalism.UG.Jpq, Formalism.REAL.Jm, Matrix.diagonal_apply, Matrix.one_apply] <;> split_ifs <;> simp_all

theorem plainMat_mem {p q n : ℕ} {ε : Fin n → Bool} {e : Ix p q ≃ Fin n} (h : SignCompat ε e) {g : Mat p q}
    (hg : gᴴ * Formalism.UG.Jpq p q * g = Formalism.UG.Jpq p q) : plainMat e g ∈ Formalism.MainNotions.S.UJset ε := by
  change (plainMat e g)ᴴ * Formalism.REAL.Jm ε * plainMat e g = Formalism.REAL.Jm ε
  rw [← reindex_form h]
  simp only [plainMat, Matrix.reindex_apply, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, hg]

theorem barMat_mem {p q n : ℕ} {ε : Fin n → Bool} {e : Ix p q ≃ Fin n} (h : SignCompat ε e) {g : Mat p q}
    (hg : gᴴ * Formalism.UG.Jpq p q * g = Formalism.UG.Jpq p q) : barMat e g ∈ Formalism.MainNotions.S.UJset ε := by
  refine plainMat_mem h ?_
  have hJ : (Formalism.UG.Jpq p q).map (starRingEnd ℂ) = Formalism.UG.Jpq p q := by
    ext a b
    rcases a with a | a <;> rcases b with b | b <;> simp [Formalism.UG.Jpq, Matrix.one_apply] <;> split_ifs <;> simp
  have h1 := congrArg (fun A : Mat p q => A.map (starRingEnd ℂ)) hg
  simp only [Matrix.map_mul, hJ] at h1
  exact h1

end GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix

end
