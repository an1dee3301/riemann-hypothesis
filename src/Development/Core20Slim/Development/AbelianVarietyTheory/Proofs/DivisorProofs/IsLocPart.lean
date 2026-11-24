module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Init.Classical
public import Init.Core
public import Init.Data.Fin.Basic
public import Init.Data.Nat.Lemmas
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.RingTheory.Valuation.Basic
public import Mathlib.RingTheory.Valuation.Integers
public import Mathlib.RingTheory.Valuation.ValuativeRel.Basic

@[expose] public section

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes ValuativeRel
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace GlobalTheory.StdPairCone

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def blk₁ {m a a' : ℕ} (X : Matrix (Fin m) (Fin (a + a')) k) : Matrix (Fin m) (Fin a) k :=
  Matrix.of fun i j => X i (Fin.castAdd a' j)

def blk₂ {m a a' : ℕ} (X : Matrix (Fin m) (Fin (a + a')) k) : Matrix (Fin m) (Fin a') k :=
  Matrix.of fun i j => X i (Fin.natAdd a j)

def IsGLO {n : ℕ} (g : Matrix (Fin n) (Fin n) k) : Prop := (∀ i j, g i j ∈ 𝒪[k]) ∧ valuation k g.det = 1


open Classical in
def stdA (ν : kˣ →* ℂˣ) (ϖ : kˣ) (c a a' : ℕ) (X : Matrix (Fin a) (Fin (a + a')) k) : ℂ :=
  if h : (blk₁ X).det ≠ 0 ∧ IsGLO (blk₁ X) ∧ ∀ i j, blk₂ X i j ∈ GlobalTheory.SplitWeil.cball (ϖ ^ c) then
    (((ν (Units.mk0 _ h.1))⁻¹ : ℂˣ) : ℂ) else 0


open Classical in
def stdB (ν : kˣ →* ℂˣ) (ϖ : kˣ) (c a a' : ℕ) (Y : Matrix (Fin a') (Fin (a + a')) k) : ℂ :=
  if h : (blk₂ Y).det ≠ 0 ∧ IsGLO (blk₂ Y) ∧ ∀ i j, blk₁ Y i j ∈ GlobalTheory.SplitWeil.cball (ϖ ^ c) then
    (((ν (Units.mk0 _ h.1))⁻¹ : ℂˣ) : ℂ) else 0


open Classical in
def unitInd (ν : kˣ →* ℂˣ) (y : k) : ℂ :=
  if h : y ≠ 0 ∧ valuation k y = 1 then (((ν (Units.mk0 y h.1))⁻¹ : ℂˣ) : ℂ) else 0


end Local

section Glob

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

end Glob

end GlobalTheory.StdPairCone
