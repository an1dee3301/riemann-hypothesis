module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Core
public import Init.Data.Sum.Basic
public import Init.Data.Sum.Lemmas
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Block
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix

namespace GlobalTheory.AdelicSvN

variable {F : Type} [Field F]

def act {R : Type} [CommRing R] [Algebra F R] {κ : Type} [Fintype κ] (g : Matrix (κ ⊕ κ) (κ ⊕ κ) F)
    (w : (κ → R) × (κ → R)) : (κ → R) × (κ → R) :=
  ((g.map (algebraMap F R) *ᵥ Sum.elim w.1 w.2) ∘ Sum.inl, (g.map (algebraMap F R) *ᵥ Sum.elim w.1 w.2) ∘ Sum.inr)

theorem act_one {R : Type} [CommRing R] [Algebra F R] {κ : Type} [Fintype κ] [DecidableEq κ]
    (w : (κ → R) × (κ → R)) : act (1 : Matrix (κ ⊕ κ) (κ ⊕ κ) F) w = w := by
  have h : (1 : Matrix (κ ⊕ κ) (κ ⊕ κ) F).map (algebraMap F R) = 1 :=
    Matrix.map_one _ (map_zero _) (map_one _)
  simp only [act, h, Matrix.one_mulVec]
  rfl

theorem act_mul {R : Type} [CommRing R] [Algebra F R] {κ : Type} [Fintype κ]
    (g h : Matrix (κ ⊕ κ) (κ ⊕ κ) F) (w : (κ → R) × (κ → R)) : act (g * h) w = act g (act h w) := by
  have e : (g * h).map (algebraMap F R) = g.map (algebraMap F R) * h.map (algebraMap F R) :=
    Matrix.map_mul (f := algebraMap F R)
  simp only [act, e, ← Matrix.mulVec_mulVec, Sum.elim_comp_inl_inr]


variable (F) in
def gens (κ : Type) [Fintype κ] [DecidableEq κ] : Set (Matrix (κ ⊕ κ) (κ ⊕ κ) F) :=
  {g | ∃ A : Matrix κ κ F, IsUnit A.det ∧ g = Matrix.fromBlocks A 0 0 (A⁻¹)ᵀ} ∪
    {g | ∃ C : Matrix κ κ F, Cᵀ = C ∧ g = Matrix.fromBlocks 1 0 (-C) 1} ∪ {Matrix.fromBlocks 0 1 (-1) 0}

variable [NumberField F]

def Realised (ψ : AddChar (AF F) ℂ) {κ : Type} [Fintype κ] (g : Matrix (κ ⊕ κ) (κ ⊕ κ) F) : Prop :=
  ∃ S : ((κ → AF F) → ℂ) → (κ → AF F) → ℂ,
    (∀ φ ∈ schA F κ, S φ ∈ schA F κ) ∧ (∀ φ ∈ schA F κ, ∃ φ' ∈ schA F κ, S φ' = φ) ∧
    (∀ l ∈ (adeleClass F).adm κ, ∃ l' ∈ (adeleClass F).adm κ, ∀ φ ∈ schA F κ, l' φ = l (S φ)) ∧
    ∀ w, ∀ φ ∈ schA F κ, S (schr ψ w φ) = schr ψ (act g w) (S φ)

theorem realised_one (ψ : AddChar (AF F) ℂ) {κ : Type} [Fintype κ] [DecidableEq κ] :
    Realised ψ (1 : Matrix (κ ⊕ κ) (κ ⊕ κ) F) :=
  ⟨id, fun φ h => h, fun φ h => ⟨φ, h, rfl⟩, fun l hl => ⟨l, hl, fun _ _ => rfl⟩,
    fun w φ _ => by rw [act_one]; rfl⟩

theorem Realised.mul {ψ : AddChar (AF F) ℂ} {κ : Type} [Fintype κ] {g h : Matrix (κ ⊕ κ) (κ ⊕ κ) F}
    (hg : Realised ψ g) (hh : Realised ψ h) : Realised ψ (g * h) := by
  obtain ⟨S, hS, hSs, hSa, hSi⟩ := hg
  obtain ⟨T, hT, hTs, hTa, hTi⟩ := hh
  refine ⟨S ∘ T, fun φ hφ => hS _ (hT φ hφ), fun φ hφ => ?_, fun l hl => ?_, fun w φ hφ => ?_⟩
  · obtain ⟨φ₁, h₁, rfl⟩ := hSs φ hφ
    obtain ⟨φ₂, h₂, rfl⟩ := hTs φ₁ h₁
    exact ⟨φ₂, h₂, rfl⟩
  · obtain ⟨l₁, hl₁, e₁⟩ := hSa l hl
    obtain ⟨l₂, hl₂, e₂⟩ := hTa l₁ hl₁
    exact ⟨l₂, hl₂, fun φ hφ => (e₂ φ hφ).trans (e₁ _ (hT φ hφ))⟩
  · simp only [Function.comp_apply]
    rw [hTi w φ hφ, hSi _ _ (hT φ hφ), act_mul]

end GlobalTheory.AdelicSvN
