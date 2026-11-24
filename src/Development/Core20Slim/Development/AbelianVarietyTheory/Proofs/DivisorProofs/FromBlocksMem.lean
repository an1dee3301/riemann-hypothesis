module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
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
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.CStarMatrix
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Block
public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.InertDbl

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

abbrev UD (σ : E →ₐ[F] E) {d : ℕ} (W : Spc F E d) : Type := UG (cA σ) (dbl (incM F W.J))

def matD {σ : E →ₐ[F] E} {d : ℕ} {W : Spc F E d} (g : UD σ W) : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) :=
  g.1.1

def latAtD {d : ℕ} (W : Spc F E d) (v : Pl (F := F)) : Set (Fin d ⊕ Fin d → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) :=
  {z | (fun i => z (Sum.inl i)) ∈ GlobalTheory.InertSph.latAt W v ∧ (fun i => z (Sum.inr i)) ∈ GlobalTheory.InertSph.latAt W v}

def KAtD (σ : E →ₐ[F] E) {d : ℕ} (W : Spc F E d) (v : Pl (F := F)) : Set (UD σ W) :=
  {g | At (evFin F v) (matD g - 1) ∧
    ∀ z ∈ latAtD W v, matD g *ᵥ z ∈ latAtD W v ∧ matD g⁻¹ *ᵥ z ∈ latAtD W v}

def antiCols (d : ℕ) : Matrix (Fin d ⊕ Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) := Matrix.fromRows 1 (-1)

def ParD (σ : E →ₐ[F] E) {d : ℕ} (W : Spc F E d) (v : Pl (F := F)) : Set (UD σ W) :=
  {p | p ∈ KAtD σ W v ∧ ∃ t : GL (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), matD p * diagCols (Fin d) = diagCols (Fin d) * (t : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))}

def NabD (σ : E →ₐ[F] E) {d : ℕ} (W : Spc F E d) (v : Pl (F := F)) : Set (UD σ W) :=
  {n | n ∈ KAtD σ W v ∧ matD n * antiCols d = antiCols d ∧
    ∃ b : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), matD n * diagCols (Fin d) = diagCols (Fin d) + antiCols d * b}

theorem fromBlocks_mem {σ : E →ₐ[F] E} {d : ℕ} {W : Spc F E d} (k : UA σ W.J) :
    ((Matrix.fromBlocks (mat k) 0 0 1 : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))))ᵀ * dbl (incM F W.J) *
      (Matrix.fromBlocks (mat k) 0 0 1 : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))).map (cA σ) = dbl (incM F W.J) := by
  have hk : (mat k)ᵀ * incM F W.J * (mat k).map (cA σ) = incM F W.J := k.2
  rw [Matrix.fromBlocks_map, Matrix.fromBlocks_transpose, dbl, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp [hk, Matrix.map_one _ (map_zero (cA σ)) (map_one (cA σ))]

def inlD (σ : E →ₐ[F] E) {d : ℕ} (W : Spc F E d) : UA σ W.J →* UD σ W where
  toFun k := ⟨⟨Matrix.fromBlocks (mat k) 0 0 1, Matrix.fromBlocks (mat k⁻¹) 0 0 1,
      by rw [Matrix.fromBlocks_multiply]; simp [mat, ← Matrix.GeneralLinearGroup.coe_mul, Matrix.fromBlocks_one],
      by rw [Matrix.fromBlocks_multiply]; simp [mat, ← Matrix.GeneralLinearGroup.coe_mul, Matrix.fromBlocks_one]⟩,
    fromBlocks_mem k⟩
  map_one' := by
    apply Subtype.ext; apply Units.ext
    show Matrix.fromBlocks (mat (1 : UA σ W.J)) 0 0 1 = 1
    simp [mat, Matrix.fromBlocks_one]
  map_mul' a b := by
    apply Subtype.ext; apply Units.ext
    show Matrix.fromBlocks (mat (a * b)) 0 0 1 = Matrix.fromBlocks (mat a) 0 0 1 * Matrix.fromBlocks (mat b) 0 0 1
    rw [Matrix.fromBlocks_multiply]; simp [mat]

theorem matD_inlD (σ : E →ₐ[F] E) {d : ℕ} (W : Spc F E d) (k : UA σ W.J) :
    matD (inlD σ W k) = Matrix.fromBlocks (mat k) 0 0 1 := rfl

def dblFun {κ : Type} (Ψ : (κ → AF F) → ℂ) : (κ ⊕ κ → AF F) → ℂ := boxFun Ψ fun x => star (Ψ x)

end GlobalTheory.InertDbl

end
