module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiCols
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Core
public import Init.Data.Sum.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Block
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
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
namespace GlobalTheory.DblVacDiag

open Matrix

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem mat_mul_mat_inv {σ : E →ₐ[F] E} {d : ℕ} {J : Matrix (Fin d) (Fin d) E} (k : UA σ J) :
    mat k * mat k⁻¹ = 1 := by
  show ((k * k⁻¹ : UA σ J) : GL (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))).1 = 1
  rw [mul_inv_cancel]; rfl

theorem mat_inv_mul_mat {σ : E →ₐ[F] E} {d : ℕ} {J : Matrix (Fin d) (Fin d) E} (k : UA σ J) :
    mat k⁻¹ * mat k = 1 := by
  show ((k⁻¹ * k : UA σ J) : GL (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))).1 = 1
  rw [inv_mul_cancel]; rfl

def diagOne {R : Type} [CommRing R] {d : ℕ} (A B : Matrix (Fin d) (Fin d) R) (hAB : A * B = 1) (hBA : B * A = 1) :
    GL (Fin d ⊕ Fin d) R :=
  ⟨fromBlocks A 0 0 1, fromBlocks B 0 0 1, by simp [fromBlocks_multiply, hAB, ← fromBlocks_one],
    by simp [fromBlocks_multiply, hBA, ← fromBlocks_one]⟩

theorem diag_mem_KD (σ : E →ₐ[F] E) {d : ℕ} (W : Spc F E d) (v : Pl (F := F)) :
    ∀ k ∈ GlobalTheory.InertSph.KAt σ W v, ∃ g : GlobalTheory.DblVac.UD σ W,
      ((g : GL (Fin d ⊕ Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) =
        Matrix.fromBlocks (mat k) 0 0 1 ∧ g ∈ GlobalTheory.DblVac.KD σ W v := by
  intro k hk
  let M := diagOne (mat k) (mat k⁻¹) (mat_mul_mat_inv k) (mat_inv_mul_mat k)
  have hU : (M : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))ᵀ * dbl (incM F W.J) *
      (M : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))).map (cA σ) = dbl (incM F W.J) := by
    have hk2 : (mat k)ᵀ * incM F W.J * (mat k).map (cA σ) = incM F W.J := k.2
    show (fromBlocks (mat k) 0 0 1)ᵀ * fromBlocks (incM F W.J) 0 0 (-incM F W.J) *
      (fromBlocks (mat k) 0 0 (1 : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))).map (cA σ) = fromBlocks (incM F W.J) 0 0 (-incM F W.J)
    rw [fromBlocks_transpose, fromBlocks_map, fromBlocks_multiply, fromBlocks_multiply]
    simp [hk2, Matrix.map_one _ (map_zero (cA σ)) (map_one (cA σ))]
  refine ⟨⟨M, hU⟩, rfl, ?_, ?_⟩
  · intro u hu
    have h1 := hk.1 u hu
    show u • (fromBlocks (mat k) 0 0 1 - 1 : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) = 0
    have h1' : u • (mat k - 1) = 0 := h1
    rw [← fromBlocks_one, sub_eq_add_neg, fromBlocks_neg, fromBlocks_add, fromBlocks_smul, ← sub_eq_add_neg]
    simp [h1']
  · intro z hz
    have hinv : GlobalTheory.DblVac.matD (⟨M, hU⟩ : GlobalTheory.DblVac.UD σ W)⁻¹ = fromBlocks (mat k⁻¹) 0 0 1 := rfl
    have hfw : GlobalTheory.DblVac.matD (⟨M, hU⟩ : GlobalTheory.DblVac.UD σ W) = fromBlocks (mat k) 0 0 1 := rfl
    rw [hinv, hfw]
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · rw [fromBlocks_mulVec]; simpa using ((hk.2 _ hz.1).1)
    · rw [fromBlocks_mulVec]; simpa using hz.2
    · rw [fromBlocks_mulVec]; simpa using ((hk.2 _ hz.1).2)
    · rw [fromBlocks_mulVec]; simpa using hz.2

end GlobalTheory.DblVacDiag
