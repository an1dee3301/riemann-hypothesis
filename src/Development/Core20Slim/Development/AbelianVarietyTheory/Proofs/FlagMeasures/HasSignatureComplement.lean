module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsLatMeasurableConst
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsFrameOfHasSignature
public import Formalism.RealPlaceAnalysis.Complexify
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.SignatureConjugationInvariant
public import Formalism.SatakeDualWeyl.Statement
public import Init.Core
public import Init.Data.Bool
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Int.Lemmas
public import Init.Data.Int.Order
public import Init.Data.List.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Nat.Lemmas
public import Init.Data.NeZero
public import Init.Data.Sum.Basic
public import Init.Data.Zero
public import Init.Omega.Coeffs
public import Init.Omega.Constraint
public import Init.Omega.Int
public import Init.Omega.LinearCombo
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Filter
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Block
public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.InvariantBasisNumber
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.RingTheory.FiniteType
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Result

@[expose] public section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.AutInhab

namespace GlobalTheory.AdaptedExists


section

variable {E : Type} [Field E] [StarRing E] {n : ℕ}




theorem gram_swap {k l : Type} [Fintype k] [Fintype l] {J : Matrix (Fin n) (Fin n) E} (hJ : Jᴴ = J)
    (A : Matrix (Fin n) k E) (B : Matrix (Fin n) l E) : Bᴴ * J * A = (Aᴴ * J * B)ᴴ := by
  simp [hJ, Matrix.mul_assoc]


end



theorem hasSignature_complement : ∀ (n m p q : ℕ) (κ : Type) [Fintype κ] [DecidableEq κ] (J : Matrix (Fin n) (Fin n) ℂ) (T T' : Matrix (Fin n) κ ℂ) (B : Matrix (Fin n) (Fin m) ℂ), Jᴴ = J → Formalism.UG.HasSignature J p q → n = m + 2 * Fintype.card κ → Tᴴ * J * T = 0 → T'ᴴ * J * T' = 0 → Tᴴ * J * T' = 1 → Tᴴ * J * B = 0 → T'ᴴ * J * B = 0 → (Bᴴ * J * B).det ≠ 0 → Formalism.UG.HasSignature (Bᴴ * J * B) (p - Fintype.card κ) (q - Fintype.card κ) := by
  intro n m p q κ _ _ J T T' B hJ hs hn h1 h2 h3 h4 h5 h6
  have hG : (Bᴴ * J * B)ᴴ = Bᴴ * J * B := (gram_swap hJ B B).symm
  obtain ⟨ε, P, hP, hPG⟩ := exists_frame (G := Bᴴ * J * B)
    (by unfold Formalism.UG.IsHerm; rw [Formalism.UG.P.cT_conj_eq, hG]) (IsUnit.mk0 _ h6)
  have h3' : T'ᴴ * J * T = 1 := by rw [gram_swap hJ, h3, conjTranspose_one]
  have h4' : Bᴴ * J * T = 0 := by rw [gram_swap hJ, h4, conjTranspose_zero]
  have h5' : Bᴴ * J * T' = 0 := by rw [gram_swap hJ, h5, conjTranspose_zero]
  obtain ⟨f⟩ : Nonempty (Fin n ≃ (κ ⊕ κ) ⊕ Fin m) := Fintype.card_eq.1 (by simp; omega)
  set Q : Matrix (Fin n) ((κ ⊕ κ) ⊕ Fin m) ℂ :=
    fromCols (fromCols (T + (1 / 2 : ℂ) • T') (T - (1 / 2 : ℂ) • T')) (B * P) with hQ
  set δ : (κ ⊕ κ) ⊕ Fin m → Bool := Sum.elim (Sum.elim (fun _ => true) fun _ => false) ε with hδ
  have hQJ : Qᴴ * J * Q = fromBlocks (fromBlocks 1 0 0 (-1)) 0 0 (Formalism.REAL.Jm ε) := by
    rw [Matrix.mul_assoc] at h1 h2 h3 h4 h5 h3' h4' h5'
    have a1 : Tᴴ * (J * (B * P)) = 0 := by rw [← Matrix.mul_assoc J, ← Matrix.mul_assoc, h4, Matrix.zero_mul]
    have a2 : T'ᴴ * (J * (B * P)) = 0 := by rw [← Matrix.mul_assoc J, ← Matrix.mul_assoc, h5, Matrix.zero_mul]
    have a3 : Pᴴ * (Bᴴ * (J * (B * P))) = Formalism.REAL.Jm ε := by rw [← hPG]; simp only [Matrix.mul_assoc]
    simp only [hQ, conjTranspose_fromCols_eq_fromRows_conjTranspose, Matrix.mul_assoc, mul_fromCols, fromRows_mul,
      conjTranspose_add, conjTranspose_sub, conjTranspose_smul, conjTranspose_mul, Matrix.mul_add, Matrix.mul_sub,
      Matrix.add_mul, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, h1, h2, h3, h3', h4', h5', a1, a2, a3]
    ext ((r | r) | r) ((s | s) | s) <;> simp [Matrix.one_apply] <;> split_ifs <;> norm_num
  have hF : (Q.submatrix id f)ᴴ * J * Q.submatrix id f = Formalism.REAL.Jm (δ ∘ f) := by
    have : (Q.submatrix id f)ᴴ * J * Q.submatrix id f = (Qᴴ * J * Q).submatrix f f := by
      ext r s; simp [Matrix.mul_apply]
    have hD : fromBlocks (fromBlocks 1 0 0 (-1)) 0 0 (Formalism.REAL.Jm ε) =
        diagonal fun a => if δ a = true then (1 : ℂ) else -1 := by
      ext ((r | r) | r) ((s | s) | s) <;> simp [hδ, Formalism.REAL.Jm, Matrix.one_apply, diagonal_apply]
      · split_ifs <;> simp
      · rfl
    rw [this, hQJ, hD, submatrix_diagonal_equiv]
    rfl
  have hU : IsUnit (Q.submatrix id f) :=
    IsUnit.of_mul_eq_one_right (Formalism.REAL.Jm (δ ∘ f) * ((Q.submatrix id f)ᴴ * J))
      (by rw [Matrix.mul_assoc, hF, Formalism.REAL.Jm_mul_self])
  obtain ⟨e1, e2⟩ := Formalism.UG.P.signature_unique _ J _ _ _ _ hs (hasSignature_of_frame hU hF)
  have hc : ∀ b : Bool, (univ.filter fun a => (δ ∘ f) a = b).card =
      (univ.filter fun a => ε a = b).card + Fintype.card κ := fun b => by
    rw [Finset.card_filter, Finset.card_filter]
    refine (Equiv.sum_comp f fun a => if δ a = b then 1 else 0).trans ?_
    rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
    cases b <;> simp [hδ, add_comm]
  rw [e1, e2, hc, hc, Nat.add_sub_cancel, Nat.add_sub_cancel]
  exact hasSignature_of_frame hP hPG

section Blocks

variable {E : Type} [Field E] {n : ℕ}


variable [NumberField E]




end Blocks




end GlobalTheory.AdaptedExists
