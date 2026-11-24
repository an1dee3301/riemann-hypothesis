module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOrthogonalComplementEmbeddingHyperbolicPai
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.NumberTheory.NumberField.Basic

@[expose] public section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_orthogonalComplement_embedding_hyperbolicPair : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (n n₁ : ℕ) (J : Matrix (Fin n) (Fin n) E) (x y : Fin n → E),
    n = n₁ + 2 → (∀ i j, σ (J j i) = J i j) → form σ J x x = 0 → form σ J y y = 0 → form σ J x y = 1 →
    ∃ (ι : Matrix (Fin n) (Fin n₁) E) (P : Matrix (Fin n₁) (Fin n) E), P * ι = 1 ∧
      (∀ u, form σ J (ι *ᵥ u) x = 0 ∧ form σ J (ι *ᵥ u) y = 0) ∧
      ∀ z, form σ J z x = 0 → form σ J z y = 0 → ∃ u, z = ι *ᵥ u := by
  first | exact @GlobalTheory.exists_orthCompl_hypPair | exact GlobalTheory.exists_orthCompl_hypPair | (intros; apply GlobalTheory.exists_orthCompl_hypPair <;> assumption)
