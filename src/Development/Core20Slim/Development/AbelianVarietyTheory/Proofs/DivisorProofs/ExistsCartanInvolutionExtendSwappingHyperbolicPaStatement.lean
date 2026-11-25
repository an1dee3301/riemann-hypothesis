module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCartanInvolutionExtendSwappingHyperbolicPa
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs

@[expose] public section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cartanInvolution_extend_swapping_hyperbolicPair : ∀ (n n₁ : ℕ) (M : Matrix (Fin n) (Fin n) ℂ) (X Yv : Fin n → ℂ) (ι : Matrix (Fin n) (Fin n₁) ℂ)
    (P : Matrix (Fin n₁) (Fin n) ℂ) (θ₁ : Matrix (Fin n₁) (Fin n₁) ℂ), n = n₁ + 2 → Mᴴ = M →
    X ⬝ᵥ M *ᵥ star X = 0 → Yv ⬝ᵥ M *ᵥ star Yv = 0 → X ⬝ᵥ M *ᵥ star Yv = 1 →
    ιᵀ *ᵥ (M *ᵥ star X) = 0 → ιᵀ *ᵥ (M *ᵥ star Yv) = 0 → P * ι = 1 →
    IsCartan (ιᵀ * M * ι.map star) θ₁ → ∃ θ, IsCartan M θ ∧ θ * ι = ι * θ₁ ∧ θ *ᵥ X = Yv := by
  first | exact @GlobalTheory.CartanPlane.extend_swap | exact GlobalTheory.CartanPlane.extend_swap | (intros; apply GlobalTheory.CartanPlane.extend_swap <;> assumption)
