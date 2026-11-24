module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerTransitive
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicStoneVonNeumannLagrangianUniquenessStatement
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Invertible.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Notation.Prod
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Tactic.LinearCombination.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section
namespace GlobalTheory.MixXEvUniq

open scoped Classical

section Alg

variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S] (c : S →ₐ[R] S)
  {α β γ δ : Type} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]



theorem schr_add [Invertible (2 : R)] (ψ : AddChar R ℂ) (a b : (α → R) × (α → R)) (h : a.1 ⬝ᵥ b.2 = b.1 ⬝ᵥ a.2)
    (φ : (α → R) → ℂ) : schr ψ (a + b) φ = schr ψ a (schr ψ b φ) := by
  funext x
  simp only [schr, Prod.fst_add, Prod.snd_add, add_dotProduct, dotProduct_add]
  rw [← mul_assoc, ← AddChar.map_add_eq_mul, add_assoc x, ← h]
  congr 2
  have h2 : (⅟(2 : R)) * 2 = 1 := invOf_mul_self _
  linear_combination (a.1 ⬝ᵥ b.2) * h2

end Alg

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}












variable {n n₁ d : ℕ} {X : Spc F E n} {X₁ : Spc F E n₁} {W : Spc F E d}




















end GlobalTheory.MixXEvUniq

end
