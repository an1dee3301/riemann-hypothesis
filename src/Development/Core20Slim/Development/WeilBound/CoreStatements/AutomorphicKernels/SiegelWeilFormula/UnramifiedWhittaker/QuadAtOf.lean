module

public import Development.Core20Slim.Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.AlmostGoodOf
public import Development.Core20Slim.Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.BasisSet
public import Development.Core20Slim.Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.TraceDual
public import Development.Core20Slim.Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhitGenLowOf
public import Development.Core20Slim.Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.LocalDefs
public import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import Init.Classical
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.Divisibility.Basic
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.IsField
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Subsemigroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Order.Kleene
public import Mathlib.Algebra.Quotient
public import Mathlib.Algebra.Regular.SMul
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Int.Cast.Lemmas
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.SetTheory.Cardinal.Finite

@[expose] public section

noncomputable section

namespace PositivityTheory.SiegelWeilFormula.Gunr

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory PositivityTheory.PfSWUS.Loc PositivityTheory.SiegelWeilFormula.Gen Filter
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def QuadHyp (σ : E →ₐ[F] E) {d : ℕ} (bs : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F))
    (S : Subring (Fv F v ⊗[F] E)) (σS : S →+* S) (ϖ : v.adicCompletionIntegers F) : Prop :=
  IsCMExt F E σ ∧ IntAt v (basisSet σ bs) ∧ (S : Set (Fv F v ⊗[F] E)) = Rv bs v ∧
    (∀ x : S, ((σS x : S) : Fv F v ⊗[F] E) = sigR (Fv F v) σ x) ∧ (ϖ : Fv F v) ≠ 0 ∧ ‖(ϖ : Fv F v)‖ < 1 ∧
    (∀ x : v.adicCompletionIntegers F, ‖(x : Fv F v)‖ < 1 → ϖ ∣ x) ∧
    Nat.card (v.adicCompletionIntegers F ⧸ Ideal.span {ϖ}) = Ideal.absNorm v.asIdeal

def Q1 : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : ℕ)
    (bs : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (S : Subring (Fv F v ⊗[F] E)) (σS : S →+* S)
    (ϖ : v.adicCompletionIntegers F), QuadHyp σ bs v S σS ϖ →
  ∀ hϖ : algebraMap (Fv F v) (Fv F v ⊗[F] E) ϖ ∈ S,
    (∀ a, σS (σS a) = a) ∧ σS ⟨_, hϖ⟩ = ⟨_, hϖ⟩ ∧ IsSMulRegular S (⟨_, hϖ⟩ : S) ∧ ¬ IsUnit (⟨_, hϖ⟩ : S) ∧
    1 < Ideal.absNorm v.asIdeal

def Q2 : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : ℕ)
    (bs : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (S : Subring (Fv F v ⊗[F] E)) (σS : S →+* S)
    (ϖ : v.adicCompletionIntegers F), QuadHyp σ bs v S σS ϖ →
  ∀ hϖ : algebraMap (Fv F v) (Fv F v ⊗[F] E) ϖ ∈ S,
    (∀ a : S, (∀ k, a ∈ lev (⟨_, hϖ⟩ : S) k) → a = 0) ∧
    ∀ f : ℕ → S, (∀ k, f (k + 1) - f k ∈ lev (⟨_, hϖ⟩ : S) k) → ∃ a, ∀ k, a - f k ∈ lev (⟨_, hϖ⟩ : S) k

def Q3 : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : ℕ)
    (bs : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (S : Subring (Fv F v ⊗[F] E)) (σS : S →+* S)
    (ϖ : v.adicCompletionIntegers F), QuadHyp σ bs v S σS ϖ →
  ∀ hϖ : algebraMap (Fv F v) (Fv F v ⊗[F] E) ϖ ∈ S,
    Nat.card (S ⧸ lev (⟨_, hϖ⟩ : S) 1) = Ideal.absNorm v.asIdeal ^ 2

def Q4 : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : ℕ)
    (bs : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (S : Subring (Fv F v ⊗[F] E)) (σS : S →+* S)
    (ϖ : v.adicCompletionIntegers F), QuadHyp σ bs v S σS ϖ →
  ∀ hϖ : algebraMap (Fv F v) (Fv F v ⊗[F] E) ϖ ∈ S,
    (∀ a : S, σS a = a → a ∉ lev (⟨_, hϖ⟩ : S) 1 → IsUnit a) ∧
    ∃ u : S, IsUnit (u - σS u) ∧ ∀ a, ∃ x y, σS x = x ∧ σS y = y ∧ a = x + y * u

def Q5 : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : ℕ)
    (bs : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (S : Subring (Fv F v ⊗[F] E)) (σS : S →+* S)
    (ϖ : v.adicCompletionIntegers F), QuadHyp σ bs v S σS ϖ →
  ∀ hϖ : algebraMap (Fv F v) (Fv F v ⊗[F] E) ϖ ∈ S,
    (IsField (Fv F v ⊗[F] E) ↔ IsField (S ⧸ lev (⟨_, hϖ⟩ : S) 1))

theorem quadAt_of (h1 : Q1) (h2 : Q2) (h3 : Q3) (h4 : Q4) (h5 : Q5) : QuadAt := by
  intro F E _ _ _ _ _ σ hσ d bs v hB S σS hcar hsig ϖ hϖ0 hϖ1 hϖd hϖc hϖ ε hε
  have hH : QuadHyp σ bs v S σS ϖ := ⟨hσ, hB, hcar, hsig, hϖ0, hϖ1, hϖd, hϖc⟩
  obtain ⟨a1, a2, a3, a4, a5⟩ := h1 F E σ d bs v S σS ϖ hH hϖ
  obtain ⟨b1, b2⟩ := h2 F E σ d bs v S σS ϖ hH hϖ
  obtain ⟨c1, c2⟩ := h4 F E σ d bs v S σS ϖ hH hϖ
  have e5 := h5 F E σ d bs v S σS ϖ hH hϖ
  refine ⟨a1, a2, a3, a4, b1, b2, c1, c2, a5, h3 F E σ d bs v S σS ϖ hH hϖ, ?_⟩
  by_cases hf : IsField (Fv F v ⊗[F] E)
  · left
    refine ⟨?_, e5.1 hf⟩
    have : (ε : ℂ) = -1 := by rw [hε, eSp, if_pos hf]
    exact_mod_cast this
  · right
    refine ⟨?_, fun h => hf (e5.2 h)⟩
    have : (ε : ℂ) = 1 := by rw [hε, eSp, if_neg hf]
    exact_mod_cast this

end PositivityTheory.SiegelWeilFormula.Gunr

end
