module

public import Development.Core20Slim.Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.BasisSet
public import Development.Core20Slim.Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.TraceDual
public import Development.Core20Slim.Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhitGenLowOf
public import Development.Core20Slim.Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.LocalDefs
public import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.Divisibility.Basic
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Subsemigroup.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Order.Kleene
public import Mathlib.Algebra.Quotient
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
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
public import Mathlib.RingTheory.Trace.Defs
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.SetTheory.Cardinal.Finite

@[expose] public section

noncomputable section

namespace PositivityTheory.SiegelWeilFormula.Gunr

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory PositivityTheory.PfSWUS.Loc PositivityTheory.SiegelWeilFormula.Gen Filter
open scoped TensorProduct

def LocRingE : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
  ∀ (d : ℕ) (bs : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)), IntAt v (basisSet σ bs) →
  ∃ (S : Subring (Fv F v ⊗[F] E)) (σS : S →+* S) (ϖ : Fv F v) (ε : ℤ)
    (hϖ : algebraMap (Fv F v) (Fv F v ⊗[F] E) ϖ ∈ S),
    (ε : ℂ) = eSp E v ∧ (S : Set (Fv F v ⊗[F] E)) = Rv bs v ∧
    (∀ x : S, ((σS x : S) : Fv F v ⊗[F] E) = sigR (Fv F v) σ x) ∧
    (∀ x : Fv F v ⊗[F] E, sigR (Fv F v) σ x = x → ∃ c : Fv F v, x = algebraMap (Fv F v) (Fv F v ⊗[F] E) c) ∧
    ϖ ∈ v.adicCompletionIntegers F ∧ ϖ ≠ 0 ∧ ‖ϖ‖ < 1 ∧
    IsUnrQuad S σS ⟨_, hϖ⟩ (Ideal.absNorm v.asIdeal) ε ∧ ‖(2 : Fv F v)‖ = 1 ∧
    ∀ a : Fv F v ⊗[F] E,
      (∀ b ∈ S, Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (a * b) ∈ v.adicCompletionIntegers F) ↔ a ∈ S

def RvRing : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (d : ℕ) (bs : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)), IntAt v (basisSet σ bs) →
  ∃ (S : Subring (Fv F v ⊗[F] E)) (σS : S →+* S), (S : Set (Fv F v ⊗[F] E)) = Rv bs v ∧
    ∀ x : S, ((σS x : S) : Fv F v ⊗[F] E) = sigR (Fv F v) σ x

def FixedK : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
  ∀ (v : HeightOneSpectrum (𝓞 F)) (x : Fv F v ⊗[F] E), sigR (Fv F v) σ x = x →
    ∃ c : Fv F v, x = algebraMap (Fv F v) (Fv F v ⊗[F] E) c

def UnifEx : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)), ∃ ϖ : v.adicCompletionIntegers F,
    ((ϖ : Fv F v) ≠ 0) ∧ ‖(ϖ : Fv F v)‖ < 1 ∧ (∀ x : v.adicCompletionIntegers F, ‖(x : Fv F v)‖ < 1 → ϖ ∣ x) ∧
    Nat.card (v.adicCompletionIntegers F ⧸ Ideal.span {ϖ}) = Ideal.absNorm v.asIdeal

def QuadAt : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
  ∀ (d : ℕ) (bs : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)), IntAt v (basisSet σ bs) →
  ∀ (S : Subring (Fv F v ⊗[F] E)) (σS : S →+* S), (S : Set (Fv F v ⊗[F] E)) = Rv bs v →
    (∀ x : S, ((σS x : S) : Fv F v ⊗[F] E) = sigR (Fv F v) σ x) →
  ∀ ϖ : v.adicCompletionIntegers F, (ϖ : Fv F v) ≠ 0 → ‖(ϖ : Fv F v)‖ < 1 →
    (∀ x : v.adicCompletionIntegers F, ‖(x : Fv F v)‖ < 1 → ϖ ∣ x) →
    Nat.card (v.adicCompletionIntegers F ⧸ Ideal.span {ϖ}) = Ideal.absNorm v.asIdeal →
  ∀ hϖ : algebraMap (Fv F v) (Fv F v ⊗[F] E) ϖ ∈ S, ∀ ε : ℤ, (ε : ℂ) = eSp E v →
    IsUnrQuad S σS ⟨_, hϖ⟩ (Ideal.absNorm v.asIdeal) ε

def TraceDualAt : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
  ∀ (d : ℕ) (bs : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)), IntAt v (basisSet σ bs) →
  ∀ a : Fv F v ⊗[F] E,
    (∀ b ∈ Rv bs v, Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (a * b) ∈ v.adicCompletionIntegers F) ↔ a ∈ Rv bs v

end PositivityTheory.SiegelWeilFormula.Gunr

end
