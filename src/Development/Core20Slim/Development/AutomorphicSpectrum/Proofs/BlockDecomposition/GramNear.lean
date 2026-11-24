module

public import Mathlib
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TrMMemFramesEIff
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaPartD
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBoundUnitary
public import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import Init.Classical
public import Init.Core
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Notation.Indicator
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Trace.Defs

@[expose] public section

noncomputable section

namespace GlobalTheory.CompanionTheory.WhitFree

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory
open scoped TensorProduct ENNReal Matrix

section Loc

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]

def gramNear (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E) (c : HermR R σ n) (U : Set (HermR R σ n)) :
    Set (Fin n → Fin M → R ⊗[F] E) :=
  {X | ∃ u ∈ U, (c : Matrix (Fin n) (Fin n) (R ⊗[F] E)) - gramR R σ J X = (u : Matrix (Fin n) (Fin n) (R ⊗[F] E))}

def gramTest (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E) (c : HermR R σ n) (ρ : HermR R σ n → ℝ)
    (X : Fin n → Fin M → R ⊗[F] E) : ℝ := by
  classical
  exact if h : (c : Matrix (Fin n) (Fin n) (R ⊗[F] E)) - gramR R σ J X ∈ HermR R σ n then ρ ⟨_, h⟩ else 0

end Loc

section Adelic

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

def boxF {M n : ℕ} (A : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin n → Fin M → Fv F v ⊗[F] E)) :
    Set (Fin n → Fin M → Af F ⊗[F] E) :=
  {X | ∀ v, projV v X ∈ A v}

def pureN {M n : ℕ} (φ : (Fin n → Fin M → Ainf F ⊗[F] E) → ℂ)
    (A : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin n → Fin M → Fv F v ⊗[F] E))
    (X : Fin n → Fin M → AF F ⊗[F] E) : ℂ :=
  φ (projInf X) * (boxF A).indicator (fun _ => (1 : ℂ)) (projFin X)

def intH (σ : E →ₐ[F] E) {d n : ℕ} (b : Module.Basis (Fin d) F E) (S : Finset (HeightOneSpectrum (𝓞 F))) :
    Set (HermR (AF F) σ n) :=
  {B | ∀ v, v ∉ S → projV v (projFin (fun a i => (B : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) a i)) ∈ latV (M := n) (n := n) b v}

def coefS (σ : E →ₐ[F] E) {d M n : ℕ} (J : Matrix (Fin M) (Fin M) E) (ψ : AddChar (AF F) ℂ)
    (dx : Measure (Fin n → Fin M → AF F ⊗[F] E)) (db : Measure (HermR (AF F) σ n))
    (Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ) (T : Matrix (Fin n) (Fin n) E)
    (b : Module.Basis (Fin d) F E) (S : Finset (HeightOneSpectrum (𝓞 F))) : ℂ :=
  ∫ B, (intH σ b S).indicator (fun _ => (1 : ℂ)) B *
    (GlobalTheory.CompanionTheory.SiegelND.starN σ J ψ dx Φ B * ψ (-(algebraMap F (AF F) (1 / 2) * Algebra.trace (AF F) (AF F ⊗[F] E)
      (Matrix.trace (T.map (inclR (AF F)) * (B : Matrix (Fin n) (Fin n) (AF F ⊗[F] E))))))) ∂db

end Adelic

end GlobalTheory.CompanionTheory.WhitFree
