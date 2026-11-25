module

public import Mathlib
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HypOneZeroZero
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import Init.Core
public import Init.Data.Fin.Basic
public import Init.Data.Nat.Basic
public import Init.Data.NeZero
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Actions
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Subsemigroup.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Notation.Indicator
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Defs.Basic

@[expose] public section

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.HypStep

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Free

def e0 (K : Type) [Zero K] [One K] (M : ℕ) : Fin 1 → Fin (M + 2) → K :=
  fun _ => Fin.cons 1 fun _ => 0

def consA {K : Type} [Zero K] [One K] {M n : ℕ} (a : Fin 1 → Fin n → K) (Y : Fin n → Fin M → K) :
    Fin (n + 1) → Fin (M + 2) → K :=
  Fin.cons (Fin.cons 1 fun _ => 0) fun j => Fin.cons (a 0 j) (Fin.cons 0 (Y j))

section PiLocalization₂

variable {F E : Type} [Field F] [Field E] [Algebra F E]
variable (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R]

def stageInt (σ : E →ₐ[F] E) {M n d : ℕ} (J : Matrix (Fin M) (Fin M) E) (b : Module.Basis (Fin d) F E)
    (lam : Measure R) (m' : Measure (Fin n → Fin M → R ⊗[F] E))
    (φ : (Fin (n + 1) → Fin (M + 2) → R ⊗[F] E) → ℝ≥0∞) (g : HA R σ (hypOne J)) : ℝ≥0∞ :=
  ∫⁻ Y, ∫⁻ a, φ (actW R σ (hypOne J) g (consA a Y)) ∂(coordW R b lam 1 n) ∂m'

end PiLocalization₂

section Adelic

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

def latStab (σ : E →ₐ[F] E) {M d : ℕ} (J : Matrix (Fin M) (Fin M) E) (b : Module.Basis (Fin d) F E)
    (v : HeightOneSpectrum (𝓞 F)) (g : HA (Fv F v) σ J) : Prop :=
  ∀ x : Fin 1 → Fin M → Fv F v ⊗[F] E, actW (Fv F v) σ J g x ∈ latV b v ↔ x ∈ latV b v

def primV (σ : E →ₐ[F] E) {M d : ℕ} (J : Matrix (Fin M) (Fin M) E) (b : Module.Basis (Fin d) F E)
    (v : HeightOneSpectrum (𝓞 F)) : Set (Fin 1 → Fin (M + 2) → Fv F v ⊗[F] E) :=
  {y | ∃ g : HA (Fv F v) σ (hypOne J), latStab σ (hypOne J) b v g ∧
    actW (Fv F v) σ (hypOne J) g (e0 _ M) = y}

def purePr (σ : E →ₐ[F] E) {M d : ℕ} (J : Matrix (Fin M) (Fin M) E) (b : Module.Basis (Fin d) F E)
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (Ψinf : (Fin 1 → Fin (M + 2) → Ainf F ⊗[F] E) → ℝ≥0∞)
    (Ψ : ∀ v : HeightOneSpectrum (𝓞 F), (Fin 1 → Fin (M + 2) → Fv F v ⊗[F] E) → ℝ≥0∞)
    (y : Fin 1 → Fin (M + 2) → AF F ⊗[F] E) : ℝ≥0∞ :=
  {y : Fin 1 → Fin (M + 2) → AF F ⊗[F] E | ∀ v, v ∉ S → projV v (projFin y) ∈ primV σ J b v}.indicator
    (fun Y => Ψinf (projInf Y) * ∏ v ∈ S, Ψ v (projV v (projFin Y))) y

def ratA (n : ℕ) : AddSubgroup (Fin 1 → Fin n → AF F ⊗[F] E) where
  carrier := Set.range (ratTup (AF F) : (Fin 1 → Fin n → E) → Fin 1 → Fin n → AF F ⊗[F] E)
  zero_mem' := ⟨0, by funext a i; simp [ratTup]⟩
  add_mem' := by
    rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
    exact ⟨x + y, by funext a i; simp [ratTup]⟩
  neg_mem' := by
    rintro _ ⟨x, rfl⟩
    exact ⟨-x, by funext a i; simp [ratTup]⟩

def IsCovolOne {n : ℕ} (dA : Measure (Fin 1 → Fin n → AF F ⊗[F] E)) : Prop :=
  dA.IsAddHaarMeasure ∧ ∃ D : Set (Fin 1 → Fin n → AF F ⊗[F] E),
    IsAddFundamentalDomain (ratA (F := F) (E := E) n) D dA ∧ dA D = 1

end Adelic

end GlobalTheory.CompanionTheory.WeilSiegel.HypStep
