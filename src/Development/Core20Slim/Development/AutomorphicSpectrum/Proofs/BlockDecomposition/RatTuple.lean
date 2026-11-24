module

public import Mathlib
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaPartD
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBoundUnitary
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermInf
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermOf
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.FiniteAdeleTopologyStatement
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.CountData
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Nat.Basic
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
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Subsemigroup.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Finsupp.SMul
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Filter.Cofinite
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Free
public import Mathlib.RingTheory.Trace.Defs
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.Topology.Algebra.RestrictedProduct.Basic

@[expose] public section

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl

open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.CompanionTheory.SW.Core
open scoped Matrix TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

def InNOh {d : ℕ} (b : Module.Basis (Fin d) F E) (N : ℕ) (x : Af F ⊗[F] E) : Prop :=
  ∀ k, ∃ y ∈ Oh F, (Algebra.TensorProduct.basis (Af F) b).repr x k = (N : Af F) * y

def latN {d : ℕ} (b : Module.Basis (Fin d) F E) (n M N : ℕ) :
    AddSubgroup (Fin n → Fin M → Af F ⊗[F] E) where
  carrier := {X | ∀ a i, InNOh b N (X a i)}
  zero_mem' := fun a i k => ⟨0, fun v => zero_mem _, by simp⟩
  add_mem' := by
    intro X Y hX hY a i k
    obtain ⟨x, hx, ex⟩ := hX a i k
    obtain ⟨y, hy, ey⟩ := hY a i k
    refine ⟨x + y, fun v => add_mem (hx v) (hy v), ?_⟩
    simp only [Pi.add_apply, map_add (f := _), Finsupp.add_apply, ex, ey, mul_add]
  neg_mem' := by
    intro X hX a i k
    obtain ⟨x, hx, ex⟩ := hX a i k
    refine ⟨-x, fun v => neg_mem (hx v), ?_⟩
    simp only [Pi.neg_apply, map_neg, Finsupp.neg_apply, ex, mul_neg]

def gram2 (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (X Y : Fin n → Fin M → Af F ⊗[F] E) : Matrix (Fin n) (Fin n) (Af F ⊗[F] E) :=
  fun a c => hR (Af F) σ J (X a) (Y c)

def phaseB (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E) (ψf : Af F → ℂ)
    (b : HermR (Af F) σ n) (X : Fin n → Fin M → Af F ⊗[F] E) : ℂ :=
  ψf (algebraMap F (Af F) (1 / 2) * Algebra.trace (Af F) (Af F ⊗[F] E)
    (Matrix.trace ((b : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)) * gramR (Af F) σ J X)))

def pairB (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E) (ψf : Af F → ℂ)
    (b : HermR (Af F) σ n) (X Y : Fin n → Fin M → Af F ⊗[F] E) : ℂ :=
  ψf (Algebra.trace (Af F) (Af F ⊗[F] E)
    (Matrix.trace ((b : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)) * gram2 σ J X Y)))

def ratTuple [NumberField E] {M n : ℕ} (J : Matrix (Fin M) (Fin M) E) (s : ℕ) (ρ : Fin M → Fin n → 𝓞 E) :
    Fin n → Fin M → Af F ⊗[F] E :=
  fun a j => inclR (Af F) ((s : E) * (J⁻¹ *ᵥ fun i => algebraMap (𝓞 E) E (ρ i a)) j)

end GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl
