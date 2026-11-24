module

public import Mathlib
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PrimitiveVectorsContentDecomposition
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsContent
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HypOneZeroZero
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCovolOne
public import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Filter.Cofinite
public import Mathlib.Order.Filter.Defs
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep GlobalTheory.CompanionTheory.WeilSiegel.HypMass
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.primitive_vectors_content_decomposition : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ (ι : Type) (c : ι → Fv F v ⊗[F] E) (w : ι → ℕ), IsContent σ b v c w → MeasurableSet (primV σ J b v) ∧ (∀ i, ∀ y ∈ primV σ J b v, scalT (c i) y ∈ latV b v) ∧ (∀ i j, ∀ y ∈ primV σ J b v, ∀ y' ∈ primV σ J b v, scalT (c i) y = scalT (c j) y' → i = j) ∧ (∀ y : Fin 1 → Fin (M + 2) → Fv F v ⊗[F] E, LinearIndependent (Fv F v ⊗[F] E) y → gramR (Fv F v) σ (hypOne J) y = 0 → y ∈ latV b v → ∃ i, ∃ y₀ ∈ primV σ J b v, y = scalT (c i) y₀) := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.HypMass.PrimDec.eventually_primV_decomposition | exact GlobalTheory.CompanionTheory.WeilSiegel.HypMass.PrimDec.eventually_primV_decomposition | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.HypMass.PrimDec.eventually_primV_decomposition <;> assumption)
