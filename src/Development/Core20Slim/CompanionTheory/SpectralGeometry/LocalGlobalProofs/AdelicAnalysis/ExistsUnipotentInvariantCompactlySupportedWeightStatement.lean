module

public import Mathlib
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ExistsUnipotentInvariantCompactlySupportedWeight
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.ENNReal.Action
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Symmetric
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Module
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unipotentInvariant_compactlySupported_weight : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∀ (laminf : Measure (Ainf F)) (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)), IsStdInf laminf → (∀ v, IsStdV v (lam v)) → ∀ ψ, IsCharAF F ψ → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (B : Matrix ι ι F), B.IsSymm → B.det ≠ 0 → ∃ (cinf : ℝ≥0) (c : HeightOneSpectrum (𝓞 F) → ℝ≥0), IsUnitProd cinf c ∧ (∀ μ : Measure (ι → Ainf F), SelfDual μ (fun x y => psiInf F ψ (x ⬝ᵥ (B.map (algebraMap F (Ainf F)) *ᵥ y))) ↔ μ = cinf • Measure.pi fun _ => laminf) ∧ ∀ v : HeightOneSpectrum (𝓞 F), (∀ μ : Measure (ι → Fv F v), SelfDual μ (fun x y => psiV F ψ v (x ⬝ᵥ (B.map (algebraMap F (Fv F v)) *ᵥ y))) ↔ μ = c v • Measure.pi fun _ => lam v) := by
  first | exact @GlobalTheory.CompanionTheory.SW.SdCoord.selfDual_coord | exact GlobalTheory.CompanionTheory.SW.SdCoord.selfDual_coord | (intros; apply GlobalTheory.CompanionTheory.SW.SdCoord.selfDual_coord <;> assumption)
