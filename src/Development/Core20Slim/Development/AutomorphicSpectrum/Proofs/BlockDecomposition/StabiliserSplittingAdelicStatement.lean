module

public import Mathlib
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StabiliserSplittingAdelic
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ActWOneApply
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HaarFundamentalDomainOrthogonalSum
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HypOneZeroZero
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCovolOne
public import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import Init.Core
public import Init.Data.Function
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Defs.Induced

@[expose] public section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep GlobalTheory.CompanionTheory.WeilSiegel.HypStep.Unf
open GlobalTheory.CompanionTheory.SW.ThetaStage
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stabiliser_splitting_adelic : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∃ (ι : HA (AF F) σ J →* stabilizer₂ (AF F) σ J) (π : stabilizer₂ (AF F) σ J →* HA (AF F) σ J), Continuous ι ∧ Continuous π ∧ (∀ u, π (ι u) = u) ∧ (∀ u ∈ HFinIn (AF F) σ J, ι u ∈ ratP (AF F) σ J) ∧ (∀ p ∈ ratP (AF F) σ J, π p ∈ HFinIn (AF F) σ J) ∧ (∃ K : Set (stabilizer₂ (AF F) σ J), IsCompact K ∧ ∀ m ∈ π.ker, ∃ γ ∈ ratP (AF F) σ J, π γ = 1 ∧ γ * m ∈ K) ∧ (∀ (k : ℕ) (u : HA (AF F) σ J) (a : Fin 1 → Fin k → AF F ⊗[F] E) (Y : Fin k → Fin M → AF F ⊗[F] E), actW (AF F) σ (hypOne J) (ι u : HA (AF F) σ (hypOne J)) (consA a Y) = consA a (actW (AF F) σ J u Y)) ∧ ∀ (k : ℕ) (Y : Fin k → Fin M → E), LinearIndependent E Y → ∃ l : π.ker → Fin 1 → Fin k → AF F ⊗[F] E, Continuous l ∧ (∀ x y, l (x * y) = l x + l y) ∧ Function.Surjective l ∧ (∀ m : π.ker, (m : stabilizer₂ (AF F) σ J) ∈ ratP (AF F) σ J → l m ∈ ratA (F := F) (E := E) k) ∧ ∀ (m : π.ker) (a : Fin 1 → Fin k → AF F ⊗[F] E), actW (AF F) σ (hypOne J) ((m : stabilizer₂ (AF F) σ J) : HA (AF F) σ (hypOne J)) (consA a (ratTup (AF F) Y)) = consA (a + l m) (ratTup (AF F) Y) := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.HypStep.Unf.Struct.stab_structure | exact GlobalTheory.CompanionTheory.WeilSiegel.HypStep.Unf.Struct.stab_structure | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.HypStep.Unf.Struct.stab_structure <;> assumption)
