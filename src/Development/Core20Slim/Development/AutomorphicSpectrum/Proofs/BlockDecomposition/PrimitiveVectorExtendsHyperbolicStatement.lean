module

public import Mathlib
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PrimitiveVectorExtendsHyperbolic
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCovolOne
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HypOneZeroZero
public import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import Init.Core
public import Init.Data.Fin.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Maximal
public import Mathlib.RingTheory.Ideal.Span

@[expose] public section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.primitive_vector_extends_hyperbolic : ∀ (T : Type) [CommRing T] (O : Subring T) (s : T →+* T), (∀ y ∈ O, s y ∈ O) → (∀ y, s (s y) = y) → IsUnit (2 : O) → (∃ δ : O, IsUnit δ ∧ s δ = -δ) → ∀ π₁ π₂ : O, (∀ P : Ideal O, P.IsMaximal → P = Ideal.span {π₁} ∨ P = Ideal.span {π₂}) → ∀ (M : ℕ) (J Ji : Matrix (Fin M) (Fin M) T), (∀ i j, J i j ∈ O) → (∀ i j, Ji i j ∈ O) → J * Ji = 1 → (∀ i j, s (J j i) = J i j) → ∀ x : Fin (M + 2) → O, (∀ P : Ideal O, P.IsMaximal → ∃ i, x i ∉ P) → hform s (hypOne J) (fun i => (x i : T)) (fun i => (x i : T)) = 0 → ∃ g ∈ UJ s (hypOne J), (g : Matrix (Fin (M + 2)) (Fin (M + 2)) T) *ᵥ (e0 T M 0) = (fun i => (x i : T)) ∧ (∀ i j, (g : Matrix (Fin (M + 2)) (Fin (M + 2)) T) i j ∈ O) ∧ ∀ i j, ((g⁻¹ : GL (Fin (M + 2)) T) : Matrix (Fin (M + 2)) (Fin (M + 2)) T) i j ∈ O := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.HypStep.PrimTrans.trans_orbit | exact GlobalTheory.CompanionTheory.WeilSiegel.HypStep.PrimTrans.trans_orbit | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.HypStep.PrimTrans.trans_orbit <;> assumption)
