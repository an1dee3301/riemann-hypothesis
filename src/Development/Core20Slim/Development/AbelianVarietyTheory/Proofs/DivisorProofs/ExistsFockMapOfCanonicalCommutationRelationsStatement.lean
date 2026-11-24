module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFockMapOfCanonicalCommutationRelations
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Formalism.LocalRingCardinality.DataTheta
public import Init.Core
public import Init.Data.Function
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Notation.Pi.Basic
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Matrix.Basis
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.PiTensorProduct.Basic
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic

@[expose] public section

open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_fockMap_of_canonicalCommutationRelations : ∀ {V : Type} [AddCommGroup V] [Module ℂ V] {W : Type} [Fintype W] [DecidableEq W] {P Q R S : ℕ}
    (H : (W → Matrix (Ix P Q) (Ix R S) ℂ) → Module.End ℂ V),
    (∀ c c', H (c + c') = H c + H c') → (∀ (r : ℝ) c, H ((r : ℂ) • c) = (r : ℂ) • H c) →
    (∀ c c', H c * H c' - H c' * H c =
      ((4 * Real.pi : ℂ) * Complex.I * ((∑ w, ∑ a, ∑ b, lineSign a b * c w a b * star (c' w a b)).im : ℂ)) • 1) →
    ∀ f₀ : V, f₀ ≠ 0 →
    (∀ w a b, H (Pi.single w (Matrix.single a b 1)) f₀ +
      (lineSign a b * Complex.I) • H (Pi.single w (Matrix.single a b Complex.I)) f₀ = 0) →
    ∃ Φ : (⨂[ℂ] _ : W, Pol P Q R S) →ₗ[ℂ] V, Function.Injective Φ ∧
      ∀ c T, Φ (sumPl (fun w => heisOp (c w)) T) = H c (Φ T) := by
  first | exact @GlobalTheory.CCRFock.fock_map_of_ccr | exact GlobalTheory.CCRFock.fock_map_of_ccr | (intros; apply GlobalTheory.CCRFock.fock_map_of_ccr <;> assumption)
