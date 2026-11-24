module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Formalism.LocalRingCardinality.DataTheta
public import Init.Core
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.Algebra.Notation.Pi.Basic
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Matrix.Basis
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Multilinear.Basic
public import Mathlib.LinearAlgebra.PiTensorProduct.Basic
public import Mathlib.Logic.Pairwise
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic

@[expose] public section

open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift

noncomputable section

namespace GlobalTheory.CCRFock

variable {V : Type} [AddCommGroup V] [Module ℂ V]

open scoped IsMulCommutative in
def polEval {ι : Type} (m : ι → Module.End ℂ V) (hm : ∀ i j, m i * m j = m j * m i) (f₀ : V) :
    MvPolynomial ι ℂ →ₗ[ℂ] V :=
  letI : IsMulCommutative (Algebra.adjoin ℂ (Set.range m)) :=
    Algebra.isMulCommutative_adjoin ℂ (by
      rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ _
      exact hm i j)
  (LinearMap.applyₗ f₀ ∘ₗ (Algebra.adjoin ℂ (Set.range m)).val.toLinearMap) ∘ₗ
    (MvPolynomial.aeval (fun i => (⟨m i, Algebra.subset_adjoin ⟨i, rfl⟩⟩ : Algebra.adjoin ℂ (Set.range m)))).toLinearMap

def polMap (W Λ : Type) [Fintype W] [DecidableEq W] :
    (⨂[ℂ] _ : W, MvPolynomial Λ ℂ) →ₗ[ℂ] MvPolynomial (W × Λ) ℂ :=
  PiTensorProduct.lift ((MultilinearMap.mkPiAlgebra ℂ W (MvPolynomial (W × Λ) ℂ)).compLinearMap
    fun w => (MvPolynomial.rename (Prod.mk w)).toLinearMap)

def unitAt {W : Type} [DecidableEq W] {P Q R S : ℕ} (j : W × (Ix P Q × Ix R S)) (z : ℂ) :
    W → Matrix (Ix P Q) (Ix R S) ℂ :=
  Pi.single j.1 (Matrix.single j.2.1 j.2.2 z)

def fockM {W : Type} [DecidableEq W] {P Q R S : ℕ} (H : (W → Matrix (Ix P Q) (Ix R S) ℂ) → Module.End ℂ V)
    (j : W × (Ix P Q × Ix R S)) : Module.End ℂ V :=
  (2 * ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ))⁻¹ •
    (H (unitAt j 1) - (lineSign j.2.1 j.2.2 * Complex.I) • H (unitAt j Complex.I))

def fockD {W : Type} [DecidableEq W] {P Q R S : ℕ} (H : (W → Matrix (Ix P Q) (Ix R S) ℂ) → Module.End ℂ V)
    (j : W × (Ix P Q × Ix R S)) : Module.End ℂ V :=
  -((2 * ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ))⁻¹ •
    (H (unitAt j 1) + (lineSign j.2.1 j.2.2 * Complex.I) • H (unitAt j Complex.I)))

def coefM (z ε : ℂ) : ℂ := (z.re : ℂ) + ε * Complex.I * (z.im : ℂ)

def coefD (z ε : ℂ) : ℂ := -(z.re : ℂ) + ε * Complex.I * (z.im : ℂ)

end GlobalTheory.CCRFock
