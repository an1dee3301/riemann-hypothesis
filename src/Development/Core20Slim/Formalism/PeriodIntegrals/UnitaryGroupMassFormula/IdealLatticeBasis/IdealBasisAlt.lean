module

public import Mathlib
public import Development.Core20Slim.Formalism.PeriodIntegrals.IdealLattice
public import Development.Core20Slim.Formalism.PeriodIntegrals.AreaLat
public import Init.Core
public import Init.Data.Fin.Basic
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.NeZero
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Order.Kleene
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.IsEmpty.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm

@[expose] public section

open NumberField

namespace PI.IdealLatticeWork

def OKArea : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (φ : K →+* ℂ), Module.finrank ℚ K = 2 → IsEmpty (K →+* ℝ) →
    ∀ b : Module.Basis (Fin 2) ℤ (𝓞 K),
      |((starRingEnd ℂ) (φ (b 0 : K)) * φ (b 1 : K)).im| = Real.sqrt |(NumberField.discr K : ℝ)| / 2

def IdealBasis : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (b : Module.Basis (Fin 2) ℤ (𝓞 K)) (cc : Ideal (𝓞 K)), cc ≠ ⊥ →
    ∃ c₁ ∈ cc, ∃ c₂ ∈ cc, (∀ c ∈ cc, ∃ m n : ℤ, c = m • c₁ + n • c₂) ∧
      ∃ p q r s : ℤ, c₁ = p • b 0 + q • b 1 ∧ c₂ = r • b 0 + s • b 1 ∧
        (p * s - q * r).natAbs = Ideal.absNorm cc

def OKBasis : Prop :=
  ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → Nonempty (Module.Basis (Fin 2) ℤ (𝓞 K))

def Assemble : Prop := OKArea → IdealBasis → OKBasis → PI.AreaLat → PI.IdealLattice

end PI.IdealLatticeWork
