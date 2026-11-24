module

public import Mathlib
public import Development.Core20Slim.Formalism.PeriodIntegrals.GTBranch
public import Formalism.PeriodIntegrals.HwIrred
public import Formalism.LocalRingCardinality.DataCoeff
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.Order.Kleene
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic

@[expose] public section

noncomputable section

namespace PI.WGB

open Formalism.BasicNotions MvPolynomial

def IsFixedW {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (mu : DomWeight n)
    (f : MvPolynomial (Fin N × Fin N) ℂ) : Prop :=
  (∀ g : GL (Fin n) ℂ, (∀ i j, j < i → g i j = 0) → (∀ i, g i i = 1) →
    sqAct ℂ N lam (embGL ℂ n N h g) f = f) ∧
  ∀ t : Fin n → ℂˣ, sqAct ℂ N lam (embGL ℂ n N h (diagGL ℂ n t)) f = ((∏ j, t j ^ mu.w j : ℂˣ) : ℂ) • f

def IsStable {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (W : Submodule ℂ (MvPolynomial (Fin N × Fin N) ℂ)) :
    Prop :=
  ∀ (g : GL (Fin n) ℂ), ∀ f ∈ W, sqAct ℂ N lam (embGL ℂ n N h g) f ∈ W

def IsEqv {n N : ℕ} (h : n + 1 = N) (mu : DomWeight n) (lam : DomWeight N)
    (φ : MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin N × Fin N) ℂ) : Prop :=
  (∀ s ∈ nablaSq ℂ n mu, φ s ∈ nablaSq ℂ N lam) ∧
  ∀ (g : GL (Fin n) ℂ), ∀ s ∈ nablaSq ℂ n mu, φ (sqAct ℂ n mu g s) = sqAct ℂ N lam (embGL ℂ n N h g) (φ s)

def ExtremalFacts : Prop :=
  ∀ (n : ℕ) (mu : DomWeight n),
    (∀ g : GL (Fin n) ℂ, (∀ i j, j < i → g i j = 0) → (∀ i, g i i = 1) →
      sqAct ℂ n mu g (extremal ℂ n mu) = extremal ℂ n mu) ∧
    (∀ t : Fin n → ℂˣ, sqAct ℂ n mu (diagGL ℂ n t) (extremal ℂ n mu) =
      ((∏ j, t j ^ mu.w j : ℂˣ) : ℂ) • extremal ℂ n mu) ∧
    (∀ (g : GL (Fin n) ℂ), ∀ s ∈ nablaSq ℂ n mu, sqAct ℂ n mu g s ∈ nablaSq ℂ n mu)

def FixedLine : Prop :=
  ∀ (n N : ℕ) (h : n + 1 = N) (lam : DomWeight N) (mu : DomWeight n) (f₁ f₂ : MvPolynomial (Fin N × Fin N) ℂ),
    f₁ ∈ nablaSq ℂ N lam → f₂ ∈ nablaSq ℂ N lam → IsFixedW h lam mu f₁ → IsFixedW h lam mu f₂ → f₂ ≠ 0 →
    (∃ c : ℂ, f₁ = c • f₂) ∧ Interlace h lam mu

def StableCompl : Prop :=
  ∀ (n N : ℕ) (h : n + 1 = N) (lam : DomWeight N) (W : Submodule ℂ (MvPolynomial (Fin N × Fin N) ℂ)),
    W ≤ nablaSq ℂ N lam → IsStable h lam W →
    ∃ W' : Submodule ℂ (MvPolynomial (Fin N × Fin N) ℂ), W' ≤ nablaSq ℂ N lam ∧ IsStable h lam W' ∧
      W ⊔ W' = nablaSq ℂ N lam ∧ W ⊓ W' = ⊥

def HighestVec : Prop :=
  ∀ (n N : ℕ) (h : n + 1 = N) (lam : DomWeight N) (W : Submodule ℂ (MvPolynomial (Fin N × Fin N) ℂ)),
    W ≤ nablaSq ℂ N lam → IsStable h lam W → W ≠ ⊥ →
    ∃ f ∈ W, f ≠ 0 ∧ ∃ mu : DomWeight n, IsFixedW h lam mu f

def Realize : Prop :=
  ∀ (n N : ℕ) (h : n + 1 = N) (lam : DomWeight N) (mu : DomWeight n) (f : MvPolynomial (Fin N × Fin N) ℂ),
    f ∈ nablaSq ℂ N lam → IsFixedW h lam mu f → f ≠ 0 →
    ∃ φ : MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin N × Fin N) ℂ,
      IsEqv h mu lam φ ∧ φ (extremal ℂ n mu) = f

end PI.WGB
