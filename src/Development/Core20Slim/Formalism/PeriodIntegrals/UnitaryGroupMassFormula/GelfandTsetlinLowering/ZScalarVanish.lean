module

public import Mathlib
public import Development.Core20Slim.Formalism.PeriodIntegrals.GTDefs
public import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
public import Formalism.LocalRingCardinality.DataCoeff
public import Development.Core20Slim.Formalism.PeriodIntegrals.GTBranch
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Int.Lemmas
public import Init.Data.Int.Order
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Omega.Coeffs
public import Init.Omega.Constraint
public import Init.Omega.Int
public import Init.Omega.LinearCombo
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Module.Submodule.Map
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Erase
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Int.Cast.Lemmas
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Order.SetNotation
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic

@[expose] public section

noncomputable section

namespace PI.WGL

open Formalism.BasicNotions MvPolynomial

def IsEqv {n N : ℕ} (h : n + 1 = N) (mu : DomWeight n) (lam : DomWeight N)
    (φ : MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin N × Fin N) ℂ) : Prop :=
  (∀ s ∈ nablaSq ℂ n mu, φ s ∈ nablaSq ℂ N lam) ∧
  ∀ (g : GL (Fin n) ℂ), ∀ s ∈ nablaSq ℂ n mu, φ (sqAct ℂ n mu g s) = sqAct ℂ N lam (embGL ℂ n N h g) (φ s)

def LastWeight {n N : ℕ} (lam : DomWeight N) (sg : DomWeight n)
    (φ : MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin N × Fin N) ℂ) : Prop :=
  ∀ (a : ℂˣ), ∀ s ∈ nablaSq ℂ n sg,
    sqAct ℂ N lam (lastGL ℂ N a) (φ s) = ((a ^ degZ lam sg : ℂˣ) : ℂ) • φ s

def zScalar {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg mu : DomWeight n) : ℤ :=
  ∏ i : Fin n, ∏ v ∈ (Rset h lam sg i).erase (sg.w i), ∏ j : Fin n, ((v - (i.1 : ℤ)) - mu.w j + (j.1 : ℤ))

def Numbers : Prop :=
  ∀ (n N : ℕ) (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n), Interlace h lam sg →
    cBr h lam sg ≠ 0 ∧ |((cBr h lam sg : ℤ) : ℝ)| ≤ cBd h lam sg ∧
    degZ lam sg = lam.w ⟨0, by omega⟩ - D0 h lam sg

def ZScalarVanish : Prop :=
  ∀ (n N : ℕ) (h : n + 1 = N) (lam : DomWeight N) (sg mu : DomWeight n), Interlace h lam sg →
    Interlace h lam mu → mu.w ≠ sg.w → wsum mu = wsum sg → zScalar h lam sg mu = 0

def XiFacts : Prop :=
  ∀ (n N : ℕ) (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n), Interlace h lam sg →
    xi ℂ h lam sg ≠ 0 ∧ xi ℂ h lam sg ∈ nablaSq ℂ N lam ∧
    (∀ g : GL (Fin n) ℂ, (∀ i j, j < i → g i j = 0) → (∀ i, g i i = 1) →
      sqAct ℂ N lam (embGL ℂ n N h g) (xi ℂ h lam sg) = xi ℂ h lam sg) ∧
    (∀ t : Fin n → ℂˣ, sqAct ℂ N lam (embGL ℂ n N h (diagGL ℂ n t)) (xi ℂ h lam sg) =
      ((∏ j, t j ^ sg.w j : ℂˣ) : ℂ) • xi ℂ h lam sg) ∧
    (∀ a : ℂˣ, sqAct ℂ N lam (lastGL ℂ N a) (xi ℂ h lam sg) = ((a ^ degZ lam sg : ℂˣ) : ℂ) • xi ℂ h lam sg) ∧
    (∀ x ∈ Matrix.unitaryGroup (Fin N) ℂ,
      ‖MvPolynomial.eval (fun v : Fin N × Fin N => x v.1 v.2) (xi ℂ h lam sg)‖ ≤ 1)

def IoExists : Prop :=
  ∀ (n N : ℕ) (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n), Interlace h lam sg →
    ∃ io0 : MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin N × Fin N) ℂ,
      IsEqv h sg lam io0 ∧ io0 (extremal ℂ n sg) = xi ℂ h lam sg ∧ LastWeight lam sg io0

def IoIntegral : Prop :=
  ∀ (n N : ℕ) (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n), Interlace h lam sg →
    ∀ io0 : MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin N × Fin N) ℂ,
      IsEqv h sg lam io0 → io0 (extremal ℂ n sg) = xi ℂ h lam sg → LastWeight lam sg io0 →
      ∀ s ∈ nablaSq ℤ n sg, ∃ f ∈ nablaSq ℤ N lam,
        io0 (((cBr h lam sg : ℤ) : ℂ) • MvPolynomial.map (Int.castRingHom ℂ) s) =
          MvPolynomial.map (Int.castRingHom ℂ) f

def CapelliZ : Prop :=
  ∀ (n N : ℕ) (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n), Interlace h lam sg →
    ∃ Z : MvPolynomial (Fin N × Fin N) ℂ →ₗ[ℂ] MvPolynomial (Fin N × Fin N) ℂ,
      (∀ f ∈ nablaSq ℤ N lam, ∃ f' ∈ nablaSq ℤ N lam,
        Z (MvPolynomial.map (Int.castRingHom ℂ) f) = MvPolynomial.map (Int.castRingHom ℂ) f') ∧
      ∀ (mu : DomWeight n), Interlace h lam mu →
        ∀ φ : MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin N × Fin N) ℂ, IsEqv h mu lam φ →
          ∀ s ∈ nablaSq ℂ n mu, Z (φ s) = ((zScalar h lam sg mu : ℤ) : ℂ) • φ s

def OtherPart {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) :
    Submodule ℂ (MvPolynomial (Fin N × Fin N) ℂ) :=
  ⨆ (mu : DomWeight n) (_ : Interlace h lam mu) (_ : mu.w ≠ sg.w) (_ : wsum mu = wsum sg)
    (φ : MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin N × Fin N) ℂ) (_ : IsEqv h mu lam φ),
    (nablaSq ℂ n mu).map φ

def LiftMod : Prop :=
  ∀ (n N : ℕ) (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n), Interlace h lam sg →
    ∀ io0 : MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin N × Fin N) ℂ,
      IsEqv h sg lam io0 → io0 (extremal ℂ n sg) = xi ℂ h lam sg → LastWeight lam sg io0 →
      ∀ s ∈ nablaSq ℤ n sg, ∃ m ∈ nablaSq ℤ N lam,
        MvPolynomial.map (Int.castRingHom ℂ) m - io0 (MvPolynomial.map (Int.castRingHom ℂ) s) ∈ OtherPart h lam sg

def BrRest {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n)
    (br : MvPolynomial (Fin N × Fin N) ℂ →ₗ[ℂ] MvPolynomial (Fin n × Fin n) ℂ) : Prop :=
  (∀ f ∈ delSq ℂ N lam, br f ∈ delSq ℂ n sg) ∧
  (∃ f ∈ delSq ℂ N lam, br f ≠ 0) ∧
  (∀ (g : GL (Fin n) ℂ), ∀ f ∈ delSq ℂ N lam,
    br (sqAct ℂ N lam (embGL ℂ n N h g) f) = sqAct ℂ n sg g (br f)) ∧
  (∀ (a : ℂˣ), ∀ f ∈ delSq ℂ N lam,
    br (sqAct ℂ N lam (lastGL ℂ N a) f) = ((a ^ degZ lam sg : ℂˣ) : ℂ) • br f) ∧
  (∀ f ∈ delSq ℂ N lam,
    (normFock sg (br f) (br f)).re ≤ brBd h lam sg ^ 2 * (normFock lam f f).re)

def AdjointBr : Prop :=
  ∀ (n N : ℕ) (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n), Interlace h lam sg →
    ∀ io : MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin N × Fin N) ℂ,
      IsEqv h sg lam io → io (extremal ℂ n sg) = ((cBr h lam sg : ℤ) : ℂ) • xi ℂ h lam sg →
      LastWeight lam sg io →
      (∀ s ∈ nablaSq ℂ n sg, (normFock lam (io s) (io s)).re ≤ brBd h lam sg ^ 2 * (normFock sg s s).re) ∧
      ∃ br : MvPolynomial (Fin N × Fin N) ℂ →ₗ[ℂ] MvPolynomial (Fin n × Fin n) ℂ,
        BrRest h lam sg br ∧ IsTranspose lam sg io br

def BrIntegral : Prop :=
  ∀ (n N : ℕ) (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n), Interlace h lam sg →
    ∀ (io : MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin N × Fin N) ℂ)
      (br : MvPolynomial (Fin N × Fin N) ℂ →ₗ[ℂ] MvPolynomial (Fin n × Fin n) ℂ),
      (∀ s ∈ nablaSq ℤ n sg, ∃ f ∈ nablaSq ℤ N lam,
        io (MvPolynomial.map (Int.castRingHom ℂ) s) = MvPolynomial.map (Int.castRingHom ℂ) f) →
      (∀ s ∈ nablaSq ℂ n sg, io s ∈ nablaSq ℂ N lam) →
      (∀ f ∈ delSq ℂ N lam, br f ∈ delSq ℂ n sg) →
      IsTranspose lam sg io br →
      ∀ f ∈ delSq ℤ N lam, ∃ g ∈ delSq ℤ n sg,
        br (MvPolynomial.map (Int.castRingHom ℂ) f) = MvPolynomial.map (Int.castRingHom ℂ) g

end PI.WGL
