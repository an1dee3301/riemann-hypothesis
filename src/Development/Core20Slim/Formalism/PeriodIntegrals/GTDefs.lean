module

public import Mathlib
public import Formalism.LocalRingCardinality.DataCoeff
public import Development.Core20Slim.Formalism.PeriodIntegrals.GTBranch
public import Formalism.GradedWeylDivisibility.StatementA
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
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Erase
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Lemmas
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic

@[expose] public section

noncomputable section

namespace PI

open Formalism.BasicNotions MvPolynomial

def lastGL (R : Type) [CommRing R] (N : ℕ) (a : Rˣ) : GL (Fin N) R :=
  diagGL R N (fun i => if i.1 + 1 = N then a else 1)

def wsum {k : ℕ} (l : DomWeight k) : ℤ := ∑ i, l.w i

def aa {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) (i : Fin n) : ℤ :=
  sg.w i - lam.w ⟨i.1 + 1, by omega⟩

def bb {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) (i : Fin n) : ℤ :=
  lam.w ⟨i.1, by omega⟩ - sg.w i

def D0 {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) : ℤ :=
  ∑ i : Fin n, (sg.w i - lam.w ⟨i.1 + 1, by omega⟩)

def D1 {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) : ℤ :=
  ∑ i : Fin n, min (lam.w ⟨i.1, by omega⟩ - lam.w ⟨i.1 + 1, by omega⟩) (D0 h lam sg)

def degZ {n N : ℕ} (lam : DomWeight N) (sg : DomWeight n) : ℤ := wsum lam - wsum sg

def Rset {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) (i : Fin n) : Finset ℤ :=
  Finset.Icc (lam.w ⟨i.1 + 1, by omega⟩) (min (lam.w ⟨i.1, by omega⟩) (lam.w ⟨i.1 + 1, by omega⟩ + D0 h lam sg))

def cBr {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) : ℤ :=
  ∏ i : Fin n, ∏ v ∈ (Rset h lam sg i).erase (sg.w i), ∏ j : Fin n, ((v - (i.1 : ℤ)) - sg.w j + (j.1 : ℤ))

def rowsZ {n N : ℕ} (h : n + 1 = N) (i : Fin n) : Fin (i.1 + 1) → Fin N :=
  fun p => if p.1 = i.1 then ⟨N - 1, by omega⟩ else ⟨p.1, by omega⟩

def xi (R : Type) [CommRing R] {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) :
    MvPolynomial (Fin N × Fin N) R :=
  ∏ i : Fin n, (Formalism.GradedWeylDivisibility.lpMinor R (i.1 + 1) (by omega) (by omega)) ^ (aa h lam sg i).toNat *
    (Formalism.GradedWeylDivisibility.initMinor R (rowsZ h i) (by omega)) ^ (bb h lam sg i).toNat

def cBd {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) : ℝ :=
  (((2 * lam.spread : ℤ) : ℝ)) ^ ((((N : ℤ) * D1 h lam sg : ℤ) : ℝ))

def brBd {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) : ℝ :=
  cBd h lam sg * Real.sqrt (Module.finrank ℂ (delSq ℂ N lam))

def IsIota {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n)
    (io : MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin N × Fin N) ℂ) : Prop :=
  (∀ s ∈ nablaSq ℤ n sg, ∃ f ∈ nablaSq ℤ N lam,
    io (MvPolynomial.map (Int.castRingHom ℂ) s) = MvPolynomial.map (Int.castRingHom ℂ) f) ∧
  (∀ s ∈ nablaSq ℂ n sg, io s ∈ nablaSq ℂ N lam) ∧
  (∀ (g : GL (Fin n) ℂ), ∀ s ∈ nablaSq ℂ n sg,
    io (sqAct ℂ n sg g s) = sqAct ℂ N lam (embGL ℂ n N h g) (io s)) ∧
  io (extremal ℂ n sg) = ((cBr h lam sg : ℤ) : ℂ) • xi ℂ h lam sg ∧
  (∀ (a : ℂˣ), ∀ s ∈ nablaSq ℂ n sg,
    sqAct ℂ N lam (lastGL ℂ N a) (io s) = ((a ^ degZ lam sg : ℂˣ) : ℂ) • io s) ∧
  (∀ s ∈ nablaSq ℂ n sg,
    (normFock lam (io s) (io s)).re ≤ brBd h lam sg ^ 2 * (normFock sg s s).re)

def IsBr {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n)
    (br : MvPolynomial (Fin N × Fin N) ℂ →ₗ[ℂ] MvPolynomial (Fin n × Fin n) ℂ) : Prop :=
  (∀ f ∈ delSq ℤ N lam, ∃ g ∈ delSq ℤ n sg,
    br (MvPolynomial.map (Int.castRingHom ℂ) f) = MvPolynomial.map (Int.castRingHom ℂ) g) ∧
  (∀ f ∈ delSq ℂ N lam, br f ∈ delSq ℂ n sg) ∧
  (∃ f ∈ delSq ℂ N lam, br f ≠ 0) ∧
  (∀ (g : GL (Fin n) ℂ), ∀ f ∈ delSq ℂ N lam,
    br (sqAct ℂ N lam (embGL ℂ n N h g) f) = sqAct ℂ n sg g (br f)) ∧
  (∀ (a : ℂˣ), ∀ f ∈ delSq ℂ N lam,
    br (sqAct ℂ N lam (lastGL ℂ N a) f) = ((a ^ degZ lam sg : ℂˣ) : ℂ) • br f) ∧
  (∀ f ∈ delSq ℂ N lam,
    (normFock sg (br f) (br f)).re ≤ brBd h lam sg ^ 2 * (normFock lam f f).re)

def IsTranspose {n N : ℕ} (lam : DomWeight N) (sg : DomWeight n)
    (io : MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin N × Fin N) ℂ)
    (br : MvPolynomial (Fin N × Fin N) ℂ →ₗ[ℂ] MvPolynomial (Fin n × Fin n) ℂ) : Prop :=
  ∀ s ∈ nablaSq ℂ n sg, ∀ f ∈ delSq ℂ N lam, normFock lam (io s) f = normFock sg s (br f)

def Branch {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) : Prop :=
  cBr h lam sg ≠ 0 ∧ |((cBr h lam sg : ℤ) : ℝ)| ≤ cBd h lam sg ∧ xi ℂ h lam sg ≠ 0 ∧
  degZ lam sg = lam.w ⟨0, by omega⟩ - D0 h lam sg ∧
  ∃ (io : MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin N × Fin N) ℂ)
    (br : MvPolynomial (Fin N × Fin N) ℂ →ₗ[ℂ] MvPolynomial (Fin n × Fin n) ℂ),
    IsIota h lam sg io ∧ IsBr h lam sg br ∧ IsTranspose lam sg io br

end PI
