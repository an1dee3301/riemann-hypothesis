module

public import Mathlib
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.IsSingTest
public import Init.Core
public import Init.Data.Sum.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MonoidAlgebra.Module
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Filter
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Set.Operations
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic

@[expose] public section

noncomputable section

open MeasureTheory MvPolynomial

namespace PositivityTheory.Rg.Sw

variable {m n : ℕ}

abbrev PX (m n : ℕ) := MvPolynomial (Fin m × Fin n × Bool) ℂ

def evX (P : PX m n) (x : Fin m → Fin n → ℂ) : ℂ :=
  MvPolynomial.eval (fun k => if k.2.2 then star (x k.1 k.2.1) else x k.1 k.2.1) P

def gs (c : ℝ) (x : Fin m → Fin n → ℂ) : ℂ := Complex.exp (-(c * ∑ a, ∑ i, ‖x a i‖ ^ 2 : ℝ))

def sgn (ε : Fin m → Bool) (a : Fin m) : ℂ := if ε a then 1 else -1

def Qb (ε : Fin m → Bool) (b : Bool) (i j : Fin n) : PX m n :=
  ∑ a ∈ Finset.univ.filter (fun a => ε a = b), X (a, i, true) * X (a, j, false)

def Qp (ε : Fin m → Bool) (i j : Fin n) : PX m n := Qb ε true i j - Qb ε false i j

def mom (c : ℝ) (P : PX m n) : ℂ := ∫ x : Fin m → Fin n → ℂ, evX P x * gs c x

def NullSec (ε : Fin m → Bool) (c : ℝ) (P : PX m n) : Prop :=
  ∀ R ∈ Algebra.adjoin ℂ (Set.range fun ij : Fin n × Fin n => (Qp ε ij.1 ij.2 : PX m n)), mom c (R * P) = 0

def hOp (ε : Fin m → Bool) (c : ℝ) (a b : Fin m) (P : PX m n) : PX m n :=
  ∑ i, (X (b, i, false) * pderiv (a, i, false) P - C (sgn ε a * sgn ε b) * X (a, i, true) * pderiv (b, i, true) P -
    C ((c : ℂ) * (1 - sgn ε a * sgn ε b)) * X (b, i, false) * X (a, i, true) * P)

def FFT : Prop :=
  ∀ (ι A B : Type) [Fintype ι] [DecidableEq ι] [Fintype A] [Fintype B] (p : MvPolynomial ((ι × A) ⊕ (ι × B)) ℂ),
    (∀ u ∈ Matrix.unitaryGroup ι ℂ, MvPolynomial.aeval (Sum.elim
        (fun x : ι × A => ∑ j, C (u x.1 j) * (X (Sum.inl (j, x.2)) : MvPolynomial ((ι × A) ⊕ (ι × B)) ℂ))
        (fun y : ι × B => ∑ j, C (star (u y.1 j)) * X (Sum.inr (j, y.2)))) p = p) →
    p ∈ Algebra.adjoin ℂ (Set.range fun ab : A × B =>
      ∑ i, (X (Sum.inl (i, ab.1)) : MvPolynomial ((ι × A) ⊕ (ι × B)) ℂ) * X (Sum.inr (i, ab.2)))

def Cyc : Prop :=
  ∀ (m n : ℕ) (ε : Fin m → Bool) (c : ℝ), 0 < c → ∀ P : PX m n,
    ∃ R ∈ Algebra.adjoin ℂ (Set.range fun k : Bool × Fin n × Fin n => (Qb ε k.1 k.2.1 k.2.2 : PX m n)), NullSec ε c (P - R)

def LC : Prop :=
  ∀ (m n : ℕ) (ε : Fin m → Bool) (c : ℝ), 0 < c → ∀ lam : PX m n →ₗ[ℂ] ℂ, (∀ a b P, lam (hOp ε c a b P) = 0) →
    ∀ P, NullSec ε c P → lam P = 0

def gramX (ε : Fin m → Bool) (x : Fin m → Fin n → ℂ) : Matrix (Fin n) (Fin n) ℂ := fun i j => evX (Qp ε i j) x

def secN (ε : Fin m → Bool) (c t : ℝ) (P : PX m n) (b : Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  ∫ x : Fin m → Fin n → ℂ, evX P x * gs c x * Complex.exp (Complex.I * t * (b * gramX ε x).trace)

def NullIff : Prop :=
  ∀ (m n : ℕ) (ε : Fin m → Bool) (c t : ℝ), 0 < c → t ≠ 0 → ∀ P : PX m n,
    NullSec ε c P ↔ ∀ b : Matrix (Fin n) (Fin n) ℂ, b.IsHermitian → secN ε c t P b = 0

end PositivityTheory.Rg.Sw
