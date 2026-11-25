module

public import Mathlib
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.ClsBoundAlt
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.IsSingTest
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.NullSec
public import Init.Core
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Logic.Function.Iterate
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
public import Mathlib.Topology.Algebra.Support
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

open MeasureTheory

namespace PositivityTheory.Rg.Sw.WR.D

open PositivityTheory.Rg.Sw

variable {m n : ℕ}

def hinv (T : Matrix (Fin n) (Fin n) ℂ) : E n := fun i j => (T i j).re + (T i j).im

def ip (y y' : E n) : ℝ := ∑ a, ∑ b, y a b * y' a b

def qX (ε : Fin m → Bool) (x : Fin m → Fin n → ℂ) : E n := hinv (gramX ε x)

def detQ (ε : Fin m → Bool) : PX m n := (Matrix.of fun i j => Qp ε i j).det

def FP (ε : Fin m → Bool) (c t : ℝ) (P : PX m n) (y : E n) : ℂ :=
  ∫ x, evX P x * gs c x * Complex.exp (Complex.I * t * ip y (qX ε x))

def AlgA : Prop :=
  ∀ (m n : ℕ) (ε : Fin m → Bool), (∀ (y : E n) (x : Fin m → Fin n → ℂ),
      (herm y * gramX ε x).trace = (ip y (qX ε x) : ℂ)) ∧
    (∀ x : Fin m → Fin n → ℂ, herm (qX ε x) = gramX ε x) ∧ (∀ y : E n, hinv (herm y) = y) ∧
    (∀ x : Fin m → Fin n → ℂ, evX (detQ ε) x = (gramX ε x).det) ∧ Continuous (qX (n := n) ε)

def IntG : Prop :=
  ∀ (m n : ℕ) (c : ℝ), 0 < c → ∀ P : PX m n, Integrable (fun x => evX P x * gs c x)

def DerivF : Prop :=
  ∀ (m n : ℕ) (ε : Fin m → Bool) (c t : ℝ), 0 < c → ∀ (P : PX m n) (N : ℕ),
    Continuous (FP ε c t P) ∧
    Delta^[N] (FP ε c t P) = FP ε c t ((MvPolynomial.C ((Complex.I * t) ^ n) * detQ ε) ^ N * P)

def MollId : Prop :=
  ∀ (n : ℕ) (X : Type) [MeasurableSpace X] (μ : Measure X) [SFinite μ] (Ψ : X → ℂ) (qq : X → E n), Integrable Ψ μ →
    Measurable qq → ∀ t : ℝ, t ≠ 0 →
    Integrable (fun y : E n => ∫ x, Ψ x * Complex.exp (Complex.I * t * ip y (qq x)) ∂μ) →
    ∀ ψ : E n → ℂ, Continuous ψ → HasCompactSupport ψ →
      ∫ x, ψ (qq x) * Ψ x ∂μ = ∫ β, ψ β * (((|t| / (2 * Real.pi)) ^ (n ^ 2) : ℝ) *
        ∫ y, (∫ x, Ψ x * Complex.exp (Complex.I * t * ip y (qq x)) ∂μ) * Complex.exp (-(Complex.I * t * ip β y)))

end PositivityTheory.Rg.Sw.WR.D
