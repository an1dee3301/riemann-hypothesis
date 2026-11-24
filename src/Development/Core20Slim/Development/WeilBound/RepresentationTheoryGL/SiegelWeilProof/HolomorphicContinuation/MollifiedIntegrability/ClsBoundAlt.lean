module

public import Mathlib
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.NullSec
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.IsSingTest
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.List.Basic
public import Init.Data.List.FinRange
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.ENat.Defs
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Filter
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Logic.Function.Iterate
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.Order.Notation
public import Mathlib.Order.TypeTags
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

open MeasureTheory Matrix

namespace PositivityTheory.Rg.Sw.WR

open PositivityTheory.Rg.Sw

variable {n : ℕ}

abbrev E (n : ℕ) := Fin n → Fin n → ℝ

def uM (s : ℂ) (y : E n) : Matrix (Fin n) (Fin n) ℂ := (1 - (Complex.I * s) • herm y)⁻¹

def vM (s : ℂ) (y : E n) : Matrix (Fin n) (Fin n) ℂ := (1 + (Complex.I * s) • herm y)⁻¹

def dP (y : E n) : ℝ := (1 + herm y * herm y).det.re

def evUV (s : ℂ) (R : MvPolynomial (Bool × Fin n × Fin n) ℂ) (y : E n) : ℂ :=
  MvPolynomial.eval (fun k => if k.1 then vM s y k.2.1 k.2.2 else uM s y k.2.1 k.2.2) R

def cls (s z : ℂ) (p q : ℕ) (R : MvPolynomial (Bool × Fin n × Fin n) ℂ) (y : E n) : ℂ :=
  ((dP y : ℝ) : ℂ) ^ (-z) * (uM s y).det ^ p * (vM s y).det ^ q * evUV s R y

def vkl (k l : Fin n) : Fin n → Fin n → ℂ := fun a b =>
  (if a = k ∧ b = l then (1 + Complex.I) / 2 else 0) + (if a = l ∧ b = k then (1 - Complex.I) / 2 else 0)

def dirC (f : E n → ℂ) (w : Fin n → Fin n → ℂ) (y : E n) : ℂ :=
  fderiv ℝ f y (fun a b => (w a b).re) + Complex.I * fderiv ℝ f y (fun a b => (w a b).im)

def Dkl (k l : Fin n) (f : E n → ℂ) : E n → ℂ := dirC f (vkl k l)

def Delta (f : E n → ℂ) : E n → ℂ :=
  ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℂ) • (List.finRange n).foldr (fun k g => Dkl k (σ k) g) f

def chr (t : ℝ) (β : E n) (y : E n) : ℂ := Complex.exp (-(Complex.I * t * ∑ a, ∑ b, β a b * y a b))

def Gauss : Prop :=
  ∀ (m n : ℕ) (ε : Fin m → Bool) (c t : ℝ), 0 < c → (t = c ∨ t = -c) → ∀ P : PX m n,
    ∃ R : MvPolynomial (Bool × Fin n × Fin n) ℂ, ∀ y : E n,
      secN ε c t P (herm y) = cls ((t / c : ℝ) : ℂ) 0 (Finset.univ.filter fun a => ε a = true).card
        (Finset.univ.filter fun a => ε a = false).card R y

def ClsBound : Prop :=
  ∀ (n : ℕ) (s : ℂ), (s = 1 ∨ s = -1) → ∀ (p q : ℕ) (R : MvPolynomial (Bool × Fin n × Fin n) ℂ) (z : ℂ),
    ContDiff ℝ (⊤ : ℕ∞) (cls s z p q R) ∧ ∀ L : List (Fin n × Fin n), ∃ C : ℝ, ∀ y,
      ‖L.foldr (fun kl g => Dkl kl.1 kl.2 g) (cls s z p q R) y‖ ≤ C * (dP y) ^ (-(z.re + (p + q : ℝ) / 2))

def ClsGain : Prop :=
  ∀ (n : ℕ) (s : ℂ), (s = 1 ∨ s = -1) → ∀ (p q N : ℕ) (R : MvPolynomial (Bool × Fin n × Fin n) ℂ),
    ∃ (J : ℕ) (a : Fin J → Polynomial ℂ) (G : Fin J → E n → ℂ), (∀ j, Continuous (G j)) ∧
      (∃ C : ℝ, ∀ j y, ‖G j y‖ ≤ C * (dP y) ^ (-((p + q + N : ℕ) : ℝ) / 2)) ∧
      ∀ z y, (Delta^[N] (cls s z p q R)) y = ((dP y : ℝ) : ℂ) ^ (-z) * ∑ j, (a j).eval z * G j y

def IBP : Prop :=
  ∀ (n : ℕ) (f : E n → ℂ) (t : ℝ) (β : E n), ContDiff ℝ (⊤ : ℕ∞) f → t ≠ 0 → (herm β).det ≠ 0 →
    (∀ L : List (Fin n × Fin n), ∃ h : E n → ℝ, Integrable h ∧ ∀ y, ‖L.foldr (fun kl g => Dkl kl.1 kl.2 g) f y‖ ≤ h y) →
    ∫ y, f y * chr t β y = (-1) ^ n * ((-(Complex.I * t)) ^ n * (herm β).det)⁻¹ * ∫ y, Delta f y * chr t β y

def Integr : Prop :=
  ∀ (n : ℕ), (∃ c : ℝ, 0 < c ∧ ∀ y : E n, c * (1 + ∑ a, ∑ b, y a b ^ 2) ≤ dP y) ∧
    ∀ σ : ℝ, (n : ℝ) ^ 2 / 2 < σ → Integrable fun y : E n => (dP y) ^ (-σ)

def Dens : Prop :=
  ∀ (m n : ℕ) (ε : Fin m → Bool) (c t : ℝ), 0 < c → (t = c ∨ t = -c) → ∀ (P : PX m n) (N : ℕ),
    (n : ℝ) ^ 2 < (m + N : ℕ) →
    ∃ g : E n → ℂ, ContinuousOn g {y | (herm y).det ≠ 0} ∧
      (∀ S : Set (E n), IsCompact S → S ⊆ {y | (herm y).det ≠ 0} →
        ∫ x in gramX ε ⁻¹' (herm '' S), evX P x * gs c x = ∫ y in S, g y) ∧
      ∀ β : E n, (herm β).det ≠ 0 →
        ((2 * Real.pi / |t|) ^ (n ^ 2) : ℝ) * g β =
          ((herm β).det ^ N)⁻¹ * ((-1) ^ n / ((-(Complex.I * t)) ^ n)) ^ N *
            ∫ y, (Delta^[N] (fun y => secN ε c t P (herm y))) y * chr t β y

def WRSt : Prop :=
  ∀ (m n : ℕ) (ε : Fin m → Bool) (c t : ℝ), 0 < c → (t = c ∨ t = -c) → ∀ P : PX m n,
    ∃ g : E n → ℂ, ContinuousOn g {y | (herm y).det ≠ 0} ∧
      (∀ S : Set (E n), IsCompact S → S ⊆ {y | (herm y).det ≠ 0} →
        ∫ x in gramX ε ⁻¹' (herm '' S), evX P x * gs c x = ∫ y in S, g y) ∧
      ∀ β : E n, (herm β).det ≠ 0 → ∃ W : ℂ → ℂ, Differentiable ℂ W ∧
        (∃ σ₀ : ℝ, ∀ z : ℂ, σ₀ < z.re →
          Integrable (fun y => ((dP y : ℝ) : ℂ) ^ (-z) * secN ε c t P (herm y) * chr t β y) ∧
          W z = ∫ y, ((dP y : ℝ) : ℂ) ^ (-z) * secN ε c t P (herm y) * chr t β y) ∧
        W 0 = ((2 * Real.pi / |t|) ^ (n ^ 2) : ℝ) * g β

end PositivityTheory.Rg.Sw.WR
