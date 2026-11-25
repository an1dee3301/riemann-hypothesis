module

public import Mathlib
public import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
public import Formalism.LocalRingCardinality.DataCoeff
public import Formalism.LocalToGlobal.Divisibility.CoefMod
public import Init.Core
public import Init.Data.Fin.Lemmas
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Nat.Basic
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Order.Basic
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic

@[expose] public section

open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.ScaledCoisometryNorms

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Col.Br

def sumGram {K : Type} [Zero K] (N : ℕ) {n : ℕ} (G' : Matrix (Fin n) (Fin n) K) (g : K) : Matrix (Fin N) (Fin N) K :=
  Matrix.of fun a b =>
    if ha : a.1 < n then (if hb : b.1 < n then G' ⟨a.1, ha⟩ ⟨b.1, hb⟩ else 0) else (if b.1 < n then 0 else g)

theorem sumGram_entries {K : Type} [Zero K] {N n : ℕ} (hN : N = n + 1) (G' : Matrix (Fin n) (Fin n) K) (g : K) :
    (∀ a b : Fin n, sumGram N G' g (iC hN a) (iC hN b) = G' a b) ∧
      (∀ a : Fin n, sumGram N G' g (iC hN a) (iL hN) = 0 ∧ sumGram N G' g (iL hN) (iC hN a) = 0) ∧
      sumGram N G' g (iL hN) (iL hN) = g := by
  refine ⟨fun a b => ?_, fun a => ⟨?_, ?_⟩, ?_⟩ <;> simp [sumGram, iC, iL]

def nrmSq {K : Type} [Field K] [StarRing K] (s : K →+* ℂ) {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n)
    (G : ι → Matrix (Fin n) (Fin n) K) (f : VV K lam) : ℝ :=
  (s (pairK lam G f f)).re

def IsScaledCoisometry {K : Type} [Field K] [StarRing K] (s : K →+* ℂ) {ι : Type} [Fintype ι] {N n : ℕ}
    (lam : ι → DomWeight N) (sg : ι → DomWeight n) (G : ι → Matrix (Fin N) (Fin N) K) (G' : ι → Matrix (Fin n) (Fin n) K)
    (P : VV K lam →ₗ[K] VV K sg) (κ : ℝ) : Prop :=
  ∃ Q : VV K sg →ₗ[K] VV K lam,
    (∀ (y : VV K sg) (f : VV K lam), pairK lam G (Q y) f = pairK sg G' y (P f)) ∧
    ∀ y y' : VV K sg, s (pairK lam G (Q y) (Q y')) = (κ : ℂ) * s (pairK sg G' y y')


def brSq {ι : Type} [Fintype ι] {N n : ℕ} (hN : N = n + 1) (lam : ι → DomWeight N) (sg : ι → DomWeight n) (T : ℝ) : ℝ :=
  ∏ τ, T ^ (-nBr (lam τ) (sg τ)) * (((cBr hN (lam τ) (sg τ) : ℤ) : ℝ) ^ 2 * kapBr ℝ hN (lam τ) (sg τ))

def NormConcl {K : Type} [Field K] [StarRing K] (s : K →+* ℂ) {ι : Type} [Fintype ι] {N n : ℕ} (hN : N = n + 1)
    (lam : ι → DomWeight N) (sg : ι → DomWeight n) (G : ι → Matrix (Fin N) (Fin N) K) (G' : ι → Matrix (Fin n) (Fin n) K)
    (t : ι → K) (T : ℝ) : Prop :=
  0 < brSq hN lam sg T ∧
  IsScaledCoisometry s lam sg G G' (brAt hN lam sg t) (brSq hN lam sg T) ∧
  (∀ f : VV K lam, nrmSq s sg G' (brAt hN lam sg t f) ≤ brSq hN lam sg T * nrmSq s lam G f) ∧
  ∃ f : VV K lam, f ≠ 0 ∧ nrmSq s sg G' (brAt hN lam sg t f) = brSq hN lam sg T * nrmSq s lam G f

def BrNorm : Prop :=
  ∀ (K : Type) [Field K] [StarRing K] (s : K →+* ℂ), (∀ x, s (star x) = star (s x)) →
  ∀ (ι : Type) [Fintype ι] (N n : ℕ) (hN : N = n + 1) (lam : ι → DomWeight N) (sg : ι → DomWeight n),
    (∀ τ, Interlace hN (lam τ) (sg τ)) → (∀ τ, SameShift (lam τ) (sg τ)) →
  ∀ (G' : ι → Matrix (Fin n) (Fin n) K), (∀ τ, ((G' τ).map s).PosDef) →
  ∀ (g t : ι → K) (T : ℝ), 0 < T → (∀ τ, ((‖s (t τ)‖ ^ 2 : ℝ) : ℂ) * s (g τ) = (T : ℂ)) →
    NormConcl s hN lam sg (fun τ => sumGram N (G' τ) (g τ)) G' t T




end GlobalTheory.IndefiniteRowSideFullHecke.ScaledCoisometryNorms
