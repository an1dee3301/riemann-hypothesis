module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ContrFactor
public import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import Development.AbelianVarietyTheory.Definitions.Foundations.SimpleSum
public import Init.Classical
public import Init.Core
public import Init.Data.Fin.Basic
public import Init.Data.Nat.Lemmas
public import Init.Data.Sum.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.PropLemmas
public import Init.SimpLemmas
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.UnitBall
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Filter
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Sets
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Basis
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Instances.Matrix

@[expose] public section

open MeasureTheory Matrix

noncomputable section
namespace GlobalTheory.PartRed
open GlobalTheory.SplitWeil GlobalTheory.RootEx

section Gen
variable {k : Type} [Field k] {R Q : Type} [Fintype R] [Fintype Q] [DecidableEq R] [DecidableEq Q]

def fillAt (β : Matrix R Q k) (E I : Finset (R × Q)) (x : Matrix R Q k) (y : I → k) : Matrix R Q k :=
  Matrix.of fun r q => if h : (r, q) ∈ I then y ⟨(r, q), h⟩ else if (r, q) ∈ E then β r q else x r q

variable [TopologicalSpace k] [MeasurableSpace k]

def red (ψ : AddChar k Circle) (ν : Measure k) (w : Matrix R Q k →ₗ[k] k) (β : Matrix R Q k)
    (E I : Finset (R × Q)) (Φ : Matrix R Q k → ℂ) (x : Matrix R Q k) : ℂ :=
  ∫ y : I → k, Φ (fillAt β E I x y) * (ψ (-w (fillAt β E I x y)) : ℂ) ∂(Measure.pi fun _ => ν)

variable {M : Type} [AddCommGroup M] [Module ℂ M]

def Kills (L : SB (Matrix R Q k) →ₗ[ℂ] M) (ψ : AddChar k Circle) (ν : Measure k) (w : Matrix R Q k →ₗ[k] k)
    (β : Matrix R Q k) (E I : Finset (R × Q)) : Prop :=
  ∀ Φ : SB (Matrix R Q k), red ψ ν w β E I Φ.1 = 0 → L Φ = 0

def EvalLaw (L : SB (Matrix R Q k) →ₗ[ℂ] M) (ψ : AddChar k Circle) (ν : Measure k) (w : Matrix R Q k →ₗ[k] k)
    (β : Matrix R Q k) (E I : Finset (R × Q)) (e : R × Q) : Prop :=
  ∀ (b : k) (Φ : SB (Matrix R Q k)), ∃ Φ' : SB (Matrix R Q k), L Φ' = L Φ ∧
    ∀ x, red ψ ν w β E I Φ'.1 x = (ψ (b * (x e.1 e.2 - β e.1 e.2)) : ℂ) * red ψ ν w β E I Φ.1 x

def IntLaw (L : SB (Matrix R Q k) →ₗ[ℂ] M) (ψ : AddChar k Circle) (ν : Measure k) (w : Matrix R Q k →ₗ[k] k)
    (β : Matrix R Q k) (E I : Finset (R × Q)) (e : R × Q) : Prop :=
  ∀ (a : k) (Φ : SB (Matrix R Q k)), ∃ Φ' : SB (Matrix R Q k), L Φ' = L Φ ∧
    ∀ x, red ψ ν w β E I Φ'.1 x = red ψ ν w β E I Φ.1 (x + Matrix.single e.1 e.2 a)

end Gen

section Flat
variable {k : Type} [Field k] {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}

def chL : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k →ₗ[k] k where
  toFun := ch
  map_add' x y := by simp [ch, Finset.sum_add_distrib]
  map_smul' a x := by simp [ch, Finset.mul_sum]

theorem chL_apply (x : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) : chL x = ch x := rfl


open Classical in
def fixSet (ρ : ℕ) : Finset ((n ⊕ Fin c) × (n' ⊕ Fin (c + 1))) :=
  Finset.univ.filter fun e => (∃ i, e.2 = Sum.inr i ∧ i.val ≤ ρ ∧ ¬ Free (ρ + 1) e) ∨
    (∃ l s, e.1 = Sum.inr l ∧ ρ < l.val ∧ e.2 = Sum.inl s)


open Classical in
def transSet (ρ : ℕ) : Finset ((n ⊕ Fin c) × (n' ⊕ Fin (c + 1))) :=
  Finset.univ.filter fun e => Free (ρ + 1) e ∧ ∀ i, e.2 = Sum.inr i → ρ < i.val


open Classical in
def lowSet (ρ : ℕ) : Finset ((n ⊕ Fin c) × (n' ⊕ Fin (c + 1))) :=
  Finset.univ.filter fun e => ∃ (l : Fin c) (i : Fin (c + 1)), e = (Sum.inr l, Sum.inr i) ∧ ρ < i.val ∧ i.val ≤ l.val


open Classical in
def upSet (ρ : ℕ) : Finset ((n ⊕ Fin c) × (n' ⊕ Fin (c + 1))) :=
  Finset.univ.filter fun e => ∃ (l : Fin c) (i : Fin (c + 1)), e = (Sum.inr l, Sum.inr i) ∧ l.val < i.val ∧ i.val ≤ ρ

def colIx (e : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1))) : ℕ := Sum.elim (fun _ => 0) (fun i => i.val) e.2

end Flat

end GlobalTheory.PartRed
