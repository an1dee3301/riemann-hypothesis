module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ContrFactor
public import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import Development.AbelianVarietyTheory.Definitions.Foundations.SimpleSum
public import Init.Classical
public import Init.Core
public import Init.Data.Nat.Lemmas
public import Init.Data.Zero
public import Init.Prelude
public import Init.PropLemmas
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
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
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Instances.Matrix

@[expose] public section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx

noncomputable section
namespace GlobalTheory.FlatFactor

section Gen
variable {k : Type} [Field k] {m m' : Type} [Fintype m] [DecidableEq m] [Fintype m'] [DecidableEq m']

def fill (ev it : Finset (m × m')) (β t : Matrix m m' k) (a : {e : m × m' // e ∈ it} → k) : Matrix m m' k :=
  Matrix.of fun r q => if h : (r, q) ∈ it then a ⟨(r, q), h⟩ else if (r, q) ∈ ev then β r q else t r q

variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]

def red (ν : Measure k) (ev it : Finset (m × m')) (β : Matrix m m' k) (Θ : Matrix m m' k → ℂ) (t : Matrix m m' k) : ℂ :=
  ∫ a, Θ (fill ev it β t a) ∂(Measure.pi fun _ => ν)

def KerRed {M : Type} [AddCommGroup M] [Module ℂ M] (ν : Measure k) (ev it : Finset (m × m')) (β : Matrix m m' k)
    (l : SB (Matrix m m' k) →ₗ[ℂ] M) : Prop :=
  ∀ Θ : SB (Matrix m m' k), (∀ t, red ν ev it β Θ.1 t = 0) → l Θ = 0

end Gen

section Pos
variable (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c ρ : ℕ)


open Classical in
def evC : Finset ((n ⊕ Fin c) × (n' ⊕ Fin (c + 1))) :=
  Finset.univ.filter fun e =>
    (∃ i, e.2 = Sum.inr i ∧ i.val < ρ ∧ ¬ Free (ρ + 1) e) ∨
    (∃ l, e.1 = Sum.inr l ∧ ρ ≤ l.val ∧ ∀ i, e.2 = Sum.inr i → i.val = ρ)


open Classical in
def itB : Finset ((n ⊕ Fin c) × (n' ⊕ Fin (c + 1))) :=
  Finset.univ.filter fun e => Free (ρ + 1) e ∧ ∀ i, e.2 = Sum.inr i → ρ ≤ i.val

def IsRead : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) → Prop
  | (.inl _, .inl _) => True
  | (.inl _, .inr i) => i.val = ρ
  | (.inr _, _) => False


open Classical in
def evAll : Finset ((n ⊕ Fin c) × (n' ⊕ Fin (c + 1))) :=
  Finset.univ.filter fun e => ¬ Free (ρ + 1) e ∧ ¬ IsRead n n' c ρ e


open Classical in
def itFree : Finset ((n ⊕ Fin c) × (n' ⊕ Fin (c + 1))) :=
  Finset.univ.filter fun e => Free (ρ + 1) e

variable {n n' c}
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def TwLaw {M : Type} [AddCommGroup M] [Module ℂ M] (ψ : AddChar k Circle)
    (l : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) →ₗ[ℂ] M) : Prop :=
  ∀ u : GL (Fin c) k, embA n u ∈ N k n c (ρ + 1) → (∀ i j : Fin c, i.val < ρ → ρ ≤ j.val → u.val i j = 0) →
    ∀ Θ Θ' Θ'' : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k),
      (∀ t, Θ'.1 t = Θ.1 (((embA n u)⁻¹).val * t)) →
      (∀ t, Θ''.1 t = (ψ (ch ((embA n u).val * t) - ch t) : ℂ) * Θ.1 t) →
      l Θ' = (ψ (-simpleSum (embA n u)) : ℂ) • l Θ''

end Pos

end GlobalTheory.FlatFactor
