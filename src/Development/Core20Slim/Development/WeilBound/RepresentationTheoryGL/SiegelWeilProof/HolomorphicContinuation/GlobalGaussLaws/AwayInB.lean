module

public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.AwayInA
public import Init.Core
public import Init.Data.Bool
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.Archimedean.Real.Hom
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Distribution.TemperateGrowth
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Sets
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Topology.Algebra.ConstMulAction
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd
public import Mathlib.Topology.Algebra.Module.Equiv.Basic
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.MetricSpace.Algebra
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.UniformSpace.Defs
public import Mathlib.Topology.UniformSpace.Real

@[expose] public section

noncomputable section

open scoped Matrix ComplexConjugate SchwartzMap
open Matrix

namespace PositivityTheory.Rg.Sw.Glob.AwayPf

section
variable {T : Type} [Fintype T] [DecidableEq T] {m n : ℕ} (τ : T)

abbrev Bsp (τ : T) (m n : ℕ) : Type := {τ' : T // τ' ≠ τ} → Fin m → Fin n → ℂ

def extF (b : Bsp τ m n) : T → Fin m → Fin n → ℂ := fun τ' => if h : τ' = τ then 0 else b ⟨τ', h⟩

def extL : Bsp τ m n →L[ℝ] (T → Fin m → Fin n → ℂ) :=
  LinearMap.toContinuousLinearMap
    { toFun := extF τ
      map_add' := fun b b' => by
        funext τ' i j
        by_cases h : τ' = τ <;> simp [extF, h]
      map_smul' := fun r b => by
        funext τ' i j
        by_cases h : τ' = τ <;> simp [extF, h] }

def coordL (k : T × Fin m × Fin n) : Bsp τ m n →L[ℝ] ℂ :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℂ) k.2.2).comp
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => Fin n → ℂ) k.2.1).comp
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : T => Fin m → Fin n → ℂ) k.1).comp (extL τ)))

theorem tg_eval {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {σ : Type} (v : σ → E → ℂ)
    (hv : ∀ k, (v k).HasTemperateGrowth) (p : MvPolynomial σ ℂ) :
    (fun x => MvPolynomial.eval (fun k => v k x) p).HasTemperateGrowth := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    have := Function.HasTemperateGrowth.const (E := E) a
    convert this using 1
    all_goals first | rfl | (funext x; simp)
  | add p q hp hq =>
    have := hp.add hq
    convert this using 1
    all_goals first | rfl | (funext x; simp)
  | mul_X p k hp =>
    have := hp.mul (hv k)
    convert this using 1
    all_goals first | rfl | (funext x; simp)

def vC (k : T × Fin m × Fin n × Bool) (b : Bsp τ m n) : ℂ :=
  if k.2.2.2 then conj (coordL τ (k.1, k.2.1, k.2.2.1) b) else coordL τ (k.1, k.2.1, k.2.2.1) b

theorem tg_vC (k : T × Fin m × Fin n × Bool) : (vC (m := m) (n := n) τ k).HasTemperateGrowth := by
  by_cases hk : k.2.2.2 = true
  · have e : vC (m := m) (n := n) τ k = ⇑(Complex.conjCLE.toContinuousLinearMap.comp (coordL τ (k.1, k.2.1, k.2.2.1))) := by
      funext b
      simp [vC, hk]
    rw [e]
    exact ContinuousLinearMap.hasTemperateGrowth _
  · have e : vC (m := m) (n := n) τ k = ⇑(coordL τ (k.1, k.2.1, k.2.2.1)) := by
      funext b
      simp [vC, hk]
    rw [e]
    exact ContinuousLinearMap.hasTemperateGrowth _

theorem tg_poly (p : MvPolynomial (T × Fin m × Fin n × Bool) ℂ) :
    (fun b : Bsp τ m n => MvPolynomial.eval (fun k => vC τ k b) p).HasTemperateGrowth :=
  tg_eval _ (tg_vC τ) p

variable (fr : Matrix (Fin m) (Fin m) ℂ)


end

end PositivityTheory.Rg.Sw.Glob.AwayPf
