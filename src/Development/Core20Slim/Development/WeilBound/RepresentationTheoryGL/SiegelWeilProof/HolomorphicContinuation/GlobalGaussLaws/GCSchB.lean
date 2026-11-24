module

public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GCSchA
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Algebra.Star.Pi
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.Real.Star
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.LinearAlgebra.Complex.Module
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.ConstMulAction
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.UniformMulAction
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.MetricSpace.Algebra
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.UniformSpace.Defs
public import Mathlib.Topology.UniformSpace.Real

@[expose] public section

noncomputable section

open scoped Matrix ComplexOrder
open Matrix

namespace PositivityTheory.Rg.Sw.Glob.GCSchH

variable {m n : ℕ}

def qF (S S' : Finset (Fin m)) (c : ℝ) (Z Z' : Matrix (Fin n) (Fin n) ℂ) (u v : Fin m → Fin n → ℂ) : ℂ :=
  -(Complex.I * c * ∑ a ∈ S, star (u a) ⬝ᵥ (Zᵀ *ᵥ v a) - Complex.I * c * ∑ a ∈ S', star (u a) ⬝ᵥ (Z'ᵀ *ᵥ v a))

def qL (S S' : Finset (Fin m)) (c : ℝ) (Z Z' : Matrix (Fin n) (Fin n) ℂ) :
    (Fin m → Fin n → ℂ) →ₗ[ℝ] (Fin m → Fin n → ℂ) →ₗ[ℝ] ℂ :=
  LinearMap.mk₂ ℝ (qF S S' c Z Z')
    (fun u₁ u₂ v => by
      simp only [qF, Pi.add_apply, star_add, add_dotProduct, Finset.sum_add_distrib]; ring)
    (fun r u v => by
      simp only [qF, Pi.smul_apply, star_smul, star_trivial, smul_dotProduct, Complex.real_smul, ← Finset.mul_sum]
      ring)
    (fun u v₁ v₂ => by
      simp only [qF, Pi.add_apply, Matrix.mulVec_add, dotProduct_add, Finset.sum_add_distrib]; ring)
    (fun r u v => by
      simp only [qF, Pi.smul_apply, Matrix.mulVec_smul, dotProduct_smul, Complex.real_smul, ← Finset.mul_sum]
      ring)

def qB (S S' : Finset (Fin m)) (c : ℝ) (Z Z' : Matrix (Fin n) (Fin n) ℂ) :
    (Fin m → Fin n → ℂ) →L[ℝ] (Fin m → Fin n → ℂ) →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap : ((Fin m → Fin n → ℂ) →ₗ[ℝ] ℂ) ≃ₗ[ℝ] _).toLinearMap ∘ₗ qL S S' c Z Z')

theorem qB_apply (S S' : Finset (Fin m)) (c : ℝ) (Z Z' : Matrix (Fin n) (Fin n) ℂ) (u v : Fin m → Fin n → ℂ) :
    qB S S' c Z Z' u v = qF S S' c Z Z' u v := rfl

theorem re_I_mul (c : ℝ) (z : ℂ) : (Complex.I * c * z).re = -(c * z.im) := by
  simp [Complex.mul_re, Complex.mul_im]

theorem quad_nonneg {P : Matrix (Fin n) (Fin n) ℂ} (hP : P.PosDef) (y : Fin n → ℂ) : 0 ≤ (star y ⬝ᵥ (P *ᵥ y)).re := (Complex.nonneg_iff.mp (hP.posSemidef.dotProduct_mulVec_nonneg y)).1

theorem quad_pos {P : Matrix (Fin n) (Fin n) ℂ} (hP : P.PosDef) {y : Fin n → ℂ} (hy : y ≠ 0) :
    0 < (star y ⬝ᵥ (P *ᵥ y)).re := (Complex.pos_iff.mp (hP.dotProduct_mulVec_pos hy)).1

end PositivityTheory.Rg.Sw.Glob.GCSchH
