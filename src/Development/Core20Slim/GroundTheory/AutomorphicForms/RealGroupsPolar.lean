module

public import Mathlib
public import Development.Core20Slim.GroundTheory.AutomorphicForms.RealGroupsLie
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.StrictPositivity
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.IsField
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Algebra.Star.SelfAdjoint
public import Mathlib.Analysis.CStarAlgebra.Basic
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.NonUnital
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.Normed.Ring.Units
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Basic.Nontrivial.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.Real.Star
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.Algebra.Star.Real
public import Mathlib.Topology.ContinuousOn
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.MetricSpace.Defs
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Metrizable.Basic
public import Mathlib.Topology.Metrizable.Uniformity
public import Mathlib.Topology.UniformSpace.Defs
public import Mathlib.Topology.UniformSpace.Matrix

@[expose] public section

namespace GroundTheory.Automorphic

open Matrix
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

theorem continuousOn_matrix_inv :
    ContinuousOn (fun A : Matrix n n 𝕜 => A⁻¹) {A | IsUnit A} := by
  rintro _ ⟨u, rfl⟩
  have h := NormedRing.inverse_continuousAt u
  have he : (fun A : Matrix n n 𝕜 => A⁻¹) = Ring.inverse := funext nonsing_inv_eq_ringInverse
  rw [he]
  exact h.continuousWithinAt

theorem posDef_conjTranspose_mul_self_GL (g : GL n 𝕜) : ((g : Matrix n n 𝕜)ᴴ * g).PosDef :=
  PosDef.conjTranspose_mul_self _ (mulVec_injective_of_isUnit g.isUnit)

noncomputable def polarPos (g : GL n 𝕜) : Matrix n n 𝕜 := CFC.sqrt ((g : Matrix n n 𝕜)ᴴ * g)

theorem polarPos_posDef (g : GL n 𝕜) : (polarPos g).PosDef := by
  have h := posDef_conjTranspose_mul_self_GL g
  rw [← isStrictlyPositive_iff_posDef] at h ⊢
  exact IsStrictlyPositive.sqrt _ h

theorem polarPos_mul_self (g : GL n 𝕜) : polarPos g * polarPos g = (g : Matrix n n 𝕜)ᴴ * g :=
  CFC.sqrt_mul_sqrt_self _ ((posDef_conjTranspose_mul_self_GL g).posSemidef.nonneg)

noncomputable def polarUnitary (g : GL n 𝕜) : Matrix n n 𝕜 := (g : Matrix n n 𝕜) * (polarPos g)⁻¹

theorem isUnit_det_of_posDef {p : Matrix n n 𝕜} (hp : p.PosDef) : IsUnit p.det :=
  (isUnit_iff_isUnit_det p).1 hp.isUnit

theorem polarUnitary_mem (g : GL n 𝕜) : polarUnitary g ∈ unitaryGroup n 𝕜 := by
  rw [mem_unitaryGroup_iff']
  have hP : (polarPos g)ᴴ = polarPos g := (polarPos_posDef g).isHermitian
  have hd := isUnit_det_of_posDef (polarPos_posDef g)
  rw [star_eq_conjTranspose, polarUnitary, conjTranspose_mul, conjTranspose_nonsing_inv, hP]
  calc (polarPos g)⁻¹ * (g : Matrix n n 𝕜)ᴴ * ((g : Matrix n n 𝕜) * (polarPos g)⁻¹)
      = (polarPos g)⁻¹ * ((g : Matrix n n 𝕜)ᴴ * g) * (polarPos g)⁻¹ := by
        simp only [Matrix.mul_assoc]
    _ = (polarPos g)⁻¹ * (polarPos g * polarPos g) * (polarPos g)⁻¹ := by rw [polarPos_mul_self]
    _ = 1 := by
        rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hd, Matrix.one_mul,
          Matrix.mul_nonsing_inv _ hd]

theorem polarUnitary_mul_polarPos (g : GL n 𝕜) : polarUnitary g * polarPos g = g := by
  rw [polarUnitary, Matrix.mul_assoc,
    Matrix.nonsing_inv_mul _ (isUnit_det_of_posDef (polarPos_posDef g)), Matrix.mul_one]

theorem polar_unique {g : GL n 𝕜} {k p : Matrix n n 𝕜} (hk : k ∈ unitaryGroup n 𝕜)
    (hp : p.PosDef) (h : k * p = g) : polarPos g = p ∧ polarUnitary g = k := by
  have hkk : kᴴ * k = 1 := by rw [← star_eq_conjTranspose]; exact mem_unitaryGroup_iff'.1 hk
  have hP : pᴴ = p := hp.isHermitian
  have hpp : p * p = (g : Matrix n n 𝕜)ᴴ * g := by
    rw [← h, conjTranspose_mul, hP]
    calc p * p = p * (kᴴ * k) * p := by rw [hkk, Matrix.mul_one]
      _ = p * kᴴ * (k * p) := by simp only [Matrix.mul_assoc]
  have h1 : polarPos g = p := CFC.sqrt_unique hpp hp.posSemidef.nonneg
  refine ⟨h1, ?_⟩
  rw [polarUnitary, h1, ← h, Matrix.mul_assoc,
    Matrix.mul_nonsing_inv _ (isUnit_det_of_posDef hp), Matrix.mul_one]



theorem continuous_polarPos
    (hsqrt : ContinuousOn (CFC.sqrt : Matrix n n 𝕜 → Matrix n n 𝕜) {a | 0 ≤ a}) :
    Continuous (polarPos : GL n 𝕜 → Matrix n n 𝕜) :=
  hsqrt.comp_continuous
    ((Units.continuous_val.matrix_conjTranspose).mul Units.continuous_val)
    (fun g => (posDef_conjTranspose_mul_self_GL g).posSemidef.nonneg)




section ExpHermitianComplex





end ExpHermitianComplex

section ExpHermitianReal





end ExpHermitianReal

end GroundTheory.Automorphic
