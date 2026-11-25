module

public import Mathlib
public import Development.Core20Slim.GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.SecondCountableTopologyArchUnitary
public import Development.Core20Slim.GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.MajorantInvolutionDiagonalForm
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Int.Order
public import Init.Data.Nat.Div.Basic
public import Init.Data.Nat.Dvd
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.BigOperators.GroupWithZero.Action
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.BigOperators
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Ring.Cast
public import Mathlib.Algebra.Order.Ring.Int
public import Mathlib.Algebra.Quotient
public import Mathlib.Algebra.Ring.Action.Rat
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Finsupp.SMul
public import Mathlib.Data.Finsupp.SMulWithZero
public import Mathlib.Data.Finsupp.Single
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Int.Cast.Lemmas
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Cast.Order.Basic
public import Mathlib.Data.Rat.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.GroupTheory.Index
public import Mathlib.LinearAlgebra.Alternating.Basic
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient
public import Mathlib.LinearAlgebra.LinearIndependent.Basic
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.LinearAlgebra.Matrix.Basis
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import Mathlib.LinearAlgebra.Quotient.Defs
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Hom.Basic
public import Mathlib.Order.Lattice
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.SetTheory.Cardinal.Finite

@[expose] public section

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField Module Matrix

theorem IndexLeDet.proof (E : Type*) [Field E] [NumberField E] : IndexLeDet.Statement E := by
  classical
  intro A hA e a T ha hT
  have hmem : ∀ i, (a i : E) ∈ A := fun i => hA ⟨a i, rfl⟩
  let b : Fin (finrank ℚ E) → A := fun i => ⟨a i, hmem i⟩
  have hb : ∀ i, b i = ∑ j, T i j • e j := by
    intro i
    apply Subtype.ext
    simp [b, hT i]

  have hdet : T.det ≠ 0 := by
    intro h0
    have h0' : ((Int.castRingHom ℚ).mapMatrix T).det = 0 := by
      rw [← RingHom.map_det, h0, map_zero]
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr h0'
    have hsum : ∑ i, v i • (a i : E) = 0 := by
      calc ∑ i, v i • (a i : E)
          = ∑ i, ∑ j, (v i * (T i j : ℚ)) • (e j : E) := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [hT i, Finset.smul_sum]
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [← Int.cast_smul_eq_zsmul ℚ, smul_smul]
        _ = ∑ j, (∑ i, v i * (T i j : ℚ)) • (e j : E) := by
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [Finset.sum_smul]
        _ = 0 := by
            refine Finset.sum_eq_zero fun j _ => ?_
            have := congrFun hv j
            simp only [vecMul, dotProduct, RingHom.mapMatrix_apply, map_apply, eq_intCast,
              Pi.zero_apply] at this
            rw [this, zero_smul]
    exact hv0 (funext fun i => Fintype.linearIndependent_iff.mp ha v hsum i)

  have hliE : LinearIndependent ℤ (fun i => (a i : E)) := ha.restrict_scalars' ℤ
  have hli : LinearIndependent ℤ b :=
    LinearIndependent.of_comp (A.subtype.toIntLinearMap) hliE
  have : Module.Free ℤ A := Module.Free.of_basis e
  have : Module.Finite ℤ A := Module.Finite.of_basis e
  set N := Submodule.span ℤ (Set.range b) with hN
  let bN := Basis.span hli
  have hbN : ((↑) ∘ bN : Fin (finrank ℚ E) → A) = b := funext fun i => congrArg Subtype.val (Basis.span_apply hli i)
  have hcard := Submodule.natAbs_det_basis_change e N bN
  rw [hbN] at hcard
  have hdetb : e.det b = T.det := by
    rw [Basis.det_apply, ← Matrix.det_transpose]
    congr 1
    ext i j
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Matrix.transpose_apply, Basis.toMatrix_apply, hb i, map_sum]
    simp [Finsupp.single_apply]
  rw [hdetb] at hcard

  have hle : N.toAddSubgroup ≤ (intSubgroup E).addSubgroupOf A := by
    have : N ≤ ((intSubgroup E).addSubgroupOf A).toIntSubmodule := by
      rw [hN, Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      show b i ∈ (intSubgroup E).addSubgroupOf A
      rw [AddSubgroup.mem_addSubgroupOf]
      exact ⟨a i, rfl⟩
    exact this
  have hidx : N.toAddSubgroup.index = T.det.natAbs := hcard.symm
  have hdvd := AddSubgroup.index_dvd_of_le hle
  rw [hidx] at hdvd
  have hle' : (intSubgroup E).relIndex A ≤ T.det.natAbs :=
    Nat.le_of_dvd (Int.natAbs_pos.mpr hdet) hdvd
  calc ((intSubgroup E).relIndex A : ℝ) ≤ (T.det.natAbs : ℝ) := by exact_mod_cast hle'
    _ = |(T.det : ℝ)| := by rw [Nat.cast_natAbs, Int.cast_abs]

end GroundTheory.Heights₂.Heights.FiniteCovolume
