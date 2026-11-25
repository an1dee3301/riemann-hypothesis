module

public import Mathlib
public import Development.Core20Slim.GroundTheory.AutomorphicForms.RealGroupsPolar
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Function
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.IsSimpleRing
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Invertible.Basic
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.GroupWithZero.Units.Lemmas
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.Matrix.LDL
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.RCLike.Lemmas
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.FieldTheory.Perfect
public import Mathlib.FieldTheory.Separable
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Order.Lattice
public import Mathlib.Order.OrderDual
public import Mathlib.Order.RelClasses
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal

@[expose] public section

namespace GroundTheory.Automorphic

open Matrix
open scoped ComplexOrder

set_option linter.unusedSectionVars false

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [LinearOrder n]


theorem isUpperTriangular_conjTranspose_iff {A : Matrix n n 𝕜} :
    Aᴴ.IsUpperTriangular ↔ A.IsLowerTriangular := by
  constructor
  · intro h i j hij
    have := h (i := j) (j := i) (OrderDual.toDual_lt_toDual.1 hij)
    simpa [conjTranspose_apply] using this
  · intro h i j hij
    have := h (show OrderDual.toDual i < OrderDual.toDual j from hij)
    simp [conjTranspose_apply, this]


section Existence

variable [WellFoundedLT n] [LocallyFiniteOrderBot n]

theorem exists_isUpperTriangular_conjTranspose_mul_self {S : Matrix n n 𝕜} (hS : S.PosDef) :
    ∃ R : Matrix n n 𝕜, R.IsUpperTriangular ∧ Rᴴ * R = S := by
  have hLi : (LDL.lowerInv hS).IsLowerTriangular := LDL.isLowerTriangular_lowerInv hS
  have hL : (LDL.lower hS).IsLowerTriangular := blockTriangular_inv_of_blockTriangular hLi
  have hD : (LDL.diag hS).PosDef := by
    rw [LDL.diag_eq_lowerInv_conj]
    exact hS.mul_mul_conjTranspose_same
      (vecMul_injective_iff_isUnit.2 (isUnit_of_invertible (LDL.lowerInv hS)))
  have hpos : ∀ i, 0 < LDL.diagEntries hS i := fun i => by
    simpa [LDL.diag] using hD.diag_pos (i := i)
  set d : n → ℝ := fun i => RCLike.re (LDL.diagEntries hS i)
  have hd : ∀ i, LDL.diagEntries hS i = (d i : 𝕜) := fun i => by
    obtain ⟨_, him⟩ := RCLike.pos_iff.1 (hpos i)
    rw [← RCLike.re_add_im (LDL.diagEntries hS i), him]; simp [d]
  have hd0 : ∀ i, 0 ≤ d i := fun i => (RCLike.pos_iff.1 (hpos i)).1.le
  refine ⟨diagonal (fun i => (Real.sqrt (d i) : 𝕜)) * (LDL.lower hS)ᴴ,
    (blockTriangular_diagonal _).mul (isUpperTriangular_conjTranspose_iff.2 hL), ?_⟩
  have hsq : (diagonal (fun i => (Real.sqrt (d i) : 𝕜)))ᴴ * diagonal (fun i => (Real.sqrt (d i) : 𝕜))
      = LDL.diag hS := by
    rw [diagonal_conjTranspose, diagonal_mul_diagonal, LDL.diag]
    congr 1; funext i
    rw [hd i, Pi.star_apply, RCLike.star_def, RCLike.conj_ofReal, ← RCLike.ofReal_mul,
      Real.mul_self_sqrt (hd0 i)]
  rw [conjTranspose_mul, conjTranspose_conjTranspose]
  calc LDL.lower hS * (diagonal fun i => (Real.sqrt (d i) : 𝕜))ᴴ *
        (diagonal (fun i => (Real.sqrt (d i) : 𝕜)) * (LDL.lower hS)ᴴ)
      = LDL.lower hS * ((diagonal fun i => (Real.sqrt (d i) : 𝕜))ᴴ *
        diagonal (fun i => (Real.sqrt (d i) : 𝕜))) * (LDL.lower hS)ᴴ := by
        simp only [Matrix.mul_assoc]
    _ = S := by rw [hsq, LDL.lower_conj_diag]

end Existence

section Existence2

variable [WellFoundedLT n] [LocallyFiniteOrderBot n]

theorem star_mul_self_norm_div {x : 𝕜} (hx : x ≠ 0) :
    star ((‖x‖ : 𝕜) / x) * ((‖x‖ : 𝕜) / x) = 1 := by
  rw [star_div₀, RCLike.star_def, RCLike.conj_ofReal, div_mul_div_comm, RCLike.conj_mul, ← sq]
  exact div_self (pow_ne_zero 2 (by simpa using hx))

theorem exists_cholesky {S : Matrix n n 𝕜} (hS : S.PosDef) :
    ∃ B : Matrix n n 𝕜, ∃ a : n → ℝ, B.IsUpperTriangular ∧ (∀ i, 0 < a i) ∧
      (∀ i, B i i = a i) ∧ Bᴴ * B = S := by
  obtain ⟨R, hR, hRS⟩ := exists_isUpperTriangular_conjTranspose_mul_self hS
  have hdet : S.det ≠ 0 := (isUnit_iff_isUnit_det S).1 hS.isUnit |>.ne_zero
  have hRi : ∀ i, R i i ≠ 0 := by
    have : R.det ≠ 0 := by
      intro h; apply hdet; rw [← hRS, det_mul, h, mul_zero]
    rw [det_of_isUpperTriangular hR] at this
    exact fun i => Finset.prod_ne_zero_iff.1 this i (Finset.mem_univ i)
  refine ⟨diagonal (fun i => (‖R i i‖ : 𝕜) / R i i) * R, fun i => ‖R i i‖,
    (blockTriangular_diagonal _).mul hR, fun i => norm_pos_iff.2 (hRi i), fun i => ?_, ?_⟩
  · rw [diagonal_mul, div_mul_cancel₀ _ (hRi i)]
  · rw [conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (diagonal _)ᴴ,
      diagonal_conjTranspose, diagonal_mul_diagonal]
    have : (fun i => (star (fun i => (‖R i i‖ : 𝕜) / R i i)) i * ((‖R i i‖ : 𝕜) / R i i)) =
        fun _ => 1 := funext fun i => star_mul_self_norm_div (hRi i)
    rw [this, diagonal_one, Matrix.one_mul, hRS]

theorem exists_KAN (g : GL n 𝕜) :
    ∃ k : unitaryGroup n 𝕜, ∃ a : n → ℝ, (∀ i, 0 < a i) ∧ ∃ u : Matrix n n 𝕜,
      u.IsUpperTriangular ∧ (∀ i, u i i = 1) ∧
        (g : Matrix n n 𝕜) = (k : Matrix n n 𝕜) * diagonal (fun i => (a i : 𝕜)) * u := by
  obtain ⟨B, a, hB, ha, hBd, hBS⟩ := exists_cholesky (posDef_conjTranspose_mul_self_GL g)
  have hBdet : IsUnit B.det := by
    rw [det_of_isUpperTriangular hB]
    exact IsUnit.mk0 _ (Finset.prod_ne_zero_iff.2 fun i _ => by
      rw [hBd i]; exact_mod_cast (ha i).ne')
  have hau : diagonal (fun i => (a i : 𝕜)) * (diagonal (fun i => ((a i : 𝕜))⁻¹) * B) = B := by
    rw [← Matrix.mul_assoc, diagonal_mul_diagonal]
    have : (fun i => (a i : 𝕜) * (a i : 𝕜)⁻¹) = fun _ => 1 :=
      funext fun i => mul_inv_cancel₀ (by exact_mod_cast (ha i).ne')
    rw [this, diagonal_one, Matrix.one_mul]
  have hk : (g : Matrix n n 𝕜) * B⁻¹ ∈ unitaryGroup n 𝕜 := by
    rw [mem_unitaryGroup_iff', star_eq_conjTranspose, conjTranspose_mul,
      conjTranspose_nonsing_inv]
    calc Bᴴ⁻¹ * (g : Matrix n n 𝕜)ᴴ * ((g : Matrix n n 𝕜) * B⁻¹)
        = Bᴴ⁻¹ * ((g : Matrix n n 𝕜)ᴴ * g) * B⁻¹ := by simp only [Matrix.mul_assoc]
      _ = Bᴴ⁻¹ * Bᴴ * (B * B⁻¹) := by rw [← hBS]; simp only [Matrix.mul_assoc]
      _ = 1 := by
        rw [Matrix.nonsing_inv_mul _ (by rw [det_conjTranspose]; exact hBdet.star),
          Matrix.mul_nonsing_inv _ hBdet, Matrix.one_mul]
  refine ⟨⟨_, hk⟩, a, ha, diagonal (fun i => ((a i : 𝕜))⁻¹) * B,
    (blockTriangular_diagonal _).mul hB, fun i => ?_, ?_⟩
  · rw [diagonal_mul, hBd i, inv_mul_cancel₀ (by exact_mod_cast (ha i).ne')]
  · rw [Matrix.mul_assoc, hau]
    show (g : Matrix n n 𝕜) = (g : Matrix n n 𝕜) * B⁻¹ * B
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hBdet, Matrix.mul_one]

end Existence2

section Uniqueness

theorem isUnit_det_diagonal_mul_of_unitriangular {a : n → ℝ} (ha : ∀ i, 0 < a i)
    {u : Matrix n n 𝕜} (hu : u.IsUpperTriangular) (hu1 : ∀ i, u i i = 1) :
    IsUnit (diagonal (fun i => (a i : 𝕜)) * u).det := by
  rw [det_of_isUpperTriangular ((blockTriangular_diagonal _).mul hu)]
  exact IsUnit.mk0 _ (Finset.prod_ne_zero_iff.2 fun i _ => by
    rw [diagonal_mul, hu1, mul_one]; exact_mod_cast (ha i).ne')


end Uniqueness

section Homeomorph

open scoped Matrix.Norms.L2Operator Topology
open Filter Set

variable [WellFoundedLT n] [LocallyFiniteOrderBot n]


variable (n) in
abbrev PosDiag := {a : n → ℝ // ∀ i, 0 < a i}

abbrev UpperUnitriangular (n 𝕜 : Type*) [RCLike 𝕜] [LinearOrder n] :=
  {u : Matrix n n 𝕜 // u.IsUpperTriangular ∧ ∀ i, u i i = 1}

theorem isUnit_det_iwasawa (x : unitaryGroup n 𝕜 × PosDiag (n := n) × UpperUnitriangular n 𝕜) :
    IsUnit ((x.1 : Matrix n n 𝕜) * diagonal (fun i => (x.2.1.1 i : 𝕜)) * x.2.2.1).det := by
  rw [Matrix.mul_assoc, det_mul]
  exact (UnitaryGroup.det_isUnit x.1).mul
    (isUnit_det_diagonal_mul_of_unitriangular x.2.1.2 x.2.2.2.1 x.2.2.2.2)

noncomputable def iwasawaMul (x : unitaryGroup n 𝕜 × PosDiag (n := n) × UpperUnitriangular n 𝕜) :
    GL n 𝕜 :=
  ⟨(x.1 : Matrix n n 𝕜) * diagonal (fun i => (x.2.1.1 i : 𝕜)) * x.2.2.1,
    ((x.1 : Matrix n n 𝕜) * diagonal (fun i => (x.2.1.1 i : 𝕜)) * x.2.2.1)⁻¹,
    mul_nonsing_inv _ (isUnit_det_iwasawa x), nonsing_inv_mul _ (isUnit_det_iwasawa x)⟩

@[simp] theorem coe_iwasawaMul (x : unitaryGroup n 𝕜 × PosDiag (n := n) × UpperUnitriangular n 𝕜) :
    ((iwasawaMul x : GL n 𝕜) : Matrix n n 𝕜) =
      (x.1 : Matrix n n 𝕜) * diagonal (fun i => (x.2.1.1 i : 𝕜)) * x.2.2.1 := rfl




theorem isCompact_unitaryGroup : IsCompact (unitaryGroup n 𝕜 : Set (Matrix n n 𝕜)) := by
  have : ProperSpace (Matrix n n 𝕜) := FiniteDimensional.proper 𝕜 _
  refine Metric.isCompact_of_isClosed_isBounded isClosed_unitary ?_
  refine (Metric.isBounded_iff_subset_closedBall (0 : Matrix n n 𝕜)).2 ⟨‖(1 : Matrix n n 𝕜)‖, ?_⟩
  intro U hU
  rw [Metric.mem_closedBall, dist_zero_right]
  have := CStarRing.norm_mem_unitary_mul (1 : Matrix n n 𝕜) hU
  rw [Matrix.mul_one] at this
  exact this.le

instance : CompactSpace (unitaryGroup n 𝕜) :=
  isCompact_iff_compactSpace.1 isCompact_unitaryGroup

end Homeomorph

section Homeomorph2

open scoped Matrix.Norms.L2Operator Topology
open Filter Set

variable [WellFoundedLT n] [LocallyFiniteOrderBot n]









end Homeomorph2

section Homeomorph3

open scoped Matrix.Norms.L2Operator Topology
open Filter Set

variable [WellFoundedLT n] [LocallyFiniteOrderBot n]

end Homeomorph3

end GroundTheory.Automorphic
