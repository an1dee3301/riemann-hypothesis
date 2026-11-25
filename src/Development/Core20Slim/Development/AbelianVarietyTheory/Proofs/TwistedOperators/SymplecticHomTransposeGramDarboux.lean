module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsReading
public import Batteries.Logic
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.LinearMap
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Finsupp.SMul
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import Mathlib.LinearAlgebra.SesquilinearForm.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.RingTheory.Trace.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DarbouxSymp

variable {D : D7}

theorem cA_incA_eq (a : D.host.E) : cA D (incA D a) = incA D (star a) := by
  simp only [cA, sigR, incA, inclR]
  simp
  rfl

theorem gram_star_eq (V : HSp D) (i j) : star (V.gram i j) = V.gram j i :=
  V.herm.eq (V.frame i) (V.frame j)

theorem gram_det_ne_zero (V : HSp D) : V.gram.det ≠ 0 := by
  intro h
  obtain ⟨v, hv, h0⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h
  apply hv
  have : V.frame.equivFun.symm v = 0 := by
    apply V.nondeg.2
    intro x
    have hx : x = ∑ i, V.frame.repr x i • V.frame i := (V.frame.sum_repr x).symm
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hx, map_sum, LinearMap.sum_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    have h1 : ∑ j, V.gram i j * v j = 0 := congr_fun h0 i
    have h2 : V.hT (V.frame i) (V.frame.equivFun.symm v) = ∑ j, V.gram i j * v j := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [Module.Basis.equivFun_symm_apply, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_smul, smul_eq_mul, mul_comm]; rfl
    rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, h2, h1, smul_zero]
  exact V.frame.equivFun.symm.injective (this.trans (map_zero _).symm)

theorem gram_map_mul_inv (V : HSp D) :
    HMul.hMul (V.gram.map (incA D) : Matrix (Fin V.rank) (Fin V.rank) (AE D)) (V.gram⁻¹.map (incA D) : Matrix (Fin V.rank) (Fin V.rank) (AE D)) = 1 := by
  rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 (gram_det_ne_zero V))]
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem hO_rearr (S T : HSp D) (X Y : WO S T) : hO S T X Y =
    ∑ b, ∑ c, ∑ d, cA D (Y c b) * incA D (T.gram c d) * ∑ a, X d a * incA D (S.gram⁻¹ a b) := by
  unfold hO
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  ring

theorem hO_darboux (S T S' T' : HSp D) (e₁ : Fin T'.rank ≃ Fin S.rank) (e₂ : Fin S'.rank ≃ Fin T.rank)
    (hT' : T'.gramᵀ = -(S.gram.submatrix e₁ e₁)) (hS' : S'.gram⁻¹ = -(T.gramᵀ.submatrix e₂ e₂)) (x y : WO S' T') :
    hO S T (HMul.hMul (xᵀ.submatrix e₂.symm e₁.symm) (S.gram.map (incA D)) : Matrix (Fin T.rank) (Fin S.rank) (AE D))
      (HMul.hMul (yᵀ.submatrix e₂.symm e₁.symm) (S.gram.map (incA D)) : Matrix (Fin T.rank) (Fin S.rank) (AE D)) =
    hO S' T' x y := by
  have L1 : ∀ d b, ∑ a, (HMul.hMul (xᵀ.submatrix e₂.symm e₁.symm) (S.gram.map (incA D)) : Matrix (Fin T.rank) (Fin S.rank) (AE D)) d a
      * incA D (S.gram⁻¹ a b) = x (e₁.symm b) (e₂.symm d) := by
    intro d b
    have h := congrFun (congrFun (show HMul.hMul (HMul.hMul (xᵀ.submatrix e₂.symm e₁.symm : Matrix (Fin T.rank) (Fin S.rank) (AE D))
      (S.gram.map (incA D) : Matrix (Fin S.rank) (Fin S.rank) (AE D))) (S.gram⁻¹.map (incA D) : Matrix (Fin S.rank) (Fin S.rank) (AE D))
      = (xᵀ.submatrix e₂.symm e₁.symm : Matrix (Fin T.rank) (Fin S.rank) (AE D)) by
        rw [Matrix.mul_assoc, gram_map_mul_inv, Matrix.mul_one]) d) b
    rw [Matrix.mul_apply] at h
    simpa using h
  have L2 : ∀ c b, cA D ((HMul.hMul (yᵀ.submatrix e₂.symm e₁.symm) (S.gram.map (incA D)) : Matrix (Fin T.rank) (Fin S.rank) (AE D)) c b)
      = ∑ k, cA D (y (e₁.symm k) (e₂.symm c)) * incA D (S.gram b k) := by
    intro c b
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Matrix.mul_apply, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, Matrix.map_apply, cA_incA_eq, gram_star_eq]
    rfl
  have E1 : ∀ a b, S'.gram⁻¹ a b = -T.gram (e₂ b) (e₂ a) := fun a b => by
    rw [hS']; rfl
  have E2 : ∀ c d, T'.gram c d = -S.gram (e₁ d) (e₁ c) := fun c d => by
    have := congrFun (congrFun hT' d) c
    simpa using this
  rw [hO_rearr]
  simp_rw [L1, L2]
  unfold hO
  simp_rw [E1, E2]
  have hR : ∀ F : Fin S.rank → Fin T.rank → Fin T.rank → Fin S.rank → AE D,
      (∀ a b c d, incA D (-T.gram (e₂ b) (e₂ a)) * cA D (y c b) * incA D (-S.gram (e₁ d) (e₁ c)) * x d a
        = F (e₁ d) (e₂ b) (e₂ a) (e₁ c)) →
      ∑ a, ∑ b, ∑ c, ∑ d, incA D (-T.gram (e₂ b) (e₂ a)) * cA D (y c b) * incA D (-S.gram (e₁ d) (e₁ c)) * x d a
        = ∑ d, ∑ c, ∑ k, ∑ b, F b c d k := by
    intro F hF
    refine Fintype.sum_equiv e₂ _ _ fun a => ?_
    refine Fintype.sum_equiv e₂ _ _ fun b => ?_
    refine Fintype.sum_equiv e₁ _ _ fun c => ?_
    refine Fintype.sum_equiv e₁ _ _ fun d => ?_
    exact hF a b c d
  rw [hR (fun b c d k => cA D (y (e₁.symm k) (e₂.symm c)) * incA D (S.gram b k) * incA D (T.gram c d) * x (e₁.symm b) (e₂.symm d))
    (fun a b c d => by simp only [Equiv.symm_apply_apply, map_neg]; ring)]
  simp only [Finset.sum_mul]
  conv_lhs => rw [Finset.sum_comm]
  conv_lhs => enter [2, c]; rw [Finset.sum_comm]
  conv_lhs => enter [2, c, 2, d]; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]

theorem symplO_darboux : ∀ (D : D7) (S T S' T' : HSp D) (e₁ : Fin T'.rank ≃ Fin S.rank) (e₂ : Fin S'.rank ≃ Fin T.rank),
    T'.gramᵀ = -(S.gram.submatrix e₁ e₁) → S'.gram⁻¹ = -(T.gramᵀ.submatrix e₂ e₂) → ∀ x y : WO S' T',
      symplO S T (HMul.hMul (xᵀ.submatrix e₂.symm e₁.symm) (S.gram.map (incA D)) : Matrix (Fin T.rank) (Fin S.rank) (AE D))
        (HMul.hMul (yᵀ.submatrix e₂.symm e₁.symm) (S.gram.map (incA D)) : Matrix (Fin T.rank) (Fin S.rank) (AE D)) =
      symplO S' T' x y := by
  intro D S T S' T' e₁ e₂ hT' hS' x y
  unfold symplO
  rw [hO_darboux S T S' T' e₁ e₂ hT' hS' x y]

end GlobalTheory.DarbouxSymp
