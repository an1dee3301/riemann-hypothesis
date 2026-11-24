module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NonemptyInvFunEquiv
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DualIsoDetGenMNeZero
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PosOkId
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.FiniteIntertwining
public import Formalism.GradedWeylDivisibility.StatementA
public import Formalism.LocalRingCardinality.DataCoeff
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Fin.Basic
public import Init.Data.Fin.Lemmas
public import Init.Data.Function
public import Init.Data.Int.Basic
public import Init.Data.Int.Lemmas
public import Init.Data.Int.LemmasAux
public import Init.Data.Int.Order
public import Init.Data.Nat.Basic
public import Init.Data.NeZero
public import Init.Data.Zero
public import Init.Omega.Coeffs
public import Init.Omega.Constraint
public import Init.Omega.Int
public import Init.Omega.LinearCombo
public import Init.Omega.Logic
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Equiv
public import Mathlib.Algebra.Module.Submodule.LinearMap
public import Mathlib.Algebra.Module.Submodule.Map
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MonoidAlgebra.Module
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Order.Group.Int
public import Mathlib.Algebra.Order.Group.Unbundled.Basic
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.Logic.Function.Defs
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Fin.Basic
public import Mathlib.Order.Monotone.Defs
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal

@[expose] public section

open MvPolynomial GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries GlobalTheory.OneFunctional Formalism.BasicNotions GlobalTheory.Branching
open scoped TensorProduct DirectSum

namespace GlobalTheory.OneFunctional

open GlobalTheory.ValCmp

theorem sqAct_eq_rnd_invTranspose (K : Type) [Field K] (n : ℕ) (lam : DomWeight n) (g : GL (Fin n) K) (f : MP K n) :
    sqAct K n lam g f = rnd K lam.detShift ((g : Matrix (Fin n) (Fin n) K)⁻¹).transpose f := by
  have hdet : IsUnit (g : Matrix (Fin n) (Fin n) K).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit g)
  have hinv : (((g : Matrix (Fin n) (Fin n) K)⁻¹).transpose)⁻¹ = (g : Matrix (Fin n) (Fin n) K).transpose := by
    rw [← Matrix.transpose_nonsing_inv, Matrix.nonsing_inv_nonsing_inv _ hdet]
  have hpow : (((g : Matrix (Fin n) (Fin n) K)⁻¹).transpose).det ^ (-lam.detShift) =
      (g : Matrix (Fin n) (Fin n) K).det ^ lam.detShift := by
    rw [Matrix.det_transpose, Matrix.det_nonsing_inv, Ring.inverse_eq_inv', inv_zpow', neg_neg]
  simp only [GlobalTheory.ValCmp.rnd, LinearMap.smul_apply, AlgHom.toLinearMap_apply, hinv, hpow, sqAct, detPow,
    Units.val_zpow_eq_zpow_val, Matrix.GeneralLinearGroup.val_det_apply]

private lemma detShift_eq_w_last {m : ℕ} (lam : DomWeight (m + 1)) : lam.detShift = lam.w (Fin.last m) := by
  unfold DomWeight.detShift
  rw [dite_eq_left (Nat.succ_pos m)]
  rfl

private lemma natW_antitone_succ {m : ℕ} (lam : DomWeight (m + 1)) : Antitone lam.natW := by
  intro i j hij
  unfold DomWeight.natW
  exact Int.toNat_le_toNat (sub_le_sub_right (lam.anti hij) _)

private lemma natW_last_eq_zero {m : ℕ} (lam : DomWeight (m + 1)) : lam.natW (Fin.last m) = 0 := by
  unfold DomWeight.natW
  rw [detShift_eq_w_last, sub_self, Int.toNat_zero]

private lemma dual_detShift_eq_neg_w_zero {m : ℕ} (lam : DomWeight (m + 1)) : lam.dual.detShift = -lam.w 0 := by
  rw [detShift_eq_w_last]
  show -lam.w (Fin.rev (Fin.last m)) = -lam.w 0
  rw [Fin.rev_last]

private lemma natW_dual_eq_nuDual {m : ℕ} (lam : DomWeight (m + 1)) :
    lam.dual.natW = GlobalTheory.ValCmp.nuDual lam.natW := by
  funext i
  have h0 : lam.w (Fin.rev i) ≤ lam.w 0 := lam.anti (Fin.zero_le _)
  have h1 : lam.w (Fin.last m) ≤ lam.w (Fin.rev i) := lam.anti (Fin.le_last _)
  have h2 : lam.dual.w i = -lam.w (Fin.rev i) := rfl
  show (lam.dual.w i - lam.dual.detShift).toNat =
    (lam.w 0 - lam.detShift).toNat - (lam.w (Fin.rev i) - lam.detShift).toNat
  rw [dual_detShift_eq_neg_w_zero, h2, detShift_eq_w_last]
  omega

private lemma neg_detShift_add_natW_zero_eq_dual_detShift {m : ℕ} (lam : DomWeight (m + 1)) :
    -(lam.detShift + ((lam.natW 0 : ℕ) : ℤ) + 0) = lam.dual.detShift := by
  have h0 : lam.w (Fin.last m) ≤ lam.w 0 := lam.anti (Fin.zero_le _)
  rw [dual_detShift_eq_neg_w_zero, detShift_eq_w_last]
  simp only [DomWeight.natW, detShift_eq_w_last]
  omega

theorem iso_irr_comp_conjU : ∀ (n : ℕ), 0 < n → ∀ lam : DomWeight n,
    Iso ((irr n lam).comp (conjU n) : Representation ℂ (U n) (nablaSq ℂ n lam)) (irr n lam.dual) := by
  intro n hn lam
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨Ψ, hinj, hmap, hact, -, -⟩ := GlobalTheory.ValCmp.exists_posOk_dual ℂ ℂ m lam.natW
    (natW_antitone_succ lam) (natW_last_eq_zero lam) lam.detShift 0
  have hmem : ∀ f : nablaSq ℂ (m + 1) lam, Ψ f ∈ nablaSq ℂ (m + 1) lam.dual := by
    intro f
    change Ψ f ∈ Formalism.GradedWeylDivisibility.dualWeyl ℂ (m + 1) (m + 1) lam.dual.natW
    rw [natW_dual_eq_nuDual, ← hmap]
    exact Submodule.mem_map_of_mem f.2
  let L : nablaSq ℂ (m + 1) lam →ₗ[ℂ] nablaSq ℂ (m + 1) lam.dual :=
    (Ψ ∘ₗ (nablaSq ℂ (m + 1) lam).subtype).codRestrict _ hmem
  have hL : Function.Bijective L := by
    constructor
    · intro f f' h
      have h1 : Ψ ((f : MP ℂ (m + 1)) - f') = 0 := by
        rw [map_sub, sub_eq_zero]
        exact congrArg Subtype.val h
      exact Subtype.ext (sub_eq_zero.mp (hinj _ (Submodule.sub_mem _ f.2 f'.2) h1))
    · rintro ⟨y, hy⟩
      have hy' : y ∈ (Formalism.GradedWeylDivisibility.dualWeyl ℂ (m + 1) (m + 1) lam.natW).map Ψ := by
        rw [hmap, ← natW_dual_eq_nuDual]
        exact hy
      obtain ⟨x, hx, hxy⟩ := Submodule.mem_map.mp hy'
      exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  refine ⟨LinearEquiv.ofBijective L hL, fun g x => Subtype.ext ?_⟩
  have hu : IsUnit (g : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ).det := by
    have hdet := congrArg Matrix.det (Matrix.mem_unitaryGroup_iff.mp g.2)
    rw [Matrix.det_mul, Matrix.det_one] at hdet
    exact isUnit_iff_exists_inv.mpr ⟨_, hdet⟩
  have hg : ((((star (g : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)).transpose)⁻¹).transpose) =
      (g : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) := by
    rw [Matrix.transpose_nonsing_inv, Matrix.transpose_transpose]
    exact Matrix.inv_eq_left_inv (Matrix.mem_unitaryGroup_iff.mp g.2)
  change Ψ (sqAct ℂ (m + 1) lam (unitaryIncl (m + 1) (conjU (m + 1) g)) (x : MP ℂ (m + 1))) =
    sqAct ℂ (m + 1) lam.dual (unitaryIncl (m + 1) g) (Ψ x)
  rw [sqAct_eq_rnd_invTranspose, sqAct_eq_rnd_invTranspose]
  simp only [GlobalTheory.Branching.unitaryIncl_coe, conjU_coe]
  rw [hg, hact _ hu _ x.2, zpow_zero, one_smul, neg_detShift_add_natW_zero_eq_dual_detShift]

end GlobalTheory.OneFunctional
