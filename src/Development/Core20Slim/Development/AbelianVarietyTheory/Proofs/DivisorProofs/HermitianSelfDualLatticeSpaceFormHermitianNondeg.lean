module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramHspOf
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Formalism.FockGram.StatementHerm
public import Formalism.HermitianLattices.StatementLat
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.PropLemmas
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Module.Submodule.Map
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Basic
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Algebra.Star.BigOperators
public import Mathlib.Algebra.Star.Pi
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fin.SuccPred
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Block
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import Mathlib.LinearAlgebra.Matrix.Nondegenerate
public import Mathlib.LinearAlgebra.Matrix.SesquilinearForm
public import Mathlib.LinearAlgebra.SesquilinearForm.Basic
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
public import Mathlib.Order.SetNotation
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.WeilSchrodingerHerm

theorem sesq_apply (D : D7) {k : ℕ} (G : Matrix (Fin k) (Fin k) D.host.E) (x y : Fin k → D.host.E) :
    GlobalTheory.WeilSchrodinger.sesq D G x y = star x ⬝ᵥ (G *ᵥ y) := by
  simp only [GlobalTheory.WeilSchrodinger.sesq, Matrix.toLinearMapₛₗ₂'_apply, starRingEnd_apply, RingHom.id_apply,
    smul_eq_mul, dotProduct, Matrix.mulVec, Finset.mul_sum, Pi.star_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem sesq_transpose_eq_form (D : D7) {k : ℕ} (J : Matrix (Fin k) (Fin k) D.host.E) (x y : Fin k → D.host.E) :
    GlobalTheory.WeilSchrodinger.sesq D Jᵀ y x = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form D.sp.cm.sig J x y := by
  rw [sesq_apply, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, dotProduct_comm]
  rfl

theorem det_ne_zero_of_hasSig {n r s : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.HasSig M r s) :
    M.det ≠ 0 := by
  obtain ⟨hrs, A, hA⟩ := h
  let e : Fin r ⊕ Fin s ≃ Fin n := finSumFinEquiv.trans (finCongr hrs)
  let P : Matrix (Fin n) (Fin n) ℂ := A.submatrix id e.symm
  have key : Pᵀ * M * P.map star =
      (Matrix.fromBlocks 1 0 0 (-1) : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ).submatrix e.symm e.symm := by
    rw [← hA]
    rfl
  have hd := congrArg Matrix.det key
  rw [Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, Matrix.det_neg,
    Matrix.det_one, Matrix.det_mul, Matrix.det_mul] at hd
  intro h0
  rw [h0, mul_zero, zero_mul] at hd
  rw [Fintype.card_fin, one_mul, mul_one] at hd
  exact pow_ne_zero s (neg_ne_zero.mpr one_ne_zero) hd.symm

variable (D : D7) (B : Base D.host.F D.host.E) {n : ℕ} (X : Spc D.host.F D.host.E n) {r s : ℕ}

theorem det_J_ne_zero (hX : X.IsHerm D.sp.cm.sig B r s) : X.J.det ≠ 0 := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace D.host.F) := inferInstance
  have h := det_ne_zero_of_hasSig (hX.sig w)
  intro h0
  apply h
  have hm : (X.J.map (B.emb w).1).det = (B.emb w).1 X.J.det := (RingHom.map_det _ _).symm
  rw [hm, h0, map_zero]

theorem mem_one_iff (z : D.host.E) : z ∈ (1 : Submodule (𝓞 D.host.E) D.host.E) ↔ IsIntegral ℤ z := by
  rw [Submodule.mem_one]
  constructor
  · rintro ⟨o, rfl⟩
    exact o.isIntegral_coe
  · intro h
    exact ⟨⟨z, h⟩, rfl⟩

theorem herm_nondeg_unimod (hX : X.IsHerm D.sp.cm.sig B r s) :
    (GlobalTheory.WeilSchrodinger.sesq D X.Jᵀ).IsSymm ∧ (GlobalTheory.WeilSchrodinger.sesq D X.Jᵀ).Nondegenerate ∧
      Formalism.HermitianLatticesTheory.IsUnimodular (GlobalTheory.WeilSchrodinger.sesq D X.Jᵀ) X.L := by
  have hdet : X.Jᵀ.det ≠ 0 := by rw [Matrix.det_transpose]; exact det_J_ne_zero D B X hX
  refine ⟨⟨fun x y => ?_⟩, ⟨fun x hx => ?_, fun y hy => ?_⟩, ?_⟩
  ·
    have hs : ∀ i j, star (X.J i j) = X.J j i := fun i j => hX.herm j i
    simp only [sesq_apply, starRingEnd_apply, dotProduct, Matrix.mulVec, star_sum, star_mul', star_star,
      Pi.star_apply, Matrix.transpose_apply, hs, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  ·
    have h1 : star x ᵥ* X.Jᵀ = 0 := by
      refine dotProduct_eq_zero _ fun v => ?_
      rw [← Matrix.dotProduct_mulVec, ← sesq_apply]
      exact hx v
    have h2 : star x = 0 := Matrix.eq_zero_of_vecMul_eq_zero hdet h1
    simpa using congrArg star h2
  ·
    have h1 : X.Jᵀ *ᵥ y = 0 := by
      refine dotProduct_eq_zero _ fun v => ?_
      rw [dotProduct_comm]
      have := hy (star v)
      rwa [sesq_apply, star_star] at this
    exact Matrix.eq_zero_of_mulVec_eq_zero hdet h1
  ·
    show Formalism.E.hdual _ X.L = X.L
    ext x
    simp only [Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.coe_restrictScalars]
    rw [hX.dual x]
    refine forall₂_congr fun y _ => ?_
    rw [sesq_transpose_eq_form, mem_one_iff]

end GlobalTheory.WeilSchrodingerHerm

end

theorem GlobalTheory.WeilSchrodingerHerm.main : ∀ (D : D7) (B : Base D.host.F D.host.E), B.IsGood D.sp.cm.sig →
    ∀ (n : ℕ) (X : Spc D.host.F D.host.E n) (r s : ℕ), X.IsHerm D.sp.cm.sig B r s →
      (GlobalTheory.WeilSchrodinger.sesq D X.Jᵀ).IsSymm ∧ (GlobalTheory.WeilSchrodinger.sesq D X.Jᵀ).Nondegenerate ∧
        Formalism.HermitianLatticesTheory.IsUnimodular (GlobalTheory.WeilSchrodinger.sesq D X.Jᵀ) X.L :=
  fun D B _ _ X _ _ hX => GlobalTheory.WeilSchrodingerHerm.herm_nondeg_unimod D B X hX
