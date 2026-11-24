module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasisAdaptedToCartanInvolution
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Formalism.LocalRingCardinality.DataTheta
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Function
public import Init.Data.Int.Basic
public import Init.Data.Int.Lemmas
public import Init.Data.Int.Order
public import Init.Data.Nat.Basic
public import Init.Data.Sum.Basic
public import Init.Data.Zero
public import Init.Omega.Coeffs
public import Init.Omega.Constraint
public import Init.Omega.Int
public import Init.Omega.LinearCombo
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Prod
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Ker
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Notation.Prod
public import Mathlib.Algebra.Order.Group.Unbundled.Basic
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Algebra.Star.BigOperators
public import Mathlib.Analysis.CStarAlgebra.Basic
public import Mathlib.Analysis.CStarAlgebra.CStarMatrix
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Analysis.Matrix.Hermitian
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fin.SuccPred
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Block
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.NNRat.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Rat.Init
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.LinearAlgebra.Matrix.InvariantBasisNumber
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.LinearAlgebra.Prod
public import Mathlib.LinearAlgebra.StdBasis
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.Bialgebra.Basic
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.EssentialFiniteness
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.TotallySplit
public import Mathlib.RingTheory.Unramified.Basic

@[expose] public section

open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.RealLift.HermitianFrameExistence

open Matrix
open scoped ComplexOrder

theorem map_star_trip {m k l o : Type} [Fintype k] [Fintype l] (X : Matrix k m ℂ) (Y : Matrix k l ℂ)
    (Z : Matrix l o ℂ) : (Xᵀ * Y * Z.map star).map star = Xᴴ * Y.map star * Z := by
  have h : ∀ {a b : Type} (W : Matrix a b ℂ), W.map star = W.map (starRingEnd ℂ) := fun _ => rfl
  rw [h (Xᵀ * Y * Z.map star), Matrix.map_mul, Matrix.map_mul]
  simp [Matrix.conjTranspose, Matrix.map_map, Function.comp_def]

theorem quad {n ι : Type} [Fintype n] [Fintype ι] (G : Matrix n n ℂ) (B : Matrix n ι ℂ) (w : ι → ℂ) :
    star (B *ᵥ w) ⬝ᵥ G *ᵥ (B *ᵥ w) = star w ⬝ᵥ (Bᴴ * G * B) *ᵥ w := by
  conv_rhs => rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, ← star_mulVec]

theorem val_inl {p q : ℕ} (u : Fin p → ℂ) :
    star (Sum.elim u (0 : Fin q → ℂ)) ⬝ᵥ (fromBlocks 1 0 0 (-1) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) *ᵥ
      Sum.elim u 0 = star u ⬝ᵥ u := by
  simp [fromBlocks_mulVec, dotProduct, Fintype.sum_sum_type]

theorem val_inr {p q : ℕ} (v : Fin q → ℂ) :
    star (Sum.elim (0 : Fin p → ℂ) v) ⬝ᵥ (fromBlocks 1 0 0 (-1) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) *ᵥ
      Sum.elim 0 v = -(star v ⬝ᵥ v) := by
  simp [fromBlocks_mulVec, dotProduct, Fintype.sum_sum_type, neg_mulVec, Finset.sum_neg_distrib]

theorem inertia {n p q r s : ℕ} (G : Matrix (Fin n) (Fin n) ℂ) (B : Matrix (Fin n) (Fin p ⊕ Fin q) ℂ)
    (A : Matrix (Fin n) (Fin r ⊕ Fin s) ℂ) (hB : Bᴴ * G * B = fromBlocks 1 0 0 (-1))
    (hA : Aᴴ * G * A = fromBlocks 1 0 0 (-1)) : p + s ≤ n := by
  have key : ∀ (u : Fin p → ℂ) (v : Fin s → ℂ), B *ᵥ Sum.elim u 0 = A *ᵥ Sum.elim 0 v → u = 0 ∧ v = 0 := by
    intro u v h
    have h1 := quad G B (Sum.elim u 0)
    have h2 := quad G A (Sum.elim 0 v)
    rw [hB, val_inl] at h1
    rw [hA, val_inr, ← h, h1] at h2
    have hu := dotProduct_star_self_nonneg u
    have hv := dotProduct_star_self_nonneg v
    have h3 : star u ⬝ᵥ u = 0 := le_antisymm (by rw [h2]; exact neg_nonpos.2 hv) hu
    have h4 : star v ⬝ᵥ v = 0 := by rw [h3] at h2; exact neg_eq_zero.1 h2.symm
    exact ⟨dotProduct_star_self_eq_zero.1 h3, dotProduct_star_self_eq_zero.1 h4⟩
  let f : (Fin p → ℂ) × (Fin s → ℂ) →ₗ[ℂ] (Fin n → ℂ) :=
    B.mulVecLin ∘ₗ ((LinearEquiv.sumArrowLequivProdArrow (Fin p) (Fin q) ℂ ℂ).symm.toLinearMap ∘ₗ
        (LinearMap.inl ℂ _ _ ∘ₗ LinearMap.fst ℂ _ _)) -
      A.mulVecLin ∘ₗ ((LinearEquiv.sumArrowLequivProdArrow (Fin r) (Fin s) ℂ ℂ).symm.toLinearMap ∘ₗ
        (LinearMap.inr ℂ _ _ ∘ₗ LinearMap.snd ℂ _ _))
  have e1 : ∀ u : Fin p → ℂ, (LinearEquiv.sumArrowLequivProdArrow (Fin p) (Fin q) ℂ ℂ).symm (u, 0) = Sum.elim u 0 := by
    intro u; ext (i | i) <;> simp
  have e2 : ∀ v : Fin s → ℂ, (LinearEquiv.sumArrowLequivProdArrow (Fin r) (Fin s) ℂ ℂ).symm ((0 : Fin r → ℂ), v) = Sum.elim (0 : Fin r → ℂ) v := by
    intro v; ext (i | i) <;> simp
  have hf : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨u, v⟩ huv
    have h0 : B *ᵥ Sum.elim u 0 - A *ᵥ Sum.elim 0 v = 0 := by
      simpa [f, e1, e2, Matrix.mulVecLin_apply] using huv
    obtain ⟨hu, hv⟩ := key u v (sub_eq_zero.1 h0)
    simp [hu, hv]
  have := LinearMap.finrank_le_finrank_of_injective hf
  simpa [Module.finrank_prod] using this

theorem card_le_of_mul_eq_one {m k : Type} [Fintype m] [Fintype k] [DecidableEq m] (X : Matrix m k ℂ)
    (Y : Matrix k m ℂ) (h : X * Y = 1) : Fintype.card m ≤ Fintype.card k := by
  have hi : Function.Injective Y.mulVecLin := by
    intro u v huv
    have := congrArg (fun w => X *ᵥ w) huv
    simpa [Matrix.mulVecLin_apply, mulVec_mulVec, h] using this
  simpa using LinearMap.finrank_le_finrank_of_injective hi

theorem star_form {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (v y : Fin n → ℂ) :
    star (v ⬝ᵥ M *ᵥ star y) = star v ⬝ᵥ M.map star *ᵥ y := by
  simp [dotProduct, mulVec, star_sum, Finset.mul_sum, mul_comm, mul_left_comm]

end GlobalTheory.RealLift.HermitianFrameExistence

namespace GlobalTheory.RealLift

open Matrix GlobalTheory.RealLift.HermitianFrameExistence
open scoped ComplexOrder

theorem frameEx_holds : FrameEx := by
  intro n r s M θ hSig hC
  obtain ⟨hrs, A0, hA0⟩ := hSig
  obtain ⟨hθθ, hiso, hpos⟩ := hC
  set G : Matrix (Fin n) (Fin n) ℂ := M.map star with hGdef
  have hJ : ∀ p q : ℕ, (fromBlocks 1 0 0 (-1) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ).map star =
      fromBlocks 1 0 0 (-1) := by
    intro p q; ext (i | i) (j | j) <;> simp [Matrix.one_apply] <;> split_ifs <;> simp
  have hA : A0ᴴ * G * A0 = fromBlocks 1 0 0 (-1) := by
    rw [← map_star_trip, hA0, hJ]

  obtain ⟨L, hLdef⟩ : ∃ L : Matrix (Fin r ⊕ Fin s) (Fin n) ℂ,
      L = (fromBlocks 1 0 0 (-1) : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ) * (A0ᴴ * G) := ⟨_, rfl⟩
  have hL : L * A0 = 1 := by
    calc L * A0 = (fromBlocks 1 0 0 (-1) : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ) * (A0ᴴ * G * A0) := by
          rw [hLdef]; simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hA, fromBlocks_multiply]; simp
  have e : Fin r ⊕ Fin s ≃ Fin n := finSumFinEquiv.trans (finCongr hrs)
  have hR : A0 * L = 1 := (mul_eq_one_comm_of_equiv e).1 hL
  have hLc : Lᴴ * A0ᴴ = 1 := by rw [← conjTranspose_mul, hR, conjTranspose_one]
  have hJh : ((fromBlocks 1 0 0 (-1)) : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ)ᴴ = fromBlocks 1 0 0 (-1) := by
    simp [fromBlocks_conjTranspose]
  have hA' : A0ᴴ * Gᴴ * A0 = A0ᴴ * G * A0 := by
    calc A0ᴴ * Gᴴ * A0 = (A0ᴴ * G * A0)ᴴ := by simp [conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by rw [hA, hJh]
  have Gherm : Gᴴ = G := by
    calc Gᴴ = (Lᴴ * A0ᴴ) * Gᴴ * (A0 * L) := by rw [hLc, hR]; simp
      _ = Lᴴ * (A0ᴴ * Gᴴ * A0) * L := by simp only [Matrix.mul_assoc]
      _ = Lᴴ * (A0ᴴ * G * A0) * L := by rw [hA']
      _ = (Lᴴ * A0ᴴ) * G * (A0 * L) := by simp only [Matrix.mul_assoc]
      _ = G := by rw [hLc, hR]; simp

  have hiso' : θᴴ * G * θ = G := by rw [← map_star_trip, hiso]
  have hcomm : θᴴ * G = G * θ := by
    calc θᴴ * G = θᴴ * G * θ * θ := by rw [Matrix.mul_assoc (θᴴ * G), hθθ, Matrix.mul_one]
      _ = G * θ := by rw [hiso']
  have hherm : (G * θ).IsHermitian := by
    unfold IsHermitian; rw [conjTranspose_mul, Gherm, hcomm]
  have hPD : (G * θ).PosDef := by
    refine Matrix.posDef_iff_dotProduct_mulVec.2 ⟨hherm, fun x hx => ?_⟩
    have hval : star x ⬝ᵥ (G * θ) *ᵥ x = star ((θ *ᵥ x) ⬝ᵥ M *ᵥ star x) := by
      rw [← hcomm, star_form, ← hGdef, ← mulVec_mulVec, dotProduct_mulVec, ← star_mulVec]
    refine Complex.pos_iff.2 ⟨?_, (hherm.im_star_dotProduct_mulVec_self x).symm⟩
    rw [hval, Complex.star_def, Complex.conj_re]; exact hpos x hx
  obtain ⟨p, q, B, B', h1, h2, h3, h4⟩ :=
    GlobalTheory.exists_basis_adapted_to_cartan_involution n G θ hθθ hiso' hPD
  have i1 := inertia G B A0 h3 hA
  have i2 := inertia G A0 B hA h3
  have i3 := card_le_of_mul_eq_one B B' h1
  simp only [Fintype.card_fin, Fintype.card_sum] at i3
  obtain rfl : p = r := by omega
  obtain rfl : q = s := by omega
  refine ⟨B, ⟨?_, B', h1⟩, h4⟩
  calc Bᵀ * M * B.map star = ((Bᵀ * M * B.map star).map star).map star := by simp [Matrix.map_map, Function.comp_def]
    _ = _ := by rw [map_star_trip, ← hGdef, h3, hJ]; rfl

end GlobalTheory.RealLift
