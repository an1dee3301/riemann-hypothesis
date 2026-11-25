module

public import Mathlib
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BlockMatrixMul
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsMaximalCompactUnnComponentStandardCartanIn
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BigCellCosetsHermitianParam
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsBlockMatrixTwoByTwoFinEq
public import Development.Core20Slim.Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.EisCellsDefs
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Block
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.CompanionTheory.EisCovar
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.EisCovar.Transfer

section Field

variable {F₀ : Type} [Field F₀] {n : ℕ}

theorem block_matrix_map {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') (A B C E : Matrix (Fin n) (Fin n) R) :
    (blk4 A B C E).map f = blk4 (A.map f) (B.map f) (C.map f) (E.map f) := by
  rw [blk4, blk4, ← Matrix.fromBlocks_map]; rfl

theorem blockMatrixTwoByTwoFin_transpose {R : Type} (A B C E : Matrix (Fin n) (Fin n) R) :
    (blk4 A B C E)ᵀ = blk4 Aᵀ Cᵀ Bᵀ Eᵀ := by
  simp only [blk4, Matrix.transpose_submatrix, Matrix.fromBlocks_transpose]

theorem cT_mul (σ : F₀ →+* F₀) {N : ℕ} (g h : Matrix (Fin N) (Fin N) F₀) : cT σ (g * h) = cT σ h * cT σ g := by
  simp only [cT, Matrix.map_mul, Matrix.transpose_mul]

theorem cT_blk4 (σ : F₀ →+* F₀) (A B C E : Matrix (Fin n) (Fin n) F₀) :
    cT σ (blk4 A B C E) = blk4 (cT σ A) (cT σ C) (cT σ B) (cT σ E) := by
  simp only [cT, block_matrix_map, blockMatrixTwoByTwoFin_transpose]

theorem cT_zero (σ : F₀ →+* F₀) : cT σ (0 : Matrix (Fin n) (Fin n) F₀) = 0 := by
  ext i j; simp [cT]

theorem cT_one (σ : F₀ →+* F₀) : cT σ (1 : Matrix (Fin n) (Fin n) F₀) = 1 := by
  ext i j; simp [cT, Matrix.one_apply, eq_comm]

theorem cT_neg (σ : F₀ →+* F₀) (x : Matrix (Fin n) (Fin n) F₀) : cT σ (-x) = -cT σ x := by
  ext i j; simp [cT]

theorem cT_cT {σ : F₀ →+* F₀} (hσ : ∀ x, σ (σ x) = x) (x : Matrix (Fin n) (Fin n) F₀) : cT σ (cT σ x) = x := by
  ext i j; simp [cT, hσ]

theorem isUnit_det_cT (σ : F₀ →+* F₀) {a : Matrix (Fin n) (Fin n) F₀} (ha : IsUnit a.det) : IsUnit (cT σ a).det := by
  have e : (cT σ a).det = σ a.det := by
    rw [cT, Matrix.det_transpose, RingHom.map_det]; rfl
  rw [e]; exact ha.map σ

theorem mA_isUnit_det (σ : F₀ →+* F₀) {a : Matrix (Fin n) (Fin n) F₀} (ha : IsUnit a.det) : IsUnit (mA σ a).det := by
  refine Matrix.isUnit_det_of_right_inverse (B := blk4 a⁻¹ 0 0 (cT σ a)) ?_
  have h1 : a * a⁻¹ = 1 := Matrix.mul_nonsing_inv _ ha
  have h2 : (cT σ a)⁻¹ * cT σ a = 1 := Matrix.nonsing_inv_mul _ (isUnit_det_cT σ ha)
  rw [mA, submatrix_fromBlocks_mul]
  simp only [Matrix.mul_zero, Matrix.zero_mul, zero_add, add_zero, h1, h2, block_matrix_one]

theorem nB_isUnit_det (b : Matrix (Fin n) (Fin n) F₀) : IsUnit (nB b).det := by
  refine Matrix.isUnit_det_of_right_inverse (B := blk4 1 (-b) 0 1) ?_
  rw [nB, submatrix_fromBlocks_mul]
  simp only [Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul, Matrix.mul_zero, zero_add, add_zero, add_neg_cancel, neg_mul, neg_neg, neg_zero, neg_add_cancel, block_matrix_one]

theorem Jm_isUnit_det : IsUnit (EC.Jm F₀ n).det := by
  refine Matrix.isUnit_det_of_right_inverse (B := blk4 0 (-1) 1 0) ?_
  rw [EC.Jm, submatrix_fromBlocks_mul]
  simp only [Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul, Matrix.mul_zero, zero_add, add_zero, add_neg_cancel, neg_mul, neg_neg, neg_zero, neg_add_cancel, block_matrix_one]

theorem mA_isUnitary {σ : F₀ →+* F₀} (hσ : ∀ x, σ (σ x) = x) {a : Matrix (Fin n) (Fin n) F₀} (ha : IsUnit a.det) :
    IsUnitary σ (EC.Jm F₀ n) (mA σ a) := by
  have h1 : cT σ a * (cT σ a)⁻¹ = 1 := Matrix.mul_nonsing_inv _ (isUnit_det_cT σ ha)
  have h2 : cT σ (cT σ a)⁻¹ * a = 1 := by
    have h := congrArg (cT σ) h1
    rwa [cT_mul, cT_cT hσ, cT_one] at h
  unfold IsUnitary EC.Jm mA
  rw [cT_blk4, submatrix_fromBlocks_mul, submatrix_fromBlocks_mul]
  simp only [cT_zero, Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.one_mul, zero_add, add_zero, neg_mul, mul_neg, neg_neg, neg_zero, neg_add_cancel, h1, h2]

theorem nB_isUnitary {σ : F₀ →+* F₀} {b : Matrix (Fin n) (Fin n) F₀} (hb : cT σ b = b) :
    IsUnitary σ (EC.Jm F₀ n) (nB b) := by
  unfold IsUnitary EC.Jm nB
  rw [cT_blk4, submatrix_fromBlocks_mul, submatrix_fromBlocks_mul]
  simp only [cT_zero, cT_one, hb, Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.one_mul, zero_add, add_zero, neg_mul, mul_neg, neg_neg, neg_zero, neg_add_cancel, add_neg_cancel]

theorem Jm_isUnitary (σ : F₀ →+* F₀) : IsUnitary σ (EC.Jm F₀ n) (EC.Jm F₀ n) := by
  unfold IsUnitary EC.Jm
  rw [cT_blk4, submatrix_fromBlocks_mul, submatrix_fromBlocks_mul]
  simp only [cT_zero, cT_one, cT_neg, Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.one_mul, zero_add, add_zero, neg_mul, mul_neg, neg_neg, neg_zero, neg_add_cancel]

theorem isUnitary_mul {σ : F₀ →+* F₀} {N : ℕ} {J g h : Matrix (Fin N) (Fin N) F₀} (hg : IsUnitary σ J g)
    (hh : IsUnitary σ J h) : IsUnitary σ J (g * h) := by
  unfold IsUnitary at *
  rw [cT_mul]
  calc cT σ h * cT σ g * J * (g * h) = cT σ h * (cT σ g * J * g) * h := by
        simp only [Matrix.mul_assoc]
    _ = J := by rw [hg, hh]

end Field

variable {D : D7} {n : ℕ}

theorem sig_sig (x : D.host.E) :
    (D.sp.cm.sig : D.host.E →+* D.host.E) ((D.sp.cm.sig : D.host.E →+* D.host.E) x) = x :=
  star_star x

theorem cT_sig_eq {a b : ℕ} (M : Matrix (Fin a) (Fin b) D.host.E) :
    cT (D.sp.cm.sig : D.host.E →+* D.host.E) M = Mᴴ := rfl

theorem map_mA (a : Matrix (Fin n) (Fin n) D.host.E) :
    (mA (D.sp.cm.sig : D.host.E →+* D.host.E) a).map (incA D) =
      blk4 (rat a) 0 0 (adj (rat a⁻¹)) := by
  change (blk4 a 0 0 (cT (D.sp.cm.sig : D.host.E →+* D.host.E) a)⁻¹).map (incA D) = _
  rw [block_matrix_map, cT_sig_eq, ← Matrix.conjTranspose_nonsing_inv, ← rat_conjTranspose]
  simp only [Matrix.map_zero _ (map_zero (incA D))]
  rfl

theorem map_nB (b : Matrix (Fin n) (Fin n) D.host.E) :
    (nB b).map (incA D) = blk4 1 (rat b) 0 1 := by
  change (blk4 1 b 0 1).map (incA D) = _
  rw [block_matrix_map]
  show blk4 (rat 1) (rat b) (rat 0) (rat 1) = _
  rw [rat_one, rat_zero]

theorem map_Jm : (EC.Jm D.host.E n).map (incA D) = blk4 0 1 (-1) 0 := by
  rw [EC.Jm, block_matrix_map]
  show blk4 (rat 0) (rat 1) (rat (-1)) (rat 0) = _
  simp only [rat_zero, rat_one, rat_neg]

theorem ratPts_transfer : RatPts → ∀ (D : D7) (n : ℕ), FieldGen D.host.E (D.sp.cm.sig : D.host.E →+* D.host.E) n → ∀ S : G D n → Prop, (∀ g h, S g → S h → S (g * h)) → (∀ (g : G D n) (a : GL (Fin n) (AE D)), mat g = blk4 a.1 0 0 (adj (a⁻¹).1) → S g) → (∀ (g : G D n) (b : Mx D n n), adj b = b → mat g = blk4 1 b 0 1 → S g) → (∀ g : G D n, mat g = blk4 0 1 (-1) 0 → S g) → ∀ γ ∈ GF D n, S γ := by
  intro hR D n hF S hmul hm hn hw γ hγ
  obtain ⟨h1, h2, -⟩ := hR D n
  obtain ⟨g, hgu, hgU, hg⟩ := h1 γ hγ
  let T : Matrix (Fin (n + n)) (Fin (n + n)) D.host.E → Prop := fun M =>
    IsUnit M.det ∧ IsUnitary (D.sp.cm.sig : D.host.E →+* D.host.E) (EC.Jm D.host.E n) M ∧
      ∀ γ' : G D n, mat γ' = M.map (incA D) → S γ'
  have hprod : ∀ M₁ M₂, T M₁ → T M₂ → T (M₁ * M₂) := by
    rintro M₁ M₂ ⟨u₁, U₁, s₁⟩ ⟨u₂, U₂, s₂⟩
    refine ⟨by rw [Matrix.det_mul]; exact u₁.mul u₂, isUnitary_mul U₁ U₂, fun γ' e => ?_⟩
    obtain ⟨γ₁, -, e₁⟩ := h2 M₁ u₁ U₁
    obtain ⟨γ₂, -, e₂⟩ := h2 M₂ u₂ U₂
    have e' : γ' = γ₁ * γ₂ := mat_injective' (by rw [e, mat_mul', e₁, e₂, Matrix.map_mul])
    rw [e']
    exact hmul _ _ (s₁ _ e₁) (s₂ _ e₂)
  have hmA : ∀ a : Matrix (Fin n) (Fin n) D.host.E, IsUnit a.det →
      T (mA (D.sp.cm.sig : D.host.E →+* D.host.E) a) := by
    intro a ha
    refine ⟨mA_isUnit_det _ ha, mA_isUnitary sig_sig ha, fun γ' e => ?_⟩
    let a' : GL (Fin n) (AE D) := ⟨rat a, rat a⁻¹,
      by rw [← rat_mul, Matrix.mul_nonsing_inv _ ha, rat_one],
      by rw [← rat_mul, Matrix.nonsing_inv_mul _ ha, rat_one]⟩
    exact hm γ' a' (e.trans (map_mA a))
  have hnB : ∀ b : Matrix (Fin n) (Fin n) D.host.E, cT (D.sp.cm.sig : D.host.E →+* D.host.E) b = b → T (nB b) := by
    intro b hb
    refine ⟨nB_isUnit_det b, nB_isUnitary hb, fun γ' e => hn γ' (rat b) ?_ (e.trans (map_nB b))⟩
    rw [← rat_conjTranspose]
    exact congrArg rat hb
  have hJ : T (EC.Jm D.host.E n) :=
    ⟨Jm_isUnit_det, Jm_isUnitary _, fun γ' e => hw γ' (e.trans map_Jm)⟩
  exact (hF T hprod hmA hnB hJ g hgu hgU).2.2 γ hg

end GlobalTheory.CompanionTheory.EisCovar.Transfer
