module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUSplittingInl
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ImportsBis
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemRatPairIff
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsFundamentalDomainOfHaar
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.SatakeDualWeyl.Statement
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
public import Mathlib.Algebra.Group.Action.Basic
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Formalism.IndefR.Datum
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.WeilPairPartner

theorem map_mul_map_inv {R S : Type} [Field R] [CommRing S] (f : R →+* S) {n : Type} [Fintype n] [DecidableEq n]
    (M : Matrix n n R) (h : M.det ≠ 0) : M.map f * (M⁻¹).map f = 1 := by
  rw [← Matrix.map_mul, M.mul_nonsing_inv (isUnit_iff_ne_zero.mpr h), Matrix.map_one _ f.map_zero f.map_one]

theorem map_inv_mul_map {R S : Type} [Field R] [CommRing S] (f : R →+* S) {n : Type} [Fintype n] [DecidableEq n]
    (M : Matrix n n R) (h : M.det ≠ 0) : (M⁻¹).map f * M.map f = 1 := by
  rw [← Matrix.map_mul, M.nonsing_inv_mul (isUnit_iff_ne_zero.mpr h), Matrix.map_one _ f.map_zero f.map_one]

theorem map_smul_eq {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {m n : Type} (r : R) (M : Matrix m n R) :
    (r • M).map f = f r • M.map f := by
  ext i j
  simp

theorem conj_inv_transpose {S : Type} [CommRing S] (c : S →+* S) {n : Type} [Fintype n] [DecidableEq n] (ξ u : S)
    (hu : IsUnit u) (B Bi K G N : Matrix n n S) (hb : Bᵀ * K * B.map c = K) (hBB : B * Bi = 1) (hBB' : Bi * B = 1)
    (hK : ξ • K = u • N) (hGN : G * N = 1) (hNG : N * G = 1) : Bi.map c * G * Biᵀ = G := by
  have hbN : Bᵀ * N * B.map c = N := by
    have h1 : Bᵀ * (ξ • K) * B.map c = ξ • K := by rw [Matrix.mul_smul, Matrix.smul_mul, hb]
    rw [hK, Matrix.mul_smul, Matrix.smul_mul] at h1
    exact hu.smul_left_cancel.mp h1
  have hcc : Bi.map c * B.map c = 1 := by
    rw [← Matrix.map_mul, hBB', Matrix.map_one _ c.map_zero c.map_one]
  have hTT : Biᵀ * Bᵀ = 1 := by rw [← Matrix.transpose_mul, hBB, Matrix.transpose_one]
  calc Bi.map c * G * Biᵀ = Bi.map c * G * Biᵀ * (N * G) := by rw [hNG, Matrix.mul_one]
    _ = Bi.map c * G * Biᵀ * ((Bᵀ * N * B.map c) * G) := by rw [hbN]
    _ = Bi.map c * G * (Biᵀ * Bᵀ) * N * B.map c * G := by simp only [Matrix.mul_assoc]
    _ = Bi.map c * (G * N) * B.map c * G := by rw [hTT, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    _ = G := by rw [hGN, Matrix.mul_one, hcc, Matrix.one_mul]

theorem pair_partner : ∀ (D : D7) (S T : HSp D) (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E)
    (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E) (ξ : AF D.host.F ⊗[D.host.F] D.host.E), JA = T.gramᵀ →
    ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹) →
    ∀ (a : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JA))
      (b : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JB)),
      ∃ (g : GA D S) (h : GA D T), mt T h = a.1.1 ∧ mt S g = (b⁻¹).1.1ᵀ := by
  intro D S T JA JB ξ hA hB a b
  have hmap : ∀ {m n : Type} (X : Matrix m n (AE D)),
      X.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF D.host.F) D.sp.cm.sig) = X.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) :=
    fun X => Matrix.ext fun i j => rfl

  have ha : (a.1.val)ᵀ * incM D.host.F JA * (a.1.val).map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) = incM D.host.F JA := a.2
  set A : Matrix (Fin T.rank) (Fin T.rank) (AE D) := a.1.val with hAdef
  have hJA : incM D.host.F JA = (incM D.host.F T.gram)ᵀ := by
    rw [hA]; rfl
  rw [hJA] at ha
  have ha' := congrArg Matrix.transpose ha
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc] at ha'
  have hmemA : a.1 ∈ Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HR (AF D.host.F) D.sp.cm.sig T.gram := by
    show Formalism.UG.cT _ a.1.val * _ * a.1.val = _
    simp only [Formalism.UG.cT, hmap]
    rw [Matrix.mul_assoc]
    exact ha'

  obtain ⟨cR, hcR⟩ : ∃ f, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF D.host.F) D.sp.cm.sig = f := ⟨_, rfl⟩
  have hb : (b.1.val)ᵀ * incM D.host.F JB * (b.1.val).map cR = incM D.host.F JB := by
    rw [← hcR, hmap]; exact b.2
  have hBB : b.1.val * (b⁻¹).1.val = 1 := by
    rw [Subgroup.coe_inv]; exact (b.1).mul_inv
  have hBB' : (b⁻¹).1.val * b.1.val = 1 := by
    rw [Subgroup.coe_inv]; exact (b.1).inv_mul
  obtain ⟨B, hBdef⟩ : ∃ B : Matrix (Fin S.rank) (Fin S.rank) (AE D), b.1.val = B := ⟨_, rfl⟩
  obtain ⟨Bi, hBidef⟩ : ∃ B : Matrix (Fin S.rank) (Fin S.rank) (AE D), (b⁻¹).1.val = B := ⟨_, rfl⟩
  rw [hBdef] at hb hBB hBB'
  rw [hBidef] at hBB hBB'
  have hGN := GlobalTheory.WeilPairPartner.map_mul_map_inv (inclR (F := D.host.F) (E := D.host.E) (AF D.host.F)) S.gram
    (GlobalTheory.VolHeckeCompare.gram_det_ne_zero S)
  have hNG := GlobalTheory.WeilPairPartner.map_inv_mul_map (inclR (F := D.host.F) (E := D.host.E) (AF D.host.F)) S.gram
    (GlobalTheory.VolHeckeCompare.gram_det_ne_zero S)
  have hsm : incM D.host.F (D.host.xi0 • S.gram⁻¹) = inclR (F := D.host.F) (AF D.host.F) D.host.xi0 •
      incM D.host.F S.gram⁻¹ :=
    GlobalTheory.WeilPairPartner.map_smul_eq _ _ _
  have hu : IsUnit (inclR (F := D.host.F) (AF D.host.F) D.host.xi0) :=
    (isUnit_iff_ne_zero.mpr (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D)).map _
  have hcore := GlobalTheory.WeilPairPartner.conj_inv_transpose cR ξ _ hu B Bi (incM D.host.F JB) (incM D.host.F S.gram)
    (incM D.host.F S.gram⁻¹) hb hBB hBB' (hB.trans hsm) hGN hNG
  have hTT : Biᵀ * Bᵀ = 1 := by
    rw [← Matrix.transpose_mul, hBB, Matrix.transpose_one]
  let gU : GL (Fin S.rank) (AE D) :=
    ⟨Biᵀ, Bᵀ, hTT, by rw [← Matrix.transpose_mul, hBB', Matrix.transpose_one]⟩
  have hmemB : gU ∈ Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HR (AF D.host.F) D.sp.cm.sig S.gram := by
    show Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF D.host.F) D.sp.cm.sig) Biᵀ * incM D.host.F S.gram * Biᵀ =
      incM D.host.F S.gram
    rw [hcR]
    simp only [Formalism.UG.cT, Matrix.transpose_map, Matrix.transpose_transpose]
    exact hcore
  refine ⟨⟨gU, hmemB⟩, ⟨a.1, hmemA⟩, rfl, ?_⟩
  show Biᵀ = ((b⁻¹).1.val)ᵀ
  rw [hBidef]

end GlobalTheory.WeilPairPartner
