module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlkGLEpsPairMem
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsGLSubmatrix
public import Development.AbelianVarietyTheory.Definitions.Foundations.MemSiegelOfIffRightAct
public import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDblCoordDblD
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
public import Init.Data.Sum.Basic
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
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Notation.Pi.Basic
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Analysis.CStarAlgebra.CStarMatrix
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
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

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SiegelTransposeInverse

open GlobalTheory.Doubling

theorem conj_mulVec_diag {A n ι : Type} [CommRing A] [Fintype n] [Fintype ι] [DecidableEq n] [DecidableEq ι]
    (e : n ⊕ n ≃ ι) (c : A →+* A) {G t : Matrix n n A} (hG : IsUnit G.det) {p : Matrix (n ⊕ n) (n ⊕ n) A}
    (hp : p * Matrix.fromRows (1 : Matrix n n A) 1 = Matrix.fromRows (1 : Matrix n n A) 1 * t)
    {X Q : Matrix ι ι A} (hQ : p.submatrix e.symm e.symm * Q = 1) (hXQ : X = Qᵀ)
    (hX : Formalism.UG.cT c X * blkMat e G (-G) * X = blkMat e G (-G)) (u : n → A) :
    (blkMat e (1 : Matrix n n A) (-1) * X * blkMat e (1 : Matrix n n A) (-1)) *ᵥ pairVec e u u =
      pairVec e ((G⁻¹ * t.map c * G) *ᵥ u) ((G⁻¹ * t.map c * G) *ᵥ u) := by
  have h1 : blkMat e G (-G) * X = (p.submatrix e.symm e.symm).map c * blkMat e G (-G) := by
    have h0 : Formalism.UG.cT c X = Q.map c := by rw [hXQ]; rfl
    have h2 : (p.submatrix e.symm e.symm).map c * Q.map c = 1 := by
      rw [← Matrix.map_mul, hQ, Matrix.map_one _ (map_zero c) (map_one c)]
    conv_rhs => rw [← hX, h0, Matrix.mul_assoc, ← Matrix.mul_assoc, h2, Matrix.one_mul]
  have h3 : ∀ y : n → A, (p.submatrix e.symm e.symm).map c *ᵥ pairVec e y y =
      pairVec e (t.map c *ᵥ y) (t.map c *ᵥ y) := by
    intro y
    have h4 := congrArg (fun M : Matrix (n ⊕ n) n A => M *ᵥ y)
      ((Matrix.map_mul (f := c) (L := p) (M := Matrix.fromRows (1 : Matrix n n A) 1)).symm.trans
        ((congrArg (fun M : Matrix (n ⊕ n) n A => M.map c) hp).trans Matrix.map_mul))
    simp only [Matrix.fromRows_map, Matrix.map_one _ (map_zero c) (map_one c), ← Matrix.mulVec_mulVec,
      Matrix.fromRows_mulVec, Matrix.one_mulVec] at h4
    rw [← Matrix.submatrix_map, Matrix.submatrix_mulVec_equiv, pairVec, pairVec, ← h4]
    have h7 : (Sum.elim y y ∘ ⇑e.symm) ∘ ⇑e.symm.symm = Sum.elim y y := by
      funext j; simp
    rw [h7]
  have h5 : blkMat e G⁻¹ (-G⁻¹) * blkMat e G (-G) = 1 := by
    rw [blkMat_mul, neg_mul_neg, Matrix.nonsing_inv_mul _ hG, blkMat_one]
  have h6 : X = blkMat e G⁻¹ (-G⁻¹) * ((p.submatrix e.symm e.symm).map c * blkMat e G (-G)) := by
    rw [← h1, ← Matrix.mul_assoc, h5, Matrix.one_mul]
  rw [h6]
  simp only [← Matrix.mulVec_mulVec, blkMat_mulVec, Matrix.neg_mulVec, Matrix.mulVec_neg, Matrix.one_mulVec, neg_neg, h3]

theorem keepsDiag_and_det {A n ι : Type} [CommRing A] [Fintype n] [Fintype ι] [DecidableEq n] [DecidableEq ι]
    (e : n ⊕ n ≃ ι) (c : A →+* A) {G t : Matrix n n A} (hG : IsUnit G.det) {Y : Matrix ι ι A}
    (hY : ∀ u, Y *ᵥ pairVec e u u = pairVec e ((G⁻¹ * t.map c * G) *ᵥ u) ((G⁻¹ * t.map c * G) *ᵥ u)) :
    KeepsDiag e Y ∧ (leviMat e Y).det = c t.det := by
  have hK : KeepsDiag e Y := keepsDiag_of_mulVec fun w hw => by
    obtain ⟨x, rfl⟩ := (mem_diagSub e).1 hw
    rw [hY]
    exact (pairVec_mem_diagSub e).2 rfl
  refine ⟨hK, ?_⟩
  have hL : leviMat e Y = G⁻¹ * t.map c * G := by
    refine Matrix.ext_of_mulVec_single fun j => ?_
    have h := (hK.mulVec_diag (Pi.single j 1)).symm.trans (hY _)
    funext i
    simpa only [pairVec_inl] using congrFun h (e (.inl i))
  rw [hL, Matrix.det_mul, Matrix.det_mul, mul_right_comm, ← Matrix.det_mul, Matrix.nonsing_inv_mul _ hG,
    Matrix.det_one, one_mul, RingHom.map_det, RingHom.mapMatrix_apply]

open GlobalTheory.DiagThetaRule in
theorem epsD_mul_self {D : D7} (S : HSp D) : epsD S * epsD S = 1 := by
  apply Subtype.ext
  apply Units.ext
  show Formalism.L2.Theta.mt (dblSp S) (epsD S) * Formalism.L2.Theta.mt (dblSp S) (epsD S) = 1
  rw [mt_epsD, blkMat_mul, neg_mul_neg, Matrix.one_mul, blkMat_one]


open GlobalTheory.DiagThetaRule in
theorem exists_siegel_conj (D : D7) (S : HSp D) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
    (p : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (GlobalTheory.WeilM.dbl (incM D.host.F JB)))
    (t : GL (Fin S.rank) (AF D.host.F ⊗[D.host.F] D.host.E))
    (hp : p.1.1 * GlobalTheory.WeilM.diagCols (Fin S.rank) = GlobalTheory.WeilM.diagCols (Fin S.rank) * t.1)
    (g : GA D (GlobalTheory.Doubling.dblSp S)) (hg : Formalism.L2.Theta.mt (GlobalTheory.Doubling.dblSp S) g =
      ((GlobalTheory.DblSchr.reG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) finSumFinEquiv.symm (GlobalTheory.DblSchr.incM_JBd S JB) p)⁻¹).1.1ᵀ) :
    ∃ h : GlobalTheory.Doubling.siegel S, GlobalTheory.DiagThetaRule.epsD S * g = (h : GA D (GlobalTheory.Doubling.dblSp S)) * GlobalTheory.DiagThetaRule.epsD S ∧
      GlobalTheory.Doubling.aP S h = GlobalTheory.Doubling.conjUnit D.sp.cm.sig (Matrix.GeneralLinearGroup.det t) := by
  have hG : IsUnit (JR (F := D.host.F) (AF D.host.F) S.gram).det := by
    have h := ((isHermND_gram S).2.isUnit).map (inclR (F := D.host.F) (E := D.host.E) (AF D.host.F))
    rw [RingHom.map_det, RingHom.mapMatrix_apply] at h
    exact h
  have hX : Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) (Formalism.L2.Theta.mt (dblSp S) g) *
      blkMat finSumFinEquiv (JR (F := D.host.F) (AF D.host.F) S.gram) (-(JR (F := D.host.F) (AF D.host.F) S.gram)) *
      Formalism.L2.Theta.mt (dblSp S) g =
      blkMat finSumFinEquiv (JR (F := D.host.F) (AF D.host.F) S.gram) (-(JR (F := D.host.F) (AF D.host.F) S.gram)) := by
    rw [← JR_dblSp_gram]
    exact g.2
  have hQ : p.1.1.submatrix finSumFinEquiv.symm finSumFinEquiv.symm *
      ((GlobalTheory.DblSchr.reG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) finSumFinEquiv.symm (GlobalTheory.DblSchr.incM_JBd S JB) p)⁻¹).1.1 = 1 := by
    rw [← GlobalTheory.DblSchr.reG_val (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) finSumFinEquiv.symm (GlobalTheory.DblSchr.incM_JBd S JB) p]
    exact Units.mul_inv _
  have hY := keepsDiag_and_det finSumFinEquiv (sigR (AF D.host.F) D.sp.cm.sig) hG
    (conj_mulVec_diag finSumFinEquiv (sigR (AF D.host.F) D.sp.cm.sig) hG hp hQ hg hX)
  refine ⟨⟨epsD S * g * epsD S, mem_siegelOf.2 hY.1⟩, ?_, Units.ext hY.2⟩
  show epsD S * g = epsD S * g * epsD S * epsD S
  rw [mul_assoc, epsD_mul_self, mul_one]

end GlobalTheory.SiegelTransposeInverse
