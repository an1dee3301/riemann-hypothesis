module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrConjApply
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteAdelicPointUnitaryGroupGramOne
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Formalism.LocalToGlobal.HermitianColumns.InLocalDiscriminantKernel
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.SatakeDualWeyl.Statement
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Equiv
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Maps

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.TestLat GlobalTheory.SumSize GlobalTheory.RowClaim GlobalTheory.ClassCount
open GlobalTheory.FrameTransport

noncomputable section

namespace GlobalTheory.FrameTransport

theorem cT_map' {A B : Type} [CommRing A] [CommRing B] {m p : Type} (s : A →+* A) (t : B →+* B) (ι : A →+* B)
    (h : ∀ a, t (ι a) = ι (s a)) (M : Matrix m p A) :
    Formalism.UG.cT t (M.map ι) = (Formalism.UG.cT s M).map ι := by
  ext i j
  simp [Formalism.UG.cT, h]

theorem conj_unitary {A B C : Type} [CommRing A] [CommRing B] [CommRing C] {n : Type} [Fintype n] [DecidableEq n]
    (s : A →+* A) (t : C →+* C) (u : B →+* B) (ι : A →+* B) (φ : C →+* B)
    (hι : ∀ a, u (ι a) = ι (s a)) (hφ : ∀ c, u (φ c) = φ (t c))
    (P Q J : Matrix n n A) (H : Matrix n n C) (hPQ : P * Q = 1) (hQP : Q * P = 1)
    (hfr : Formalism.UG.cT s P * J * P = 1) (hH : Formalism.UG.cT t H * H = 1) :
    Formalism.UG.cT u (P.map ι * H.map φ * Q.map ι) * J.map ι * (P.map ι * H.map φ * Q.map ι) = J.map ι := by
  have hJ : J = Formalism.UG.cT s Q * Q := by
    calc J = Formalism.UG.cT s (P * Q) * J * (P * Q) := by
            rw [hPQ, Formalism.UG.cT_one, Matrix.one_mul, Matrix.mul_one]
      _ = Formalism.UG.cT s Q * (Formalism.UG.cT s P * J * P) * Q := by
            rw [Formalism.UG.cT_mul]; simp only [Matrix.mul_assoc]
      _ = Formalism.UG.cT s Q * Q := by rw [hfr, Matrix.mul_one]
  have hHu : Formalism.UG.cT u (H.map φ) * H.map φ = 1 := by
    rw [cT_map' t u φ hφ, ← Matrix.map_mul, hH, Matrix.map_one _ (map_zero _) (map_one _)]
  have hQP' : Q.map ι * P.map ι = 1 := by
    rw [← Matrix.map_mul, hQP, Matrix.map_one _ (map_zero _) (map_one _)]
  have hPQc : Formalism.UG.cT u (P.map ι) * Formalism.UG.cT u (Q.map ι) = 1 := by
    rw [← Formalism.UG.cT_mul, hQP', Formalism.UG.cT_one]
  have hJ' : J.map ι = Formalism.UG.cT u (Q.map ι) * Q.map ι := by
    rw [hJ, Matrix.map_mul, cT_map' s u ι hι]
  rw [hJ']
  calc Formalism.UG.cT u (P.map ι * H.map φ * Q.map ι) * (Formalism.UG.cT u (Q.map ι) * Q.map ι) * (P.map ι * H.map φ * Q.map ι)
      = Formalism.UG.cT u (Q.map ι) * (Formalism.UG.cT u (H.map φ) * (Formalism.UG.cT u (P.map ι) * Formalism.UG.cT u (Q.map ι))
          * (Q.map ι * P.map ι) * H.map φ) * Q.map ι := by
        rw [Formalism.UG.cT_mul, Formalism.UG.cT_mul]; simp only [Matrix.mul_assoc]
    _ = Formalism.UG.cT u (Q.map ι) * Q.map ι := by
        rw [hPQc, hQP', Matrix.mul_one, Matrix.mul_one, hHu, Matrix.mul_one]

theorem adSwap_sgA (D : D7) (y : StandardLatticesGL3.AE D) :
    adSwap D (StandardLatticesGL3.sgA D y) = Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F) (adSwap D y) := by
  unfold adSwap
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
  rw [GlobalTheory.BotFormula.toAfE_sgA]
  generalize (GlobalTheory.BotFormula.toAfE D) y = x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a e =>
    simp [Lev.swapAE, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR, Formalism.UG.sigR, Algebra.TensorProduct.map_tmul]
  | add x y hx hy => rw [RingHom.map_add (f := _), RingHom.map_add (f := _), RingHom.map_add (f := _), hx, hy, RingHom.map_add (f := _)]

theorem sigR_inclEAf (D : D7) (a : D.host.E) :
    Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F) (inclEAf D a) = inclEAf D (D.sp.cm.sig a) := by
  simp only [inclEAf, Formalism.UG.sigR, Formalism.UG.inclE, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    Algebra.TensorProduct.includeLeftRingHom_apply, Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq]

theorem frConj_mem_UA {D : D7} (V : HSp D) (fr : GL (Fin V.rank) D.host.E)
    (hfr : Formalism.UG.cT (↑D.sp.cm.sig) (fr : Matrix (Fin V.rank) (Fin V.rank) D.host.E) * V.gram
      * (fr : Matrix (Fin V.rank) (Fin V.rank) D.host.E) = 1)
    (h : StandardLatticesGL3.GA D V.rank) : GlobalTheory.FrameTransport.frConj fr h.1 ∈ UA D.sp.cm V.gram := by
  have h2 : Formalism.UG.cT (StandardLatticesGL3.sgA D) (h.1 : Matrix (Fin V.rank) (Fin V.rank) (StandardLatticesGL3.AE D))
      * (1 : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (StandardLatticesGL3.inc D) * (h.1 : Matrix (Fin V.rank) (Fin V.rank) (StandardLatticesGL3.AE D)) =
      (1 : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (StandardLatticesGL3.inc D) := h.2
  rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one] at h2
  have key := conj_unitary (D.sp.cm.sig : D.host.E →+* D.host.E) (StandardLatticesGL3.sgA D) (Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F))
    (inclEAf D) (adSwap D) (sigR_inclEAf D) (fun y => (adSwap_sgA D y).symm)
    (fr : Matrix (Fin V.rank) (Fin V.rank) D.host.E) ((fr⁻¹ : GL (Fin V.rank) D.host.E) : Matrix (Fin V.rank) (Fin V.rank) D.host.E)
    V.gram (h.1 : Matrix (Fin V.rank) (Fin V.rank) (StandardLatticesGL3.AE D))
    (by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]) (by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]) hfr h2
  exact key

end GlobalTheory.FrameTransport

end
