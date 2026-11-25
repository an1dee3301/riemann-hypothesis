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
public import Init.Data.Int.Basic
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
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
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.Tactic.Group

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.TestLat GlobalTheory.SumSize GlobalTheory.RowClaim GlobalTheory.ClassCount
open GlobalTheory.FrameTransport

noncomputable section

namespace GlobalTheory.FrameTransport.Onto

open scoped TensorProduct

theorem swapAE_sigR (D : D7) (z : TensorProduct D.host.F (Af D.host.F) D.host.E) :
    Lev.swapAE D (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Af D.host.F) D.sp.cm.sig z) =
      Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F) (Lev.swapAE D z) := by
  induction z using TensorProduct.induction_on with
  | zero => rw [RingHom.map_zero, RingHom.map_zero, RingHom.map_zero]
  | add a b ha hb => rw [RingHom.map_add (f := _), RingHom.map_add (f := _), ha, hb, RingHom.map_add (f := _), RingHom.map_add (f := _)]
  | tmul a e => rfl

theorem adSwap_sgA (D : D7) (y : StandardLatticesGL3.AE D) :
    adSwap D (StandardLatticesGL3.sgA D y) = Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F) (adSwap D y) := by
  show Lev.swapAE D (GlobalTheory.BotFormula.toAfE D (StandardLatticesGL3.sgA D y)) = _
  rw [GlobalTheory.BotFormula.toAfE_sgA]
  exact swapAE_sigR D _

def adSwapEquiv (D : D7) : StandardLatticesGL3.AE D ≃+* Lev.EAf D :=
  (GlobalTheory.BotFormula.toAfE D).trans (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).toRingEquiv

theorem adSwapEquiv_apply (D : D7) (y : StandardLatticesGL3.AE D) : adSwapEquiv D y = adSwap D y := rfl

theorem sigR_inclEAf (D : D7) (e : D.host.E) :
    Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F) (inclEAf D e) = inclEAf D (D.sp.cm.sig e) := rfl

end GlobalTheory.FrameTransport.Onto

namespace GlobalTheory.FrameTransport.Onto

theorem cT_map_inclEAf (D : D7) {n : ℕ} (A : Matrix (Fin n) (Fin n) D.host.E) :
    (Formalism.UG.cT (↑D.sp.cm.sig) A).map (inclEAf D) =
      Formalism.UG.cT (Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F)) (A.map (inclEAf D)) := by
  ext i j
  exact (sigR_inclEAf D (A j i)).symm

theorem cT_map_adSwap (D : D7) {n : ℕ} (A : Matrix (Fin n) (Fin n) (StandardLatticesGL3.AE D)) :
    (Formalism.UG.cT (StandardLatticesGL3.sgA D) A).map (adSwap D) =
      Formalism.UG.cT (Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F)) (A.map (adSwap D)) := by
  ext i j
  exact adSwap_sgA D (A j i)

theorem conj_unitary {R : Type} [CommRing R] (s : R →+* R) {n : ℕ} (J P Pi M : Matrix (Fin n) (Fin n) R)
    (hPPi : P * Pi = 1) (hP : Formalism.UG.cT s P * J * P = 1) (hM : Formalism.UG.cT s M * J * M = J) :
    Formalism.UG.cT s (Pi * M * P) * (Pi * M * P) = 1 := by
  have h2 : Formalism.UG.cT s Pi * Formalism.UG.cT s P = 1 := by rw [← Formalism.UG.cT_mul, hPPi, Formalism.UG.cT_one]
  have hJ : J = Formalism.UG.cT s Pi * Pi := by
    calc J = (Formalism.UG.cT s Pi * Formalism.UG.cT s P) * J * (P * Pi) := by rw [h2, hPPi, Matrix.one_mul, Matrix.mul_one]
      _ = Formalism.UG.cT s Pi * (Formalism.UG.cT s P * J * P) * Pi := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hP, Matrix.mul_one]
  rw [Formalism.UG.cT_mul, Formalism.UG.cT_mul, ← hP]
  calc _ = Formalism.UG.cT s P * (Formalism.UG.cT s M * (Formalism.UG.cT s Pi * Pi) * M) * P := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [← hJ, hM]

theorem _root_.GlobalTheory.FrameTransport.exists_frConj_eq : ∀ {D : D7} (V : HSp D) (fr : GL (Fin V.rank) D.host.E), Formalism.UG.cT (↑D.sp.cm.sig) (fr : Matrix (Fin V.rank) (Fin V.rank) D.host.E) * V.gram * (fr : Matrix (Fin V.rank) (Fin V.rank) D.host.E) = 1 → ∀ M : GL (Fin V.rank) (Lev.EAf D), M ∈ UA D.sp.cm V.gram → ∃ h : StandardLatticesGL3.GA D V.rank, GlobalTheory.FrameTransport.frConj fr h.1 = M := by
  intro D V fr hfr M hM
  let P : GL (Fin V.rank) (Lev.EAf D) := Formalism.UG.bc (inclEAf D) fr
  let N : GL (Fin V.rank) (Lev.EAf D) := P⁻¹ * M * P
  let h0 : GL (Fin V.rank) (StandardLatticesGL3.AE D) := Formalism.UG.bc (adSwapEquiv D).symm.toRingHom N
  have hbc : Formalism.UG.bc (adSwap D) h0 = N := by
    ext i j
    show adSwap D ((adSwapEquiv D).symm _) = _
    rw [← adSwapEquiv_apply, RingEquiv.apply_symm_apply]
  have hbcm : h0.val.map (adSwap D) = N.val := congrArg Units.val hbc
  have hPPi : P.val * (P⁻¹).val = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hfr' : Formalism.UG.cT (Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F)) P.val * V.gram.map (inclEAf D) * P.val = 1 := by
    have := congrArg (fun X => X.map (inclEAf D)) hfr
    simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)] at this
    rw [cT_map_inclEAf] at this
    exact this
  have hN : Formalism.UG.cT (Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F)) N.val * N.val = 1 := by
    have hNv : N.val = (P⁻¹).val * M.val * P.val := by simp only [N, Units.val_mul]
    rw [hNv]
    exact conj_unitary _ _ _ _ _ hPPi hfr' hM
  refine ⟨⟨h0, ?_⟩, ?_⟩
  · show Formalism.UG.cT (StandardLatticesGL3.sgA D) h0.val *
        (1 : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (Formalism.UG.inclE (F := ℚ) (IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)) *
        h0.val = (1 : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (Formalism.UG.inclE (F := ℚ) (IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ))
    rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one]
    apply Matrix.map_injective (adSwapEquiv D).injective
    change (Formalism.UG.cT (StandardLatticesGL3.sgA D) h0.val * h0.val).map (adSwap D) =
      (1 : Matrix (Fin V.rank) (Fin V.rank) (StandardLatticesGL3.AE D)).map (adSwap D)
    rw [Matrix.map_mul, cT_map_adSwap, hbcm, hN, Matrix.map_one _ (map_zero _) (map_one _)]
  · show frConj fr h0 = M
    rw [frConj_apply, hbc]
    show P * (P⁻¹ * M * P) * P⁻¹ = M
    group

end GlobalTheory.FrameTransport.Onto
