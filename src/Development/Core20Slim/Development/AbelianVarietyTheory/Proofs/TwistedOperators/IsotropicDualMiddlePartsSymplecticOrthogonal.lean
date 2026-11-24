module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
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
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Trace.Defs

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwistFormsOrth

variable {D : D7}

theorem hO_mul_rat_eq_zero (V W : HSp D) {r s : ℕ} (a : Mx D W.rank r) (b : Mx D W.rank s)
    (R : Matrix (Fin r) (Fin V.rank) D.host.E) (Q : Matrix (Fin s) (Fin V.rank) D.host.E)
    (h : R * V.gram⁻¹ * Qᴴ = 0) :
    hO V W (a * GlobalTheory.MixModel.rat R) (b * GlobalTheory.MixModel.rat Q) = 0 := by
  rw [GlobalTheory.MixModel.hO_eq_trace, GlobalTheory.MixModel.adj_mul, ← GlobalTheory.MixModel.rat_conjTranspose]
  have hz : GlobalTheory.MixModel.rat R * (GlobalTheory.MixModel.giA V * GlobalTheory.MixModel.rat Qᴴ) = 0 := by
    rw [GlobalTheory.MixModel.giA, ← GlobalTheory.MixModel.rat_mul, ← GlobalTheory.MixModel.rat_mul, ← Matrix.mul_assoc, h,
      GlobalTheory.MixModel.rat_zero]
  have e : GlobalTheory.MixModel.giA V * (GlobalTheory.MixModel.rat Qᴴ * GlobalTheory.MixModel.adj b * (GlobalTheory.MixModel.gA W * (a * GlobalTheory.MixModel.rat R)))
      = GlobalTheory.MixModel.giA V * GlobalTheory.MixModel.rat Qᴴ * (GlobalTheory.MixModel.adj b * (GlobalTheory.MixModel.gA W * a)) * GlobalTheory.MixModel.rat R := by
    simp only [Matrix.mul_assoc]
  rw [e, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hz, Matrix.zero_mul, Matrix.trace_zero]

theorem symplO_mul_rat_eq_zero (V W : HSp D) {r s : ℕ} (a : Mx D W.rank r) (b : Mx D W.rank s)
    (R : Matrix (Fin r) (Fin V.rank) D.host.E) (Q : Matrix (Fin s) (Fin V.rank) D.host.E)
    (h : R * V.gram⁻¹ * Qᴴ = 0) :
    symplO V W (a * GlobalTheory.MixModel.rat R) (b * GlobalTheory.MixModel.rat Q) = 0 := by
  rw [GlobalTheory.MixModel.symplO_eq, hO_mul_rat_eq_zero V W a b R Q h, mul_zero, map_zero]

theorem frame_pair (V : HSp D) {r s : ℕ} (C₁ : Matrix (Fin V.rank) (Fin r) D.host.E)
    (C₂ : Matrix (Fin V.rank) (Fin s) D.host.E) :
    adj D C₁ * V.gram * V.gram⁻¹ * (adj D C₂ * V.gram)ᴴ = adj D C₁ * V.gram * C₂ := by
  have hG := GlobalTheory.MixModel.gram_isUnit_det V
  simp only [adj, GlobalTheory.MixModel.cT_sig, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    GlobalTheory.MixModel.gram_conjTranspose]
  simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hG]

theorem frame_mid (V V' : HSp D) {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E)
    (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E) (h : adj D C * V.gram * B = 0) :
    adj D C * V.gram * V.gram⁻¹ * (V'.gram⁻¹ * adj D B * V.gram)ᴴ = 0 := by
  have hG := GlobalTheory.MixModel.gram_isUnit_det V
  simp only [adj, GlobalTheory.MixModel.cT_sig] at h ⊢
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, GlobalTheory.MixModel.gram_conjTranspose,
    GlobalTheory.MixModel.gramInv_conjTranspose]
  simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hG]
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h, Matrix.zero_mul]

theorem orthogonal : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → ∀ C' : Matrix (Fin V.rank) (Fin r) D.host.E, adj D C * V.gram * C' = 1 → adj D C' * V.gram * C' = 0 → adj D C' * V.gram * B = 0 → (∀ a b, symplO V W (isoPart V W C a) (isoPart V W C b) = 0) ∧ (∀ a x, symplO V W (isoPart V W C a) (midPart V V' W B x) = 0) ∧ (∀ a x, symplO V W (isoPart V W C' a) (midPart V V' W B x) = 0) ∧ (∀ a b, symplO V W (isoPart V W C' a) (isoPart V W C' b) = 0) := by
  intro D V V' W r C B hs C' _ hC' hC'B
  have hC : adj D C * V.gram * C = 0 := hs.frame.2.2
  refine ⟨fun a b => ?_, fun a x => ?_, fun a x => ?_, fun a b => ?_⟩
  · exact symplO_mul_rat_eq_zero V W a b (adj D C * V.gram) (adj D C * V.gram) ((frame_pair V C C).trans hC)
  · exact symplO_mul_rat_eq_zero V W a x (adj D C * V.gram) (V'.gram⁻¹ * adj D B * V.gram) (frame_mid V V' C B hs.orth)
  · exact symplO_mul_rat_eq_zero V W a x (adj D C' * V.gram) (V'.gram⁻¹ * adj D B * V.gram) (frame_mid V V' C' B hC'B)
  · exact symplO_mul_rat_eq_zero V W a b (adj D C' * V.gram) (adj D C' * V.gram) ((frame_pair V C' C').trans hC')

end GlobalTheory.TwistFormsOrth

end
