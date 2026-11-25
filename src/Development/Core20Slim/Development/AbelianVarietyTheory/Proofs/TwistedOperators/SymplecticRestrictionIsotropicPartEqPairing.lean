module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.HalfSymplZeroRight
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FinTensMemLatO
public import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.StarPurelyImaginaryEqNeg
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.T2SpaceHalfAdelicMatrixAddSubgroup
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
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Algebra.Star.BigOperators
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Trace.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition GlobalTheory.HalfAverage

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HalfAverage
variable {D : D7}

private theorem sum_comm_three_reverse {M ι κ μ : Type*} [AddCommMonoid M] [Fintype ι] [Fintype κ] [Fintype μ]
    (f : ι → κ → μ → M) : ∑ i, ∑ j, ∑ k, f i j k = ∑ k, ∑ j, ∑ i, f i j k :=
  calc ∑ i, ∑ j, ∑ k, f i j k = ∑ i, ∑ k, ∑ j, f i j k := Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ k, ∑ i, ∑ j, f i j k := Finset.sum_comm
    _ = ∑ k, ∑ j, ∑ i, f i j k := Finset.sum_congr rfl fun _ _ => Finset.sum_comm

theorem hO_eq_trace (S T : HSp D) (x y : WO S T) :
    hO S T x y = Matrix.trace ((S.gram⁻¹).map (incA D) * (y.map (cA D)).transpose * (T.gram).map (incA D) * x) := by
  unfold hO
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  refine (sum_comm_three_reverse _).trans ?_
  exact Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun b _ => by ring

theorem halfPair_eq_trace (W : HSp D) {r : ℕ} (a t : Mx D W.rank r) :
    halfPair W a t = Matrix.trace ((a.map (cA D)).transpose * (W.gram).map (incA D) * t) := by
  unfold halfPair
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply, Finset.sum_mul]
  exact Finset.sum_comm

theorem map_cA_isoMat_transpose (V : HSp D) {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E) :
    Matrix.transpose (((adj D C * V.gram).map (incA D)).map (cA D)) = (V.gram * C).map (incA D) := by
  ext i j
  simp only [Matrix.transpose_apply, Matrix.map_apply]
  rw [GlobalTheory.DualPairCheck.cA_incA]
  congr 1
  simp only [Matrix.mul_apply, star_sum, star_mul', adj, Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply,
    GlobalTheory.BesselCompare.sig_eq, star_star, GlobalTheory.DualPairCheck.gram_star]
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

theorem sympl_restEmb_isoPart : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → ∀ K : Matrix (Fin r) (Fin V.rank) D.host.E, K * C = 1 → ∀ a t : Mx D W.rank r, symplO V W (restEmb V W K t) (isoPart V W C a) = halfSympl W a t := by
  intro D V V' W r C B _ K hK a t
  have hG : IsUnit V.gram.det := GlobalTheory.LatVac.gram_det_isUnit V
  have h1 : K * V.gram⁻¹ * (V.gram * C) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc V.gram⁻¹, Matrix.nonsing_inv_mul _ hG, Matrix.one_mul, hK]
  have key : K.map (incA D) * (V.gram⁻¹).map (incA D) * (V.gram * C).map (incA D) = 1 := by
    rw [← Matrix.map_mul, ← Matrix.map_mul, h1]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  suffices h : hO V W (restEmb V W K t) (isoPart V W C a) = halfPair W a t by
    unfold symplO halfSympl
    rw [h]
  have e1 : (isoPart V W C a).map (cA D) = a.map (cA D) * ((adj D C * V.gram).map (incA D)).map (cA D) := by
    unfold isoPart
    exact Matrix.map_mul
  have e2 : restEmb V W K t = (t : Matrix (Fin W.rank) (Fin r) (AE D)) * K.map (incA D) := rfl
  rw [hO_eq_trace, halfPair_eq_trace, e1, Matrix.transpose_mul, map_cA_isoMat_transpose, e2]
  calc _ = Matrix.trace ((K.map (incA D) * (V.gram⁻¹).map (incA D) * (V.gram * C).map (incA D)) *
        ((a.map (cA D)).transpose * (W.gram).map (incA D) * t)) := by
        simp only [Matrix.mul_assoc]
        rw [Matrix.trace_mul_comm (K.map (incA D))]
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [key, Matrix.one_mul]

end GlobalTheory.HalfAverage
