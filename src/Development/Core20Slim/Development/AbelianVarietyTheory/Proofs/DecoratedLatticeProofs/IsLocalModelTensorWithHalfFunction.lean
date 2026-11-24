module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.LatticeFrames.TiedAt
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TensorOneApply
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.UnitaryVolumePairs
public import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsRatDatum
public import Formalism.HermitianCurvature.StatementM
public import Formalism.HermitianCurvature.StatementMA
public import Formalism.HermitianCurvature.StatementQ
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LevelSubgroupCharacterUnitary
public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.CurveHyp
public import Formalism.SharpRestriction.CuspSpanNormBounds.LeadMinorK
public import Formalism.SharpRestriction.Divisibility.OrbitPlaces
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
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
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Trace.Defs
public import Mathlib.Tactic.LinearCombination.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel    GlobalTheory.SplitWeil  GlobalTheory.AdForm GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocMod.TensorModel

variable {D : D7}

theorem cA_invol (z : AE D) : cA D (cA D z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    rw [show cA D (cA D (a ⊗ₜ[D.host.F] x)) = a ⊗ₜ[D.host.F] star (star x) from rfl, star_star]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]

theorem symplO_add_left' (S T : HSp D) (x x' y : WO S T) :
    symplO S T (x + x') y = symplO S T x y + symplO S T x' y := by
  unfold symplO hO
  simp only [Matrix.add_apply, mul_add, Finset.sum_add_distrib, map_add (f := _)]

theorem half_sum {m n : ℕ} {e e' : AE D} (he : e * e' = 0) {u : Mx D m n} (hu : IsHalf e' u) : IsHalf (e + e') u :=
  fun i j => by
    have h0 : e * u i j = 0 := by
      calc e * u i j = e * (e' * u i j) := by rw [hu i j]
        _ = 0 := by rw [← mul_assoc, he, zero_mul]
    rw [add_mul, h0, zero_add, hu i j]

theorem half_sum_cA {m n : ℕ} {e e' : AE D} (he : e * e' = 0) {u : Mx D m n} (hu : IsHalf (cA D e') u) :
    IsHalf (cA D (e + e')) u := by
  rw [map_add (f := _)]
  refine half_sum ?_ hu
  rw [← map_mul, he, map_zero]

theorem symplO_half_zero {S T : HSp D} {e e' : AE D} (he : e * e' = 0) {s y : WO S T} (hs : IsHalf e s)
    (hy : IsHalf (cA D e') y) : symplO S T s y = 0 := by
  have h0 : hO S T s y = 0 := by
    unfold hO
    refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => Finset.sum_eq_zero fun c _ =>
      Finset.sum_eq_zero fun d _ => ?_
    have h1 : cA D (y c b) = e' * cA D (y c b) := by
      conv_lhs => rw [← hy c b]
      rw [map_mul, cA_invol]
    have h2 : s d a = e * s d a := (hs d a).symm
    rw [h1, h2]
    linear_combination (incA D (S.gram⁻¹ a b) * cA D (y c b) * incA D (T.gram c d) * s d a) * he
  unfold symplO
  rw [h0, mul_zero, map_zero]

theorem isModel_tensor : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (e : AE D), e * p.e = 0 → ∀ Φ : WO S T → ℂ, (∀ t, Φ t ≠ 0 → IsHalf e t) → ∀ (f₀ : WO S T → ℂ) (T' : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)), IsPlaceModel ψ (symplO S T) (heisO ψ S T) (e + p.e) (stdHom S T) 1 f₀ T' → (∀ Φ', IsSBHalf (e + p.e) (stdHom S T) Φ' → IsThetaFunO ψ S T (T' Φ')) → (∀ Ψ ∈ SB (Matrix Y Y' k), IsSBHalf (e + p.e) (stdHom S T) (p.tensorAt FS FT Φ Ψ)) → p.IsModel ψ FS FT (T' ∘ₗ p.tensorL FS FT Φ) := by
  intro D k _ _ _ _ p ψ S T Y Y' _ _ _ _ FS FT e he Φ hΦ f₀ T' hP hθ hSB
  have hup : ∀ x, IsHalf (e + p.e) (p.up FS FT x) := fun x => half_sum he (Witness.up_half p FS FT x)
  refine ⟨fun Ψ => ?_, fun x Ψ Ψ' h => ?_, fun y hy Ψ Ψ' h => ?_⟩
  · exact hθ _ (hSB Ψ.1 Ψ.2)
  · have key : p.tensorAt FS FT Φ Ψ'.1 = fun t => p.tensorAt FS FT Φ Ψ.1 (t + p.up FS FT x) := by
      funext t
      simp only [Place.tensorAt]
      rw [Witness.down_add, Witness.down_up, Witness.up_add, h, add_sub_add_right_eq_sub]
    simp only [LinearMap.comp_apply, Place.tensorL_apply]
    rw [key]
    exact hP.trans _ (hSB Ψ.1 Ψ.2) _ (hup x)
  · have key : p.tensorAt FS FT Φ Ψ'.1 = fun t => ψ (symplO S T t y) * p.tensorAt FS FT Φ Ψ.1 t := by
      funext t
      simp only [Place.tensorAt]
      rw [h]
      by_cases h0 : Φ (t - p.up FS FT (p.down FS FT t)) = 0
      · rw [h0]; ring
      · have e1 : symplO S T t y = symplO S T (t - p.up FS FT (p.down FS FT t)) y +
            symplO S T (p.up FS FT (p.down FS FT t)) y := by
          rw [← symplO_add_left', sub_add_cancel]
        rw [e1, symplO_half_zero he (hΦ _ h0) hy, zero_add]
        ring
    simp only [LinearMap.comp_apply, Place.tensorL_apply]
    rw [key]
    exact hP.modul _ (hSB Ψ.1 Ψ.2) _ (half_sum_cA he hy)

end GlobalTheory.LocMod.TensorModel
end
