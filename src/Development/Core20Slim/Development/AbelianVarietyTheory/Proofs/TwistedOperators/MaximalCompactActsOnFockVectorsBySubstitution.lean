module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockPolynomialVectorMaximalCompactMovedBasesStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OmPureTensorOOfFinite
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.PureTensorLIntertwine
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrictedTensorBasePointNormSq
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIntOv
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HalfLinearCocycle
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Classical
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Int.Order
public import Init.Data.Zero
public import Init.Omega.Coeffs
public import Init.Omega.Constraint
public import Init.Omega.Int
public import Init.Omega.LinearCombo
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FockCompact

theorem det_isUnit_of_onb {k : ℕ} {G s B : Matrix (Fin k) (Fin k) ℂ} {p : ℕ}
    (h : Formalism.IndefR.Datum.IsONBasis G s B p) : IsUnit B.det := by
  obtain ⟨ε, hε, hB, -⟩ := h
  have hd : (Bᴴ * G * B).det ≠ 0 := by
    rw [hB, Matrix.det_diagonal]
    refine Finset.prod_ne_zero_iff.mpr fun a _ => ?_
    rcases hε a with ⟨h1, -⟩ | ⟨h1, -⟩ <;> simp [h1]
  rw [Matrix.det_mul] at hd
  exact isUnit_iff_ne_zero.mpr (right_ne_zero_of_mul hd)

theorem comm_of_onb {k : ℕ} {G s B κ : Matrix (Fin k) (Fin k) ℂ} {p : ℕ}
    (h : Formalism.IndefR.Datum.IsONBasis G s B p) (hκ : IsKMat p κ) : s * (B * κ * B⁻¹) = B * κ * B⁻¹ * s := by
  have hu := det_isUnit_of_onb h
  obtain ⟨ε, hε, -, hs⟩ := h
  obtain ⟨-, hκ0⟩ := hκ
  have hBi : B * B⁻¹ = 1 := Matrix.mul_nonsing_inv B hu
  have hiB : B⁻¹ * B = 1 := Matrix.nonsing_inv_mul B hu
  have hcomm : (diagonal fun a => (ε a : ℂ)) * κ = κ * diagonal fun a => (ε a : ℂ) := by
    ext i j
    rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
    by_cases hij : (i.val < p ↔ j.val < p)
    · have hij' : ε i = ε j := by
        rcases hε i with ⟨hi1, hi2⟩ | ⟨hi1, hi2⟩ <;> rcases hε j with ⟨hj1, hj2⟩ | ⟨hj1, hj2⟩
        · rw [hi1, hj1]
        · exact absurd (hij.mp hi2) (by omega)
        · exact absurd (hij.mpr hj2) (by omega)
        · rw [hi1, hj1]
      rw [hij', mul_comm]
    · rw [hκ0 i j hij, mul_zero, zero_mul]
  have hs' : s = B * (diagonal fun a => (ε a : ℂ)) * B⁻¹ := by
    calc s = s * (B * B⁻¹) := by rw [hBi, mul_one]
      _ = B * (diagonal fun a => (ε a : ℂ)) * B⁻¹ := by rw [← mul_assoc, hs]
  rw [hs']
  simp only [mul_assoc]
  rw [← mul_assoc B⁻¹ B, hiB, one_mul, ← mul_assoc B⁻¹ B, hiB, one_mul, ← mul_assoc _ κ, hcomm, mul_assoc κ]

theorem compAt_of_atTau {D : D7} {θ : InfFam D} {S : HSp D} {τ : D.what₂.Tau}
    {M : Matrix (Fin S.rank) (Fin S.rank) ℂ} {g : GA D S} (h : IsAtTau θ S τ M g) :
    compAt θ τ (Formalism.L2.Theta.mt S g) = M ∧ ∀ ρ, ρ ≠ τ → compAt θ ρ (Formalism.L2.Theta.mt S g) = 1 := by
  obtain ⟨-, h1, h2⟩ := h
  refine ⟨Eq.trans ?_ h1, fun ρ hρ => Eq.trans ?_ (h2 ρ hρ)⟩
  · rfl
  · rfl

theorem om_pureTensorO_compact : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : OmT S T), IsWeilDatumO ψ S T χS χT om → IsInfFam θ → ∀ (sS BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (pS pT : D.what₂.Tau → ℕ), (∀ ρ, pS ρ ≤ S.rank) → (∀ ρ, pT ρ ≤ T.rank) → (∀ ρ, IsCartanInv (gramAt D S ρ) (sS ρ)) → (∀ ρ, IsCartanInv (gramAt D T ρ) (sT ρ)) → (∀ ρ, IsONBasis (gramAt D S ρ) (sS ρ) (BS ρ) (pS ρ)) → (∀ ρ, IsONBasis (gramAt D T ρ) (sT ρ) (BT ρ) (pT ρ)) → ∀ f, IsThetaFunO ψ S T f → ∀ (τ : D.what₂.Tau) κS κT, IsKMat (pS τ) κS → IsKMat (pT τ) κT → ∀ g h, IsAtTau θ S τ (BS τ * κS * (BS τ)⁻¹) g → IsAtTau θ T τ (BT τ * κT * (BT τ)⁻¹) h → ∀ c : ℂ, om (g, h) f = c • f → ∀ P, om (g, h) (pureTensorO ψ θ S T sS sT BS BT f P) = c • pureTensorO ψ θ S T sS sT BS BT f (fockSub τ (pS τ) (pT τ) κS κT P) := by
  intro D ψ θ S T χS χT om hW hθ sS BS sT BT pS pT hpS hpT hcS hcT hoS hoT f hf τ κS κT hκS hκT g h hg hh c hc P
  have hstd : IsStdChar D ψ (-1) := hW.std
  obtain ⟨hgτ, hgρ⟩ := compAt_of_atTau hg
  obtain ⟨hhτ, hhρ⟩ := compAt_of_atTau hh
  have hcomS : ∀ ρ, sS ρ * compAt θ ρ (Formalism.L2.Theta.mt S g) = compAt θ ρ (Formalism.L2.Theta.mt S g) * sS ρ := by
    intro ρ
    by_cases hρ : ρ = τ
    · subst hρ
      rw [hgτ]
      exact comm_of_onb (hoS ρ) hκS
    · rw [hgρ ρ hρ, mul_one, one_mul]
  have hcomT : ∀ ρ, sT ρ * compAt θ ρ (Formalism.L2.Theta.mt T h) = compAt θ ρ (Formalism.L2.Theta.mt T h) * sT ρ := by
    intro ρ
    by_cases hρ : ρ = τ
    · subst hρ
      rw [hhτ]
      exact comm_of_onb (hoT ρ) hκT
    · rw [hhρ ρ hρ, mul_one, one_mul]
  have key := (GlobalTheory.OrientedHeis.om_pureTensorO D ψ θ S T χS χT om hW hθ sS sS BS
    (fun ρ => compAt θ ρ (Formalism.L2.Theta.mt S g) * BS ρ) sT sT BT
    (fun ρ => compAt θ ρ (Formalism.L2.Theta.mt T h) * BT ρ) g h hcomS hcomT (fun _ => rfl) (fun _ => rfl) f hf P).2
  rw [key, hc, GlobalTheory.FiniteFock.pureTensorO_smul]
  have e2 := GlobalTheory.T.fockPolynomialVector_maximalCompact_moved_bases D ψ θ S T hstd hθ sS BS sT BT pS pT hpS hpT hcS hcT hoS hoT f hf τ κS κT hκS hκT
    (fun ρ => compAt θ ρ (Formalism.L2.Theta.mt S g) * BS ρ) (fun ρ => compAt θ ρ (Formalism.L2.Theta.mt T h) * BT ρ) ?_ ?_ ?_ P
  · rw [e2]
  · show compAt θ τ (Formalism.L2.Theta.mt S g) * BS τ = BS τ * κS
    rw [hgτ, mul_assoc, Matrix.nonsing_inv_mul _ (det_isUnit_of_onb (hoS τ)), mul_one]
  · show compAt θ τ (Formalism.L2.Theta.mt T h) * BT τ = BT τ * κT
    rw [hhτ, mul_assoc, Matrix.nonsing_inv_mul _ (det_isUnit_of_onb (hoT τ)), mul_one]
  · intro ρ hρ
    refine ⟨?_, ?_⟩
    · show compAt θ ρ (Formalism.L2.Theta.mt S g) * BS ρ = BS ρ
      rw [hgρ ρ hρ, one_mul]
    · show compAt θ ρ (Formalism.L2.Theta.mt T h) * BT ρ = BT ρ
      rw [hhρ ρ hρ, one_mul]

end GlobalTheory.FockCompact
