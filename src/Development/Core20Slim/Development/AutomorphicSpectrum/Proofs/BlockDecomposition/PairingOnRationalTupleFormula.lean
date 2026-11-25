module

public import Mathlib
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaPartD
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBoundUnitary
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermInf
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermOf
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.FiniteAdeleTopologyStatement
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RatTuple
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.GlobalProofs.SchwartzBruhatEqSumPure
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.GlobalProofs.AdelicCharacterArchimedeanFormStatement
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.StandardAdelicCharacterStatement
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.InfiniteAdeleHaarMapEqScaledVolumeStatement
public import Formalism.SatakeDualWeyl.Statement
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.ByCases
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.IsEmpty.Defs
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
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Trace.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ GlobalTheory.CompanionTheory.SiegelND.Integ.Hua
open NumberField
open GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl GlobalTheory.CompanionTheory.SW.Core

noncomputable section
namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl.PairSingle

theorem pair_single : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
    ∀ (n : ℕ) (ψf : Af F → ℂ) (c : hermE σ n) (c₀ : Fin n) (i₀ : Fin M) (x : Af F ⊗[F] E) (s : ℕ)
      (ρ : Fin M → Fin n → 𝓞 E),
    pairB σ J ψf (hermIn (Af F) σ n c) (fun a i => if a = c₀ ∧ i = i₀ then x else 0) (ratTuple J s ρ) =
      ψf (Algebra.trace (Af F) (Af F ⊗[F] E) (sigR (Af F) σ x * inclR (Af F)
        ((s : E) * ∑ a, c.1 a c₀ * algebraMap (𝓞 E) E (ρ i₀ a)))) := by
  intro F E _ _ _ _ _ σ M J hJ n ψf c c₀ i₀ x s ρ
  have hdet : IsUnit J.det := isUnit_iff_ne_zero.mpr hJ.2
  have key : ∀ a, hR (Af F) σ J (fun i => if i = i₀ then x else 0) (ratTuple J s ρ a) =
      sigR (Af F) σ x * inclR (Af F) ((s : E) * algebraMap (𝓞 E) E (ρ i₀ a)) := by
    intro a
    have hv : ∑ j, J i₀ j * (J⁻¹ *ᵥ fun i => algebraMap (𝓞 E) E (ρ i a)) j
        = algebraMap (𝓞 E) E (ρ i₀ a) := by
      have h1 : (J *ᵥ (J⁻¹ *ᵥ fun i => algebraMap (𝓞 E) E (ρ i a))) i₀ =
          algebraMap (𝓞 E) E (ρ i₀ a) := by
        rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
      simpa [Matrix.mulVec, dotProduct] using h1
    unfold hR Formalism.UG.hform
    rw [Finset.sum_eq_single i₀]
    · simp only [if_true, JR, ratTuple, Matrix.map_apply]
      rw [← hv]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_mul, map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    · intro i _ hi
      simp [hi]
    · simp
  have hz : ∀ (c' : Fin n) (a : Fin n), c' ≠ c₀ →
      hR (Af F) σ J (fun i => if c' = c₀ ∧ i = i₀ then x else 0) (ratTuple J s ρ a) = 0 := by
    intro c' a hc
    simp [hR, Formalism.UG.hform, hc]
  have hin : ∀ a b, ((hermIn (Af F) σ n c : HermR (Af F) σ n) :
      Matrix (Fin n) (Fin n) (Af F ⊗[F] E)) a b = inclR (Af F) (c.1 a b) := fun a b => rfl
  have htr : Matrix.trace (((hermIn (Af F) σ n c : HermR (Af F) σ n) :
      Matrix (Fin n) (Fin n) (Af F ⊗[F] E)) *
        gram2 σ J (fun a i => if a = c₀ ∧ i = i₀ then x else 0) (ratTuple J s ρ)) =
      sigR (Af F) σ x * inclR (Af F)
        ((s : E) * ∑ a, c.1 a c₀ * algebraMap (𝓞 E) E (ρ i₀ a)) := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, hin, gram2]
    have h2 : ∀ a, ∑ c', inclR (Af F) (c.1 a c') *
        hR (Af F) σ J (fun i => if c' = c₀ ∧ i = i₀ then x else 0) (ratTuple J s ρ a) =
        inclR (Af F) (c.1 a c₀) *
          (sigR (Af F) σ x * inclR (Af F) ((s : E) * algebraMap (𝓞 E) E (ρ i₀ a))) := by
      intro a
      rw [Finset.sum_eq_single c₀]
      · simp only [true_and]
        rw [key a]
      · intro c' _ hc
        rw [hz c' a hc, mul_zero]
      · simp
    simp only [h2]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Finset.mul_sum, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [map_mul]
    ring
  unfold pairB
  rw [htr]

end GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl.PairSingle
