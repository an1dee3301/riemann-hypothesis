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
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsUnitHermOfDet
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.NonUnitalHom
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.RingTheory.Trace.Basic
public import Mathlib.RingTheory.Trace.Defs
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.LinearCombination.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Inv
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

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl.PhaseAdd

section Gen

variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem trace_sigR (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) (hσ : ∀ e, σ (σ e) = e)
    (z : R ⊗[F] E) :
    Algebra.trace R (R ⊗[F] E) (sigR R σ z) = Algebra.trace R (R ⊗[F] E) z := by
  let s : E ≃ₐ[F] E := AlgEquiv.ofAlgHom σ σ (AlgHom.ext hσ) (AlgHom.ext hσ)
  let e : (R ⊗[F] E) ≃ₐ[R] (R ⊗[F] E) := Algebra.TensorProduct.congr AlgEquiv.refl s
  have h : sigR R σ z = e z := by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a c => simp [sigR, e, s]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  rw [h]
  exact Algebra.trace_eq_of_algEquiv e z

theorem hR_add_left (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) {M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (x x' y : Fin M → R ⊗[F] E) :
    hR R σ J (x + x') y = hR R σ J x y + hR R σ J x' y := by
  simp only [hR, Formalism.UG.hform, Pi.add_apply, map_add (f := _), add_mul, Finset.sum_add_distrib]

theorem hR_add_right (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) {M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (x y y' : Fin M → R ⊗[F] E) :
    hR R σ J x (y + y') = hR R σ J x y + hR R σ J x y' := by
  simp only [hR, Formalism.UG.hform, Pi.add_apply, mul_add, Finset.sum_add_distrib]

end Gen

section Fin

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

theorem trace_gram2_swap (σ : E →ₐ[F] E) (hσ : ∀ e, σ (σ e) = e)
    {M n : ℕ} {J : Matrix (Fin M) (Fin M) E} (hJ : ∀ i j, σ (J j i) = J i j) (b : HermR (Af F) σ n)
    (X Y : Fin n → Fin M → Af F ⊗[F] E) :
    Algebra.trace (Af F) (Af F ⊗[F] E)
        (Matrix.trace ((b : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)) * gram2 σ J Y X)) =
      Algebra.trace (Af F) (Af F ⊗[F] E)
        (Matrix.trace ((b : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)) * gram2 σ J X Y)) := by
  rw [← trace_sigR (Af F) σ hσ]
  congr 1
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, map_sum, map_mul, gram2]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
  have hb : sigR (Af F) σ ((b : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)) c a) = (b : Matrix _ _ _) a c := b.2 a c
  rw [hb, GlobalTheory.CompanionTheory.SiegelND.Coef.sigR_hR (Af F) σ hσ hJ]

theorem gramR_add (σ : E →ₐ[F] E) {M n : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (X Y : Fin n → Fin M → Af F ⊗[F] E) :
    gramR (Af F) σ J (X + Y) = gramR (Af F) σ J X + gramR (Af F) σ J Y + gram2 σ J X Y + gram2 σ J Y X := by
  funext a c
  simp only [gramR, gram2, Pi.add_apply, Matrix.add_apply, hR_add_left, hR_add_right]
  abel

end Fin

theorem psiFin_add {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ) (u v : Af F) :
    psiFin F ψ (u + v) = psiFin F ψ u * psiFin F ψ v := by
  have h : pairA F 0 (u + v) = pairA F 0 u + pairA F 0 v := by
    have h0 : (0 : Ainf F) = 0 + 0 := (add_zero 0).symm
    exact congrArg (fun t => pairA F t (u + v)) h0
  simp only [psiFin]
  rw [h, AddChar.map_add_eq_mul]

theorem phaseB_add : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
    ∀ (n : ℕ) (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → ∀ (b : HermR (Af F) σ n)
    (X Y : Fin n → Fin M → Af F ⊗[F] E),
    phaseB σ J (psiFin F ψ) b (X + Y) =
      phaseB σ J (psiFin F ψ) b X * phaseB σ J (psiFin F ψ) b Y * pairB σ J (psiFin F ψ) b X Y := by
  intro F E _ _ _ _ _ σ hCM M J hJ n ψ _ b X Y
  have hsw := trace_gram2_swap σ (GlobalTheory.CompanionTheory.SiegelND.Coef.sig_invol hCM) hJ.1 b X Y
  have h2 : algebraMap F (Af F) (1 / 2) + algebraMap F (Af F) (1 / 2) = 1 := by
    rw [← map_add (f := _)]
    norm_num
  simp only [phaseB, pairB]
  rw [← psiFin_add, ← psiFin_add]
  congr 1
  rw [gramR_add, mul_add, mul_add, mul_add, Matrix.trace_add, Matrix.trace_add, Matrix.trace_add,
    map_add, map_add, map_add, hsw]
  linear_combination (Algebra.trace (Af F) (Af F ⊗[F] E)
    (Matrix.trace ((b : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)) * gram2 σ J X Y))) * h2

end GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl.PhaseAdd
