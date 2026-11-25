module

public import Mathlib
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCovolOne
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HypOneZeroZero
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TrMMemFramesEIff
public import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import Init.Core
public import Init.Data.Fin.Basic
public import Init.Data.Fin.Lemmas
public import Init.Data.Nat.Basic
public import Init.Data.Nat.Lemmas
public import Init.Data.NeZero
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Torsion.Pi
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Basic.Unique
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.ZMod.Defs
public import Mathlib.LinearAlgebra.LinearIndependent.Basic
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TotallySplit

@[expose] public section

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.HypStep

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free

theorem hypOne_mul_hypOne_of_mul_eq_one {K : Type} [Field K] {M : ℕ} {A B : Matrix (Fin M) (Fin M) K}
    (h : A * B = 1) : hypOne A * hypOne B = 1 := by
  ext i j
  rw [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_succ]
  refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun i => ?_) i) i <;>
    refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => ?_) j) j
  all_goals
    simp [hypOne_zero_zero, hypOne_zero_one, hypOne_one_zero, hypOne_one_one, hypOne_zero_rest,
      hypOne_one_rest, hypOne_rest_zero, hypOne_rest_one, hypOne_rest_rest, Matrix.one_apply,
      ← Matrix.mul_apply, h, Fin.ext_iff]

theorem isHermND_hypOne {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ}
    {J : Matrix (Fin M) (Fin M) E} (hJ : IsHermND σ J) : IsHermND σ (hypOne J) := by
  refine ⟨fun i j => ?_, ?_⟩
  · refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun i => ?_) i) i <;>
      refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => ?_) j) j
    all_goals first
      | exact hJ.1 i j
      | simp [hypOne_zero_zero, hypOne_zero_one, hypOne_one_zero, hypOne_one_one, hypOne_zero_rest,
          hypOne_one_rest, hypOne_rest_zero, hypOne_rest_one]
  · have hu : IsUnit J.det := isUnit_iff_ne_zero.mpr hJ.2
    have h1 : hypOne J * hypOne J⁻¹ = 1 :=
      hypOne_mul_hypOne_of_mul_eq_one (Matrix.mul_nonsing_inv J hu)
    intro h0
    have h2 := congrArg Matrix.det h1
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at h2
    exact zero_ne_one h2

theorem e0_mem_framesE {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) :
    e0 E M ∈ framesE σ (hypOne J) (0 : Matrix (Fin 1) (Fin 1) E) := by
  refine ⟨linearIndependent_unique_iff.2 ?_, ?_⟩
  · intro h
    have := congrFun h 0
    simp [e0] at this
  · ext a b
    simp [gramE, hE, hform, e0, Fin.sum_univ_succ, hypOne_zero_zero]

theorem hypOne_isHermND_and_e0_mem (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E) (_hσ : IsCMExt F E σ) (M : ℕ) (J : Matrix (Fin M) (Fin M) E)
    (hJ : IsHermND σ J) :
    IsHermND σ (hypOne J) ∧ e0 E M ∈ framesE σ (hypOne J) (0 : Matrix (Fin 1) (Fin 1) E) :=
  ⟨isHermND_hypOne σ hJ, e0_mem_framesE σ J⟩

end GlobalTheory.CompanionTheory.WeilSiegel.HypStep
