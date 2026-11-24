module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinDiv
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAddCharSymplecticLocalLatticeEqOne
public import Batteries.Classes.RatCast
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Int.Lemmas
public import Init.Data.Nat.Basic
public import Init.Data.Nat.Lemmas
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Ext
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.Algebra.Algebra.Prod
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.EuclideanDomain.Int
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Notation.Prod
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.Kleene
public import Mathlib.Algebra.Ring.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Equiv
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Pi
public import Mathlib.Algebra.Ring.Prod
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Int.Cast.Lemmas
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Rat.Cast.CharZero
public import Mathlib.Data.Rat.Cast.Defs
public import Mathlib.Data.Rat.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.FieldTheory.Perfect
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.DedekindDomain.Different
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.FractionalIdeal.Basic
public import Mathlib.RingTheory.FractionalIdeal.Operations
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Localization.Integer
public import Mathlib.RingTheory.PrincipalIdealDomain
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.Trace.Defs
public import Mathlib.Tactic.LinearCombination.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix nonZeroDivisors

noncomputable section
namespace GlobalTheory.FinSupp

theorem exists_den_of_trace_int (F : Type) [Field F] [NumberField F] :
    ∃ D : ℕ, 1 ≤ D ∧ ∀ t : F, (∀ a : 𝓞 F, ∃ m : ℤ, Algebra.trace ℚ F ((a : F) * t) = m) →
      IsIntegral ℤ ((D : F) * t) := by
  classical
  obtain ⟨c, hc, hfr⟩ := (FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 F)⁰ F)).2
  have hc0 : c ≠ 0 := nonZeroDivisors.ne_zero hc
  refine ⟨Ideal.absNorm (Ideal.span {c}), ?_, fun t ht => ?_⟩
  · rw [Nat.one_le_iff_ne_zero, Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
    exact hc0
  · have hmem : t ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 F)⁰ F) := by
      have h10 : (1 : FractionalIdeal (𝓞 F)⁰ F) ≠ 0 := by
        first | exact one_ne_zero | simp | exact FractionalIdeal.one_ne_zero
      rw [FractionalIdeal.mem_dual h10]
      intro a ha
      obtain ⟨b, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 ha
      obtain ⟨m, hm⟩ := ht b
      refine ⟨m, ?_⟩
      rw [Algebra.traceForm_apply, mul_comm, hm]
      simp
    obtain ⟨y, hy⟩ := hfr t hmem
    obtain ⟨e, he⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {c}))
    have : ((Ideal.absNorm (Ideal.span {c}) : ℕ) : F) * t = ((e * y : 𝓞 F) : F) := by
      have h1 : ((Ideal.absNorm (Ideal.span {c}) : ℕ) : F) = ((e : F) * (c : F)) := by
        have := congrArg (fun z : 𝓞 F => (z : F)) he
        simp only [map_mul, map_natCast] at this
        rw [← this]
      rw [h1, mul_assoc]
      have h2 : (y : F) = (c : F) * t := by
        rw [show (y : F) = algebraMap (𝓞 F) F y from rfl, hy, Algebra.smul_def]
      push_cast
      first | rw [h2] | rw [← h2] | exact congrArg (_ * ·) h2.symm | simp [h2]
    rw [this]
    exact (e * y).isIntegral_coe

theorem trace_int_of_finPart {F : Type} [Field F] [NumberField F] {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (s : F)
    (hs : ψ (finPart F (algebraMap F (AF F) s)) = 1) : ∃ m : ℤ, Algebra.trace ℚ F s = m := by
  set x : AF F := algebraMap F (AF F) s with hx
  set z : AF F := x - finPart F x with hzdef
  have hz : At (evI F) z := by
    intro u hu
    have hu1 : u.1 = 0 := by
      apply (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective
      rw [map_zero]
      exact hu
    show u * z = 0
    refine Prod.ext ?_ ?_
    · change u.1 * (x.1 - (0 : Ainf F)) = 0
      rw [hu1, zero_mul]
    · change u.2 * (x.2 - x.2) = 0
      rw [sub_self, mul_zero]
  have hψz : ψ z = 1 := by
    have h := hψ.2.1 s
    rw [← hx, show x = z + finPart F x by rw [hzdef, sub_add_cancel], AddChar.map_add_eq_mul, hs, mul_one] at h
    exact h
  have hev : evI F z = mixedEmbedding F s := by
    show InfiniteAdeleRing.ringEquiv_mixedSpace F (x.1 - 0) = _
    rw [sub_zero, InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp]
    rfl
  have h := hψ.2.2 z hz
  rw [hψz, hev, GlobalTheory.LatVacArith.trace_mixedEmbedding] at h
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.1 h.symm
  have hne : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have hq : (((Algebra.trace ℚ F s : ℚ) : ℝ) : ℂ) = -(n : ℂ) := by
    apply mul_right_cancel₀ hne
    linear_combination -hn
  refine ⟨-n, ?_⟩
  push_cast
  exact_mod_cast hq

end GlobalTheory.FinSupp

namespace GlobalTheory.FinSupp.DenStd

theorem exists_den : ∀ (F : Type) [Field F] [NumberField F], ∃ D : ℕ, 1 ≤ D ∧ ∀ ψ : AddChar (AF F) ℂ, IsStd ψ → ∀ t : F,
    (∀ a : 𝓞 F, ψ (GlobalTheory.FinSupp.finPart F (algebraMap F (AF F) ((a : F) * t))) = 1) → IsIntegral ℤ ((D : F) * t) := by
  intro F _ _
  obtain ⟨D, hD, hint⟩ := GlobalTheory.FinSupp.exists_den_of_trace_int F
  exact ⟨D, hD, fun ψ hψ t ht => hint t fun a => GlobalTheory.FinSupp.trace_int_of_finPart hψ _ (ht a)⟩

end GlobalTheory.FinSupp.DenStd
