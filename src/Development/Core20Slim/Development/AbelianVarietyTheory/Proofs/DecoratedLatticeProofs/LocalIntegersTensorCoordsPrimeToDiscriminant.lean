module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SigV
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EqIdOfIsUnramifiedAt
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DisjointSpanPerpLat
public import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FiniteResidueFieldAdicCompletionIntegers
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Order.Lemmas
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.NonUnitalHom
public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Subsemigroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.Algebra.Order.ZeroLEOne
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Degree.Operations
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Cast.Order.Basic
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Lattice.Nat
public import Mathlib.Order.RelClasses
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.Tactic.ComputeDegree
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl IsDedekindDomain NumberField GlobalTheory.FixedUnitNorm
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.FixedUnitNorm.Coords

section Field

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E}

theorem isIntegral_of_trace_norm (w : E) (t n : 𝓞 F) (ht : w + σ w = algebraMap F E t)
    (hn : w * σ w = algebraMap F E n) : IsIntegral ℤ w := by
  have hE : IsIntegral (𝓞 E) w := by
    refine ⟨Polynomial.X ^ 2 - Polynomial.C (algebraMap (𝓞 F) (𝓞 E) t) * Polynomial.X +
      Polynomial.C (algebraMap (𝓞 F) (𝓞 E) n), by monicity!, ?_⟩
    have h1 : algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) t) = algebraMap F E t := rfl
    have h2 : algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) n) = algebraMap F E n := rfl
    simp only [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_pow,
      Polynomial.eval₂_X, Polynomial.eval₂_C, h1, h2, ← ht, ← hn]
    ring
  exact isIntegral_trans (R := ℤ) w hE

theorem exists_coords (h : IsCMExt F E σ) (w : E) (t n : 𝓞 F) (ht : w + σ w = algebraMap F E t)
    (hn : w * σ w = algebraMap F E n) (x : 𝓞 E) :
    ∃ a b : 𝓞 F, (x : E) * algebraMap F E ((t ^ 2 - 4 * n : 𝓞 F) : F) =
      algebraMap F E a + algebraMap F E b * w := by
  have hσ := GlobalTheory.SelfDualLatticeCompare.conj_conj h
  let W : 𝓞 E := ⟨w, isIntegral_of_trace_norm w t n ht hn⟩
  let s : 𝓞 E →+* 𝓞 E := RingOfIntegers.mapRingHom (σ : E →+* E)
  have hs : ∀ y : 𝓞 E, ((s y : 𝓞 E) : E) = σ y := fun _ => rfl
  have hW : ((W : 𝓞 E) : E) = w := rfl
  obtain ⟨a, ha⟩ := GlobalTheory.UnramifiedDiscriminant.exists_int_of_conj_eq h
    ((s x * W - x * s W) * (W - s W)) (by
      change σ ((σ (x : E) * w - (x : E) * σ w) * (w - σ w)) = (σ (x : E) * w - (x : E) * σ w) * (w - σ w)
      simp only [map_mul, map_sub, hσ]
      ring)
  obtain ⟨b, hb⟩ := GlobalTheory.UnramifiedDiscriminant.exists_int_of_conj_eq h
    ((x - s x) * (W - s W)) (by
      change σ (((x : E) - σ x) * (w - σ w)) = ((x : E) - σ x) * (w - σ w)
      simp only [map_mul, map_sub, hσ]
      ring)
  have ha' : algebraMap F E a = (σ x * w - x * σ w) * (w - σ w) := by
    exact congrArg (algebraMap (𝓞 E) E) ha
  have hb' : algebraMap F E b = (x - σ x) * (w - σ w) := by
    exact congrArg (algebraMap (𝓞 E) E) hb
  refine ⟨a, b, ?_⟩
  have hd : algebraMap F E ((t ^ 2 - 4 * n : 𝓞 F) : F) = (algebraMap F E t) ^ 2 - 4 * algebraMap F E n := by
    push_cast
    simp [map_sub, map_pow, map_mul, map_ofNat]
  rw [hd, ha', hb', ← ht, ← hn]
  ring

theorem tmul_move {K : Type} [Field K] [Algebra F K] (m : K) (r : F) (e : E) :
    (algebraMap F K r * m) ⊗ₜ[F] e = m ⊗ₜ[F] (algebraMap F E r * e) := by
  rw [← Algebra.smul_def, ← Algebra.smul_def, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]

theorem coords_add {K : Type} [Field K] [Algebra F K] (a b a' b' : K) (w : E) :
    (a ⊗ₜ[F] (1 : E) + b ⊗ₜ[F] w) + (a' ⊗ₜ[F] (1 : E) + b' ⊗ₜ[F] w) = (a + a') ⊗ₜ[F] (1 : E) + (b + b') ⊗ₜ[F] w := by
  rw [TensorProduct.add_tmul, TensorProduct.add_tmul, add_add_add_comm]

theorem coords_neg {K : Type} [Field K] [Algebra F K] (a b : K) (w : E) :
    -(a ⊗ₜ[F] (1 : E) + b ⊗ₜ[F] w) = (-a) ⊗ₜ[F] (1 : E) + (-b) ⊗ₜ[F] w := by
  rw [TensorProduct.neg_tmul, TensorProduct.neg_tmul, neg_add]

end Field

end GlobalTheory.FixedUnitNorm.Coords

namespace GlobalTheory.FixedUnitNorm.Coords


set_option maxHeartbeats 1000000 in
theorem mem_intV_coords : ∀ (D : D7) (v : Pl D) (w : D.host.E) (t n : 𝓞 D.host.F),
    w + D.sp.cm.sig w = algebraMap D.host.F D.host.E t → w * D.sp.cm.sig w = algebraMap D.host.F D.host.E n →
    t ^ 2 - 4 * n ∉ v.asIdeal → ∀ z ∈ intV D v, ∃ a ∈ v.adicCompletionIntegers D.host.F,
      ∃ b ∈ v.adicCompletionIntegers D.host.F, z = a ⊗ₜ[D.host.F] (1 : D.host.E) + b ⊗ₜ[D.host.F] w := by
  intro D v w t n ht hn hv z hz
  have hcm := GlobalTheory.AdelicU.isCMExt_host D
  have hcoe : ∀ r : 𝓞 D.host.F, ((algebraMap (𝓞 D.host.F) (v.adicCompletionIntegers D.host.F) r :
      v.adicCompletionIntegers D.host.F) : Fv D.host.F v) = algebraMap D.host.F (Fv D.host.F v) (r : D.host.F) :=
    fun r => rfl
  have hmem : ∀ r : 𝓞 D.host.F, algebraMap D.host.F (Fv D.host.F v) (r : D.host.F) ∈
      v.adicCompletionIntegers D.host.F := fun r => hcoe r ▸ (algebraMap (𝓞 D.host.F) (v.adicCompletionIntegers D.host.F) r).2
  obtain ⟨u, hu⟩ := ((GlobalTheory.SelfDualGenus.isUnit_algebraMap_iff v (t ^ 2 - 4 * n)).2 hv).exists_left_inv
  set U : Fv D.host.F v := ((u : v.adicCompletionIntegers D.host.F) : Fv D.host.F v) with hU
  have hu' : U * algebraMap D.host.F (Fv D.host.F v) ((t ^ 2 - 4 * n : 𝓞 D.host.F) : D.host.F) = 1 := by
    have := congrArg (fun y : v.adicCompletionIntegers D.host.F => (y : Fv D.host.F v)) hu
    rw [MulMemClass.coe_mul, hcoe, OneMemClass.coe_one] at this
    exact this
  induction hz using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨c, hc, x, rfl⟩ := hy
    obtain ⟨a, b, hab⟩ := exists_coords hcm w t n ht hn x
    refine ⟨c * U * algebraMap D.host.F (Fv D.host.F v) (a : D.host.F), mul_mem (mul_mem hc u.2) (hmem a),
      c * U * algebraMap D.host.F (Fv D.host.F v) (b : D.host.F), mul_mem (mul_mem hc u.2) (hmem b), ?_⟩
    have hc' : c = algebraMap D.host.F (Fv D.host.F v) ((t ^ 2 - 4 * n : 𝓞 D.host.F) : D.host.F) * (c * U) := by
      rw [mul_comm, mul_assoc, hu', mul_one]
    calc c ⊗ₜ[D.host.F] (x : D.host.E)
        = (algebraMap D.host.F (Fv D.host.F v) ((t ^ 2 - 4 * n : 𝓞 D.host.F) : D.host.F) * (c * U)) ⊗ₜ[D.host.F]
            (x : D.host.E) := by rw [← hc']
      _ = (c * U) ⊗ₜ[D.host.F] (algebraMap D.host.F D.host.E ((t ^ 2 - 4 * n : 𝓞 D.host.F) : D.host.F) * x) :=
          tmul_move _ _ _
      _ = (c * U) ⊗ₜ[D.host.F] (algebraMap D.host.F D.host.E (a : D.host.F) * 1 +
            algebraMap D.host.F D.host.E (b : D.host.F) * w) := by rw [mul_comm (algebraMap D.host.F D.host.E _) (x : D.host.E), hab, mul_one]
      _ = (algebraMap D.host.F (Fv D.host.F v) (a : D.host.F) * (c * U)) ⊗ₜ[D.host.F] (1 : D.host.E) +
            (algebraMap D.host.F (Fv D.host.F v) (b : D.host.F) * (c * U)) ⊗ₜ[D.host.F] w := by
          rw [TensorProduct.tmul_add, tmul_move, tmul_move]
      _ = _ := by rw [mul_comm (algebraMap D.host.F (Fv D.host.F v) (a : D.host.F)),
            mul_comm (algebraMap D.host.F (Fv D.host.F v) (b : D.host.F))]
  | zero => exact ⟨0, zero_mem _, 0, zero_mem _, by simp⟩
  | add y y' _ _ h h' =>
    obtain ⟨a, ha, b, hb, rfl⟩ := h
    obtain ⟨a', ha', b', hb', rfl⟩ := h'
    refine ⟨a + a', add_mem ha ha', b + b', add_mem hb hb', ?_⟩
    exact coords_add a b a' b' w
  | neg y _ h =>
    obtain ⟨a, ha, b, hb, rfl⟩ := h
    refine ⟨-a, neg_mem ha, -b, neg_mem hb, ?_⟩
    exact coords_neg a b w

end GlobalTheory.FixedUnitNorm.Coords
