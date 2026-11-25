module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FlatSpaceComponents
public import Batteries.Logic
public import Formalism.FrobeniusOrbits.Statement
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataKernels
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ZsmulGeneratorEqZeroOfProjection
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Fin.Basic
public import Init.Data.Int.Basic
public import Init.Data.Int.DivMod.Basic
public import Init.Data.Int.DivMod.Bootstrap
public import Init.Data.Int.Lemmas
public import Init.Data.Int.Order
public import Init.Data.List.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Omega.Coeffs
public import Init.Omega.Constraint
public import Init.Omega.Int
public import Init.Omega.LinearCombo
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
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Group.Even
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.GroupWithZero.Units.Lemmas
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Notation.Prod
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.Rat.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.FieldTheory.Separable
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.LinearAlgebra.SesquilinearForm.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.CMField
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Tactic.FieldSimp.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain
open scoped nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Proof.normLineDecompositionsOfBaseSpace_proof

open GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents

theorem star_eq_conj (D : D7) (x : D.host.E) : star x = D.host.conj x := by
  have := D.host.der.cm
  obtain ⟨ψ⟩ := (inferInstance : Nonempty (D.host.E →+* ℂ))
  have hc : ∀ y, ψ (D.host.conj y) = starRingEnd ℂ (ψ y) :=
    (D.host.der.conj_iff ψ D.host.conj).2 (MulEquiv.apply_symm_apply _ _)
  apply ψ.injective
  rw [hc]
  exact NumberField.IsCMField.complexEmbedding_complexConj _ ψ x

theorem hT_zero_symm {E : Type} [Field E] [NumberField E] [StarRing E] (S : HSpace E) {x y : S.V}
    (h : S.hT x y = 0) : S.hT y x = 0 := by
  rw [← S.herm.eq x y, h, map_zero]

theorem isDec_smul (D : D7) (t : D.host.E) :
    IsDec (D.sp.Y 0) (D.sp.X 0) (D.sp.iXY 0) (fun _ : Fin 1 => t • D.sp.zm)
      (-(t * star t * ((D.mem D.u₀).A.T : D.host.E))) D.sp.hypE D.sp.hypF := by
  have hm : 0 < D.R.m := by have := D.R.two_le_m; omega
  have hsym : ∀ a b : (D.sp.Y 0).V, (D.sp.Y 0).hT a b = 0 → (D.sp.Y 0).hT b a = 0 :=
    fun a b h => hT_zero_symm (D.sp.Y 0) h
  refine
    { isom := D.sp.iXY_isom 0 hm
      a_le := le_rfl
      rank := ?_
      z_norm := ?_
      z_X := ?_
      ee := ?_
      ff := ?_
      ef := ?_
      hyp_X := ?_
      hyperbolicDecomp_hyp_orthogonal_line := ?_ }
  · rw [D.sp.Y_rank 0 (Nat.zero_le _), D.sp.X_rank 0 (Nat.zero_le _)]
    obtain ⟨j, hj⟩ := D.R.m_even
    simp only [Formalism.BasicNotions.Ranks.rankY, Formalism.BasicNotions.Ranks.N, Formalism.BasicNotions.Ranks.r, Formalism.BasicNotions.Ranks.rS]
    omega
  · intro i
    simp only [HSpace.hD, LinearMap.map_smulₛₗ₂, map_smul, D.sp.zm_norm, starRingEnd_apply, smul_eq_mul,
      D.sp_T]
    ring
  · intro i x
    simp only [HSpace.hD, LinearMap.map_smulₛₗ₂, hsym _ _ (D.sp.zm_orth x), smul_zero]
  · intro i j
    exact D.sp.hyp_ee j i
  · intro i j
    exact D.sp.hyp_ff j i
  · intro i j
    simp only [HSpace.hD]
    rw [← (D.sp.Y 0).herm.eq (D.sp.hypE i) (D.sp.hypF j), D.sp.hyp_ef]
    split_ifs <;> simp
  · intro i x
    exact ⟨hsym _ _ (D.sp.hyp_orthX i x).1, hsym _ _ (D.sp.hyp_orthX i x).2⟩
  · intro i j
    simp only [HSpace.hD, map_smul, hsym _ _ (D.sp.hyp_orthz i).1, hsym _ _ (D.sp.hyp_orthz i).2, smul_zero,
      and_self]

theorem recordDec (D : D7) : RecordDecSt D := by
  refine ⟨fun u => ?_, ?_⟩
  · have hc0 := D.cOf_ne u
    have hc1 : D.host.conj (D.cOf u) ≠ 0 := (map_ne_zero _).2 hc0
    have h := isDec_smul D (D.cOf u)⁻¹
    have hs : -((D.cOf u)⁻¹ * star (D.cOf u)⁻¹ * ((D.mem D.u₀).A.T : D.host.E)) = -Tu D u := by
      rw [star_inv₀, star_eq_conj, ← D.cOf_eq u]
      field_simp
    rw [hs] at h
    exact h
  · obtain ⟨π, -, hπ, -⟩ := D.T_norm D.u₀
    have hT : ((D.mem D.u₀).A.T : D.host.E) ≠ 0 := by
      rw [← D.sp_T]
      exact_mod_cast D.sp.T_prime.ne_zero
    have hπ0 : (π : D.host.E) ≠ 0 := by
      rintro h0
      rw [h0, zero_mul] at hπ
      exact hT hπ.symm
    have hπ1 : D.host.conj (π : D.host.E) ≠ 0 := (map_ne_zero _).2 hπ0
    refine ⟨(π : D.host.E)⁻¹ • D.sp.zm, ?_⟩
    have h := isDec_smul D (π : D.host.E)⁻¹
    have hs : -((π : D.host.E)⁻¹ * star (π : D.host.E)⁻¹ * ((D.mem D.u₀).A.T : D.host.E)) = -1 := by
      rw [star_inv₀, star_eq_conj, ← hπ]
      field_simp
    rw [hs] at h
    exact h

end GlobalTheory.Proof.normLineDecompositionsOfBaseSpace_proof
