module

public import Mathlib
public import Formalism.LocalRingCardinality.DataKerI
public import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
public import Formalism.LocalToGlobal.KernelLattices.LateralTheory
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ProjectiveOfFg
public import Development.Core20Slim.Development.AbelianVarietyTheory.BlockTheory.JetGauges.ThetaSpanAdjoint
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsMulMemOfMemSpan
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.ProjectiveLattices.PartitionExtendByZeroAntitone
public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Function
public import Init.Data.Nat.Basic
public import Init.Data.Nat.Coprime
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.PropLemmas
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Subsemigroup.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.ZeroLEOne
public import Mathlib.Algebra.Quotient
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Algebra.Star.BigOperators
public import Mathlib.Algebra.Star.Unitary
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Rat.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.FieldTheory.Separable
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Quotient.Defs
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.CMField
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.Unramified.Basic

@[expose] public section

set_option autoImplicit false

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric NumberField
open scoped Matrix

namespace GlobalTheory.RepEqAt

section General

open Formalism.L2.Pj GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {N : ℕ}

theorem exists_triv (hur : Algebra.Unramified (𝓞 (maximalRealSubfield E)) (𝓞 E)) {n : ℕ} (hn : 0 < n)
    (Λ : GenLat E N) (hU : Λ.Unimod) :
    ∃ γ : Matrix (Fin N) (Fin N) E, IsUnitaryM γ ∧ ∃ k : ℕ, Nat.Coprime k n ∧
      (∀ v ∈ Λ.La, k • (γ *ᵥ v) ∈ Formalism.L2.Pj.stdLat E N) ∧
      ∀ x ∈ Formalism.L2.Pj.stdLat E N, ∃ v ∈ Λ.La, γ *ᵥ v = k • x := by
  have hsub : ∀ a b : 𝓞 E ⧸ Ideal.span {((1 : ℕ) : 𝓞 E)}, a = b := fun a b => by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    exact Ideal.Quotient.eq.2 (Ideal.mem_span_singleton'.2 ⟨a - b, by simp⟩)
  have hiso : IsIsomMod Λ 1 0 := by
    refine ⟨fun y => ⟨0, funext fun j => hsub _ _⟩, fun v => ⟨fun _ => ⟨v, v.2, by simp⟩, fun _ => rfl⟩,
      fun v w x y _ _ => ?_⟩
    obtain ⟨a, ha⟩ := (hU w).1 w.2 v v.2
    refine ⟨a - ∑ j, x j * IsCMField.ringOfIntegersComplexConj E (y j), ?_⟩
    have e1 : ∑ j, (v : Fin N → E) j * IsCMField.complexConj E ((w : Fin N → E) j) = (a : E) := by
      refine Eq.trans ?_ ha.symm
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    have e2 : ∑ j, (x j : E) * IsCMField.complexConj E (y j : E) =
        ((∑ j, x j * IsCMField.ringOfIntegersComplexConj E (y j) : 𝓞 E) : E) := by
      change _ = algebraMap (𝓞 E) E _
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_mul, ← IsCMField.coe_ringOfIntegersComplexConj]
    rw [e1, e2, Nat.cast_one, one_mul]
    exact (map_sub (algebraMap (𝓞 E) E) _ _).symm
  obtain ⟨γ, hγ, ⟨k, hk, h1, h2⟩, -⟩ :=
    GlobalTheory.RepTrivial.repExists E N hur 1 n one_pos hn Λ 0 hU hiso
  rw [GlobalTheory.GenusLatCompare.span_smul_le_iff] at h1 h2
  exact ⟨γ, hγ, k, hk, fun v hv => h1 _ ⟨v, hv, rfl⟩, fun x hx => h2 x hx⟩

end General

theorem repExS (D : D7) : GL3Theta.repExS D := by
  letI := D.host.cmStar
  intro n hn N L L₀
  have hur := Formalism.L2.Pj.unramBridge D.host.E (Formalism.L2.Pj.cmUnram_conj D)
  have hst : ∀ x : D.host.E, star x = IsCMField.complexConj D.host.E x := fun _ => rfl
  have hU : ∀ M : SDLat D.host.E N, (⟨M.1⟩ : Formalism.L2.Pj.GenLat D.host.E N).Unimod := fun M v => by
    refine (M.2.2.2 v).trans (forall₂_congr fun w _ => ?_)
    have e : ∀ x y : Fin N → D.host.E, IsCMField.complexConj D.host.E (stdH D.host.E N x y) =
        stdH D.host.E N y x := fun x y => by
      rw [← hst]
      simp [stdH, mul_comm]
    have c : ∀ x y : Fin N → D.host.E, stdH D.host.E N x y ∈ (algebraMap (𝓞 D.host.E) D.host.E).range →
        stdH D.host.E N y x ∈ (algebraMap (𝓞 D.host.E) D.host.E).range := by
      rintro x y ⟨a, ha⟩
      refine ⟨IsCMField.ringOfIntegersComplexConj D.host.E a, ?_⟩
      rw [← e, ← ha]
      exact IsCMField.coe_ringOfIntegersComplexConj D.host.E a
    exact ⟨c w v, c v w⟩
  have hun : ∀ γ : Matrix (Fin N) (Fin N) D.host.E, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence.IsUnitaryM γ →
      γ ∈ Matrix.unitaryGroup (Fin N) D.host.E := fun γ h => Matrix.mem_unitaryGroup_iff'.2 h
  obtain ⟨γ, hγ, k, hk, h1, h2⟩ := exists_triv hur hn _ (hU L)
  obtain ⟨δ, hδ, l, hl, h3, h4⟩ := exists_triv hur hn _ (hU L₀)
  have hδ1 : star δ * δ = 1 := Matrix.mem_unitaryGroup_iff'.1 (hun δ hδ)
  have hγ1 : star γ * γ = 1 := Matrix.mem_unitaryGroup_iff'.1 (hun γ hγ)
  have hinv : ∀ v, star δ *ᵥ (δ *ᵥ v) = v := fun v => by
    rw [Matrix.mulVec_mulVec, hδ1, Matrix.one_mulVec]
  refine ⟨⟨star δ * γ, mul_mem (Unitary.star_mem (hun δ hδ)) (hun γ hγ)⟩, k * l,
    Nat.Coprime.mul_left hk hl, ?_, fun x hx => ?_⟩
  · rintro _ ⟨v, hv, rfl⟩
    obtain ⟨u, hu, e⟩ := h4 _ (h1 v hv)
    have : ((k * l : ℕ) : D.host.E) • ((star δ * γ) *ᵥ v) = u := by
      rw [← hinv u, e, Nat.cast_smul_eq_nsmul, ← Matrix.mulVec_mulVec, smul_smul, mul_comm l k,
        Matrix.mulVec_smul]
    exact this ▸ hu
  · obtain ⟨u, hu, e⟩ := h2 _ (h3 x hx)
    refine ⟨u, hu, ?_⟩
    change (star δ * γ) *ᵥ u = _
    rw [← Matrix.mulVec_mulVec, e, smul_smul, Matrix.mulVec_smul, hinv, Nat.cast_smul_eq_nsmul]

end GlobalTheory.RepEqAt
