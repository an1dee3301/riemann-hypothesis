module

public import Mathlib
public import Formalism.UnipotentAdelicQuotients.ThmBInHecke
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteAdeleBaseChangeEquiv
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsAdeleRingTensorEquivInfiniteProdFinite
public import Formalism.LocalToGlobal.Divisibility.Tuples
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Levelaf
public import Formalism.SatakeDualWeyl.Statement
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.NonUnitalHom
public import Mathlib.Algebra.Algebra.Prod
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Prod
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Algebra.Group.Submonoid.BigOperators
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Notation.Prod
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Equiv
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Prod
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.RingTheory.Valuation.ValuationSubring

@[expose] public section

noncomputable section

open HeckeCharacterZeroLocus.ThmBIn NumberField IsDedekindDomain
open scoped TensorProduct

namespace GlobalTheory.CMPrimeIdele

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]




variable (F E) in
def infPart : AE F E →+* Ainf F ⊗[F] E :=
  (Algebra.TensorProduct.map (AlgHom.fst F (Ainf F) (Af F) : AF F →ₐ[F] Ainf F) (AlgHom.id F E)).toRingHom


variable (F E) in
def swapAf : Af F ⊗[F] E →+* E ⊗[F] Af F := (Algebra.TensorProduct.comm F (Af F) E).toRingEquiv.toRingHom

def Comp (Φ : AE F E →+* FiniteAdeleRing (𝓞 E) E) : Prop :=
  (∀ z, infPart F E z = 0 → Φ z = 0 → z = 0) ∧
  (∀ s, ∃ z, infPart F E z = 0 ∧ Φ z = s) ∧
  (∀ x, Φ (incA F E x) = algebraMap _ _ x) ∧
  (∀ z, finPart F E z ∈ intAE F E ↔ ∀ Q, Φ z Q ∈ Q.adicCompletionIntegers E) ∧
  ∀ (a : AF F) Q, Φ (algebraMap _ _ a) Q = GlobalTheory.AdeleBaseChange.locMap F Q (a.2 (Q.under (𝓞 F)))

theorem mem_intAE_iff (z : Af F ⊗[F] E) :
    z ∈ intAE F E ↔ swapAf F E z ∈ Formalism.L2.DIV.RInt F E := by
  constructor
  · intro hz
    have : intAE F E ≤ (Formalism.L2.DIV.RInt F E).toAddSubgroup.comap (swapAf F E).toAddMonoidHom := by
      refine (AddSubgroup.closure_le _).2 ?_
      rintro _ ⟨a, ha, x, rfl⟩
      exact Formalism.UG.P.levelaf_tmul_mem x ha
    exact this hz
  · intro hz
    obtain ⟨m, g, hg⟩ := Module.Finite.exists_fin (R := ℤ) (M := 𝓞 E)
    obtain ⟨r, hr, e⟩ := Formalism.UG.P.levelaf_decomp g hg hz
    have : z = ∑ j, r j ⊗ₜ[F] (g j : E) := by
      apply (Algebra.TensorProduct.comm F (Af F) E).injective
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      exact e
    rw [this]
    exact sum_mem fun j _ => AddSubgroup.subset_closure ⟨r j, hr j, g j, rfl⟩

variable (F E) in

def IsDelta (Φ : AE F E →+* FiniteAdeleRing (𝓞 E) E) (P : HeightOneSpectrum (𝓞 E)) (e : AE F E) : Prop :=
  infPart F E e = 0 ∧ Φ e P = 1 ∧ ∀ Q, Q ≠ P → Φ e Q = 0





variable {σ : E →ₐ[F] E}














section

variable {Φ : AE F E →+* FiniteAdeleRing (𝓞 E) E}

theorem ev_mul (a b : AE F E) (Q : HeightOneSpectrum (𝓞 E)) : Φ (a * b) Q = Φ a Q * Φ b Q := by
  rw [map_mul]; rfl



variable (hΦ : Comp Φ)
include hΦ

theorem Comp.ext' {a b : AE F E} (h1 : infPart F E a = infPart F E b) (h2 : ∀ Q, Φ a Q = Φ b Q) : a = b := by
  rw [← sub_eq_zero]
  refine hΦ.1 _ (by rw [RingHom.map_sub, h1, sub_self]) ?_
  rw [map_sub, sub_eq_zero]
  exact FiniteAdeleRing.ext _ h2







theorem place_comp {v : HeightOneSpectrum (𝓞 F)} {ε : AF F} (h : IsPlaceIdem F v ε) :
    infPart F E (algebraMap _ (AE F E) ε) = 0 ∧
    (∀ Q : HeightOneSpectrum (𝓞 E), Q.under (𝓞 F) = v → Φ (algebraMap _ _ ε) Q = 1) ∧
    (∀ Q : HeightOneSpectrum (𝓞 E), Q.under (𝓞 F) ≠ v → Φ (algebraMap _ _ ε) Q = 0) := by
  obtain ⟨α, rfl, h1, h0⟩ := h
  refine ⟨TensorProduct.zero_tmul _ _, fun Q hQ => ?_, fun Q hQ => ?_⟩
  · subst hQ
    rw [hΦ.2.2.2.2]
    exact (congrArg _ h1).trans (map_one _)
  · rw [hΦ.2.2.2.2]
    exact (congrArg _ (h0 _ hQ)).trans (map_zero _)


end



end GlobalTheory.CMPrimeIdele
