module

public import Mathlib
public import Development.Core20Slim.GroundTheory.LocalFields.FormalGroups.LubinTate
public import Development.Core20Slim.GroundTheory.LocalFields.FormalGroups.LubinTateGroup
public import Development.Core20Slim.GroundTheory.LocalFields.LubinTatePoints
public import Development.Core20Slim.GroundTheory.LocalFields.LubinTateTorsion
public import Development.Core20Slim.GroundTheory.LocalFields.LubinTateTower
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Int.Lemmas
public import Init.Data.Int.Order
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Omega.Coeffs
public import Init.Omega.Constraint
public import Init.Omega.Int
public import Init.Omega.LinearCombo
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Divisibility.Basic
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.IsField
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Irreducible.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Subsemigroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Divisibility
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Quotient
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.FieldTheory.Normal.Basic
public import Mathlib.FieldTheory.Normal.Defs
public import Mathlib.FieldTheory.Separable
public import Mathlib.FieldTheory.SplittingField.IsSplittingField
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.RingTheory.Algebraic.Defs
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.NonUnitalSubring.Defs
public import Mathlib.RingTheory.NonUnitalSubsemiring.Defs
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.Valuation.Integers
public import Mathlib.RingTheory.Valuation.ValuativeRel.Basic
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Topology.Algebra.ValuativeRel.ValuativeTopology
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Separation.Hausdorff

set_option synthInstance.maxHeartbeats 400000

@[expose] public section

noncomputable section

open IntermediateField

namespace GroundTheory.LocalField

open ValuativeRel

section Restrict

variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]

def restrictAutFun {E F : IntermediateField K Ω} (h : F ≤ E) [Normal K F] (σ : E ≃ₐ[K] E) :
    F ≃ₐ[K] F :=
  AlgHom.restrictNormal' ((E.val.comp (σ : E →ₐ[K] E)).comp (inclusion h)) F

theorem restrictAutFun_apply {E F : IntermediateField K Ω} (h : F ≤ E) [Normal K F]
    (σ : E ≃ₐ[K] E) (x : F) : ((restrictAutFun h σ x : F) : Ω) = σ ⟨x, h x.2⟩ := by
  have := AlgHom.restrictNormal_commutes ((E.val.comp (σ : E →ₐ[K] E)).comp (inclusion h)) F x
  simp only [restrictAutFun, AlgHom.restrictNormal', AlgEquiv.coe_ofBijective]
  exact this

def restrictAut {E F : IntermediateField K Ω} (h : F ≤ E) [Normal K F] :
    (E ≃ₐ[K] E) →* (F ≃ₐ[K] F) where
  toFun := restrictAutFun h
  map_one' := AlgEquiv.ext fun x => Subtype.ext (by rw [restrictAutFun_apply]; rfl)
  map_mul' σ τ := AlgEquiv.ext fun x => Subtype.ext (by
    rw [AlgEquiv.mul_apply, restrictAutFun_apply, restrictAutFun_apply]
    have : (⟨(restrictAutFun h τ x : Ω), h (restrictAutFun h τ x).2⟩ : E) = τ ⟨x, h x.2⟩ :=
      Subtype.ext (restrictAutFun_apply h τ x)
    rw [this]
    rfl)

theorem restrictAut_apply {E F : IntermediateField K Ω} (h : F ≤ E) [Normal K F]
    (σ : E ≃ₐ[K] E) (x : F) : ((restrictAut h σ x : F) : Ω) = σ ⟨x, h x.2⟩ :=
  restrictAutFun_apply h σ x




end Restrict

namespace FormalGroup

section Reduce

variable {K : Type*} [Field K] [ValuativeRel K]

def unitsReduce (π : 𝒪[K]) {m n : ℕ} (h : m ≤ n) :
    (𝒪[K] ⧸ Ideal.span {π ^ n})ˣ →* (𝒪[K] ⧸ Ideal.span {π ^ m})ˣ :=
  Units.map (Ideal.Quotient.factor
    (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow π h))).toMonoidHom


def unitsMk (π : 𝒪[K]) (n : ℕ) : 𝒪[K]ˣ →* (𝒪[K] ⧸ Ideal.span {π ^ n})ˣ :=
  Units.map (Ideal.Quotient.mk (Ideal.span {π ^ n})).toMonoidHom

theorem coe_unitsMk (π : 𝒪[K]) (n : ℕ) (u : 𝒪[K]ˣ) :
    (unitsMk π n u : 𝒪[K] ⧸ Ideal.span {π ^ n}) = Ideal.Quotient.mk _ (u : 𝒪[K]) := rfl


end Reduce

section Char

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω]
variable {π : 𝒪[K]} (hπ : Irreducible π) {f g : PowerSeries 𝒪[K]}

variable [IsSepClosed Ω]

open Polynomial in
local instance normal_lubinTateField (hf : IsLubinTateSeries π f) (n : ℕ) :
    Normal K (lubinTateField Ω hπ hf n) := by
  have hq := one_lt_card_residueField' K
  have hlt : IsLubinTateSeries π (ltPoly π : PowerSeries 𝒪[K]) := {
    constantCoeff_eq_zero := by
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe, ltPoly]
      simp [coeff_X_pow, show 0 ≠ Nat.card 𝓀[K] by omega]
    coeff_one := by
      rw [Polynomial.coeff_coe, ltPoly]
      simp [coeff_X_pow, hq.ne]
    dvd_coeff_sub := fun k => by
      rw [coeff_ltPoly_sub, coeff_C_mul_X]
      split_ifs
      · exact dvd_rfl
      · exact dvd_zero π }
  have hpow (x : IdealPoint Ω (lubinTateFormalGroup hπ hlt)) :
      (π ^ n • x).val = aeval x.val ((ltPolyIter π n).map (algebraMap 𝒪[K] K)) := by
    have := t2Space_of_isValuativeTopology Ω
    induction n with
    | zero => simp [ltPolyIter_zero]
    | succ n ih =>
      rw [pow_succ', mul_smul, lubinTate_uniformizer_smul_val hlt, psEval_polynomial, ih,
        ltPolyIter_succ, Polynomial.map_comp, aeval_comp]
  let p := (ltPolyIter π n).map (algebraMap 𝒪[K] K)
  have hsep : p.Separable := separable_ltPolyIter hπ n
  have htorsion (x : IdealPoint Ω (lubinTateFormalGroup hπ hlt)) :
      x ∈ lubinTateTorsion Ω hlt n ↔ aeval x.val ((ltPolyIter π n).map (algebraMap 𝒪[K] K)) = 0 := by
    rw [mem_lubinTateTorsion, ← hpow]
    exact ⟨fun h => by rw [h]; rfl, fun h => IdealPoint.ext h⟩
  have hroots : IdealPoint.val '' (lubinTateTorsion Ω (hπ := hπ) hlt n :
      Set (IdealPoint Ω (lubinTateFormalGroup hπ hlt))) = p.rootSet Ω := by
    ext z
    rw [mem_rootSet_of_ne hsep.ne_zero]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (htorsion x).mp hx
    · intro hz
      let x : IdealPoint Ω (lubinTateFormalGroup hπ hlt) :=
        IdealPoint.mk z (valuation_lt_one_of_aeval_ltPolyIter_eq_zero hπ n hz)
      exact ⟨x, (htorsion x).mpr hz, rfl⟩
  rw [lubinTateField_eq hπ hf hlt, lubinTateField, hroots]
  have := adjoin_rootSet_isSplittingField (IsSepClosed.splits_codomain p hsep) (L := Ω)
  exact Normal.of_isSplittingField p

def lubinTateChar (hf : IsLubinTateSeries π f) (n : ℕ) {E : IntermediateField K Ω}
    (hE : lubinTateField Ω hπ hf n ≤ E) : (E ≃ₐ[K] E) →* (𝒪[K] ⧸ Ideal.span {π ^ n})ˣ :=
  (lubinTateGalEquiv hπ hf n).toMonoidHom.comp (restrictAut hE)

theorem lubinTateChar_spec (hf : IsLubinTateSeries π f) {n : ℕ} {E : IntermediateField K Ω}
    (hE : lubinTateField Ω hπ hf n ≤ E) (σ : E ≃ₐ[K] E)
    {x : IdealPoint Ω (lubinTateFormalGroup hπ hf)} (hx : x ∈ lubinTateTorsion Ω hf n) (a : 𝒪[K])
    (ha : Ideal.Quotient.mk _ a = (lubinTateChar hπ hf n hE σ : 𝒪[K] ⧸ Ideal.span {π ^ n})) :
    ((σ ⟨x.val, hE (val_mem_lubinTateField hπ hf hx)⟩ : E) : Ω) = (a • x).val :=
  (restrictAut_apply hE σ ⟨x.val, val_mem_lubinTateField hπ hf hx⟩).symm.trans
    (lubinTateGalEquiv_spec hf n (restrictAut hE σ) x hx a ha)

theorem lubinTateChar_eq_of_apply (hf : IsLubinTateSeries π f) {n : ℕ} {E : IntermediateField K Ω}
    (hE : lubinTateField Ω hπ hf n ≤ E) (σ : E ≃ₐ[K] E) (a : 𝒪[K])
    (h : ∀ (x) (hx : x ∈ lubinTateTorsion Ω (hπ := hπ) hf n),
      ((σ ⟨x.val, hE (val_mem_lubinTateField hπ hf hx)⟩ : E) : Ω) = (a • x).val) :
    (lubinTateChar hπ hf n hE σ : 𝒪[K] ⧸ Ideal.span {π ^ n}) = Ideal.Quotient.mk _ a := by
  obtain ⟨l, hl, hann, -⟩ := exists_generator_lubinTateTorsion (Ω := Ω) (hπ := hπ) hf n
  obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective
    (lubinTateChar hπ hf n hE σ : 𝒪[K] ⧸ Ideal.span {π ^ n})
  have h1 := lubinTateChar_spec hπ hf hE σ hl b hb
  rw [h l hl] at h1
  have h2 : b • l = a • l := (IdealPoint.ext h1).symm
  rw [← hb, Ideal.Quotient.eq, ← hann, sub_smul, sub_eq_zero]
  exact h2



end Char

end FormalGroup

end GroundTheory.LocalField
