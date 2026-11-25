module

public import Mathlib
public import Development.Core20Slim.GroundTheory.GlobalFields.HerbrandQuotients.CycTate
public import Development.Core20Slim.GroundTheory.GlobalFields.CompletionAtPlace.Galois
public import Development.Core20Slim.GroundTheory.LocalFields.HerbrandLocal
public import Development.Core20Slim.GroundTheory.LocalFields.UnramifiedNorms
public import Development.Core20Slim.GroundTheory.LocalFields.HerbrandCyclic
public import Development.Core20Slim.GroundTheory.GlobalFields.CompletionAtPlace
public import Development.Core20Slim.GroundTheory.GlobalFields.CompletionAtPlace.Integers
public import Development.Core20Slim.GroundTheory.GlobalFields.LocalFieldAtPlace
public import Development.Core20Slim.GroundTheory.LocalFields.CompleteTrivial
public import GroundTheory.LocalFields.Interface
public import GroundTheory.LocalFields.Uniqueness
public import Development.Core20Slim.GroundTheory.LocalFields.UnitsGalois
public import Development.Core20Slim.GroundTheory.LocalFields.UnramifiedDefs
public import Development.Core20Slim.GroundTheory.TateCohomology.HerbrandAbstract
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Function
public import Init.Data.Int.Basic
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.IsField
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Units
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Group.Equiv.TypeTags
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Group.Units.Equiv
public import Mathlib.Algebra.Group.WithOne.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.WithZero
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Order.Monoid.Unbundled.TypeTags
public import Mathlib.Algebra.Ring.Action.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Equiv
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.NNRat.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Rat.Init
public import Mathlib.FieldTheory.Fixed
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.GroupTheory.GroupAction.Defs
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Over
public import Mathlib.RingTheory.Ideal.Pointwise
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import Mathlib.RingTheory.RamificationInertia.Ramification
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.Valuation.Basic
public import Mathlib.RingTheory.Valuation.Extension
public import Mathlib.RingTheory.Valuation.Integers
public import Mathlib.RingTheory.Valuation.ValuationRing
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.RingTheory.Valuation.ValuativeRel.Basic
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Topology.Algebra.Valued.ValuationTopology
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.UniformSpace.Defs

set_option synthInstance.maxHeartbeats 400000

@[expose] public section

noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField ValuativeRel GroundTheory.GroupCoh

open scoped Pointwise

namespace GroundTheory.Global

section ChangeOfGroup

variable {k H G V W : Type*} [CommRing k] [Group H] [Group G] [AddCommGroup V] [Module k V]
  [AddCommGroup W] [Module k W] {ρ' : Representation k H V} {ρ : Representation k G W}

theorem cycSubOne_mulEquiv (e : H →* G) (f : V ≃+ W) (hf : ∀ h x, f (ρ' h x) = ρ (e h) (f x))
    (τ : H) (x : V) : f (cycSubOne ρ' τ x) = cycSubOne ρ (e τ) (f x) := by
  rw [cycSubOne_apply, cycSubOne_apply, map_sub, hf]

variable [Fintype H] [Fintype G]

theorem cycNorm_mulEquiv (e : H ≃* G) (f : V ≃+ W) (hf : ∀ h x, f (ρ' h x) = ρ (e h) (f x))
    (x : V) : f (cycNorm ρ' x) = cycNorm ρ (f x) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [cycNorm_apply, cycNorm_apply, map_sum]
  simp_rw [hf]
  exact Fintype.sum_equiv e.toEquiv _ _ fun _ ↦ rfl

def cycTateZeroEquivOfMulEquiv (e : H ≃* G) (f : V ≃+ W) (hf : ∀ h x, f (ρ' h x) = ρ (e h) (f x))
    (τ : H) : CycTateZero ρ' τ ≃+ CycTateZero ρ (e τ) :=
  kerModRangeCongr f (cycSubOne_mulEquiv e.toMonoidHom f hf τ) (cycNorm_mulEquiv e f hf)

def cycTateNegOneEquivOfMulEquiv (e : H ≃* G) (f : V ≃+ W)
    (hf : ∀ h x, f (ρ' h x) = ρ (e h) (f x)) (τ : H) :
    CycTateNegOne ρ' τ ≃+ CycTateNegOne ρ (e τ) :=
  kerModRangeCongr f (cycNorm_mulEquiv e f hf) (cycSubOne_mulEquiv e.toMonoidHom f hf τ)

theorem cycHerbrand_eq_of_mulEquiv (e : H ≃* G) (f : V ≃+ W)
    (hf : ∀ h x, f (ρ' h x) = ρ (e h) (f x)) (τ : H) :
    (HasHerbrandQuotient (cycSubOne ρ' τ) (cycNorm ρ') ↔
      HasHerbrandQuotient (cycSubOne ρ (e τ)) (cycNorm ρ)) ∧
    cycHerbrand ρ' τ = cycHerbrand ρ (e τ) := by
  have e0 := (cycTateZeroEquivOfMulEquiv e f hf τ).toEquiv
  have e1 := (cycTateNegOneEquivOfMulEquiv e f hf τ).toEquiv
  refine ⟨?_, ?_⟩
  · exact ⟨fun h ↦ ⟨Finite.of_equiv _ e0 (h := h.1), Finite.of_equiv _ e1 (h := h.2)⟩,
      fun h ↦ ⟨Finite.of_equiv _ e0.symm (h := h.1), Finite.of_equiv _ e1.symm (h := h.2)⟩⟩
  · rw [cycHerbrand_eq, cycHerbrand_eq, Nat.card_congr e0, Nat.card_congr e1]


omit [Fintype H] [Fintype G] in
theorem mem_zpowers_mulEquiv (e : H ≃* G) {τ : H} (hτ : ∀ h, h ∈ Subgroup.zpowers τ) (g : G) :
    g ∈ Subgroup.zpowers (e τ) := by
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 (hτ (e.symm g))
  refine Subgroup.mem_zpowers_iff.2 ⟨n, ?_⟩
  rw [← map_zpow, hn, MulEquiv.apply_symm_apply]

end ChangeOfGroup

section DecompositionAction

variable {K L : Type*} [Field K] [Field L] [NumberField L] [Algebra K L]
  (w : HeightOneSpectrum (𝓞 L))

instance decompositionMulSemiringAction :
    MulSemiringAction (MulAction.stabilizer Gal(L/K) w.asIdeal) (w.adicCompletion L) where
  smul σ x := adicCompletionRingHomOf w σ.1 (smul_asIdeal_of_mem_stabilizer w σ) x
  one_smul x := by
    change adicCompletionRingHomOf w 1 _ x = RingHom.id _ x
    congr 1
    exact ringHom_ext_adicCompletion w (continuous_adicCompletionRingHomOf _ _) continuous_id
      fun y ↦ by rw [adicCompletionRingHomOf_algebraMap]; rfl
  mul_smul σ τ x := by
    change adicCompletionRingHomOf w (σ * τ).1 (smul_asIdeal_of_mem_stabilizer w (σ * τ)) x =
      ((adicCompletionRingHomOf w σ.1 (smul_asIdeal_of_mem_stabilizer w σ)).comp
        (adicCompletionRingHomOf w τ.1 (smul_asIdeal_of_mem_stabilizer w τ))) x
    congr 1
    exact ringHom_ext_adicCompletion w (continuous_adicCompletionRingHomOf _ _)
      ((continuous_adicCompletionRingHomOf σ.1 (smul_asIdeal_of_mem_stabilizer w σ)).comp
        (continuous_adicCompletionRingHomOf τ.1 (smul_asIdeal_of_mem_stabilizer w τ)))
      fun y ↦ by
        rw [RingHom.comp_apply, adicCompletionRingHomOf_algebraMap,
          adicCompletionRingHomOf_algebraMap, adicCompletionRingHomOf_algebraMap]
        rfl
  smul_zero σ := map_zero _
  smul_add σ := map_add _
  smul_one σ := map_one _
  smul_mul σ := map_mul _

variable {w}

theorem decomposition_smul_def (σ : MulAction.stabilizer Gal(L/K) w.asIdeal)
    (x : w.adicCompletion L) :
    σ • x = adicCompletionRingHomOf w σ.1 (smul_asIdeal_of_mem_stabilizer w σ) x :=
  rfl

theorem valued_decomposition_smul (σ : MulAction.stabilizer Gal(L/K) w.asIdeal)
    (x : w.adicCompletion L) : Valued.v (σ • x) = Valued.v x :=
  valued_adicCompletionRingHomOf _ _ x

variable (w)

instance decompositionMulSemiringActionIntegers :
    MulSemiringAction (MulAction.stabilizer Gal(L/K) w.asIdeal) (w.adicCompletionIntegers L) where
  smul σ x := ⟨σ • (x : w.adicCompletion L), by
    rw [mem_adicCompletionIntegers, valued_decomposition_smul]
    exact x.2⟩
  one_smul x := Subtype.ext (one_smul _ (x : w.adicCompletion L))
  mul_smul σ τ x := Subtype.ext (mul_smul σ τ (x : w.adicCompletion L))
  smul_zero σ := Subtype.ext (smul_zero σ)
  smul_add σ x y := Subtype.ext (smul_add σ (x : w.adicCompletion L) y)
  smul_one σ := Subtype.ext (smul_one σ)
  smul_mul σ x y := Subtype.ext (MulSemiringAction.smul_mul σ (x : w.adicCompletion L) y)


instance decompositionUnitsAction :
    MulDistribMulAction (MulAction.stabilizer Gal(L/K) w.asIdeal) (w.adicCompletion L)ˣ :=
  Units.mulDistribMulActionRight

instance decompositionIntegerUnitsAction :
    MulDistribMulAction (MulAction.stabilizer Gal(L/K) w.asIdeal) (w.adicCompletionIntegers L)ˣ :=
  Units.mulDistribMulActionRight

variable {w}

@[simp]
theorem coe_decomposition_smul_units (σ : MulAction.stabilizer Gal(L/K) w.asIdeal)
    (u : (w.adicCompletion L)ˣ) : ((σ • u : (w.adicCompletion L)ˣ) : w.adicCompletion L) =
      σ • (u : w.adicCompletion L) :=
  rfl

@[simp]
theorem coe_decomposition_smul_integerUnits (σ : MulAction.stabilizer Gal(L/K) w.asIdeal)
    (u : (w.adicCompletionIntegers L)ˣ) :
    (((σ • u : (w.adicCompletionIntegers L)ˣ) : w.adicCompletionIntegers L) :
      w.adicCompletion L) = σ • ((u : w.adicCompletionIntegers L) : w.adicCompletion L) :=
  rfl

end DecompositionAction

section Units

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]
  (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]
  [Algebra (v.adicCompletion K) (w.adicCompletion L)]
  [ContinuousSMul (v.adicCompletion K) (w.adicCompletion L)]
  [IsScalarTower K (v.adicCompletion K) (w.adicCompletion L)]

theorem ofMulDistribMulAction_decomposition_units (σ : MulAction.stabilizer Gal(L/K) w.asIdeal)
    (x : Additive (w.adicCompletion L)ˣ) :
    Representation.ofMulDistribMulAction (MulAction.stabilizer Gal(L/K) w.asIdeal)
        (w.adicCompletion L)ˣ σ x =
      Representation.ofMulDistribMulAction Gal(w.adicCompletion L/v.adicCompletion K)
        (w.adicCompletion L)ˣ (decompositionMulEquiv v w σ) x := by
  apply Additive.toMul.injective
  apply Units.ext
  rfl

theorem cycHerbrand_adicCompletion_units [Fintype (MulAction.stabilizer Gal(L/K) w.asIdeal)]
    (τ : MulAction.stabilizer Gal(L/K) w.asIdeal) (hτ : ∀ σ, σ ∈ Subgroup.zpowers τ) :
    HasHerbrandQuotient
        (cycSubOne (Representation.ofMulDistribMulAction (MulAction.stabilizer Gal(L/K) w.asIdeal)
          (w.adicCompletion L)ˣ) τ)
        (cycNorm (Representation.ofMulDistribMulAction (MulAction.stabilizer Gal(L/K) w.asIdeal)
          (w.adicCompletion L)ˣ)) ∧
      cycHerbrand (Representation.ofMulDistribMulAction (MulAction.stabilizer Gal(L/K) w.asIdeal)
          (w.adicCompletion L)ˣ) τ =
        Module.finrank (v.adicCompletion K) (w.adicCompletion L) := by
  obtain ⟨h1, h2⟩ := cycHerbrand_eq_of_mulEquiv
    (ρ' := Representation.ofMulDistribMulAction (MulAction.stabilizer Gal(L/K) w.asIdeal)
      (w.adicCompletion L)ˣ)
    (ρ := Representation.ofMulDistribMulAction Gal(w.adicCompletion L/v.adicCompletion K)
      (w.adicCompletion L)ˣ)
    (decompositionMulEquiv v w) (AddEquiv.refl _)
    (fun σ x ↦ ofMulDistribMulAction_decomposition_units v w σ x) τ
  obtain ⟨h3, h4⟩ := GroundTheory.LocalField.cycHerbrand_units_eq_finrank
    (K := v.adicCompletion K) (L := w.adicCompletion L)
    (mem_zpowers_mulEquiv (decompositionMulEquiv v w) hτ)
  exact ⟨h1.2 h3, h2.trans h4⟩

end Units

section UnitsCard

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]
  (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]

def adicCompletionIntegersEquivInteger :
    w.adicCompletionIntegers L ≃+* 𝒪[w.adicCompletion L] where
  toFun x := ⟨x, (mem_valuationInteger_iff w (x : w.adicCompletion L)).2 x.2⟩
  invFun y := ⟨y, (mem_valuationInteger_iff w (y : w.adicCompletion L)).1 y.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

def integerUnitsAddEquiv :
    Additive (w.adicCompletionIntegers L)ˣ ≃+ Additive 𝒪[w.adicCompletion L]ˣ :=
  MulEquiv.toAdditive (Units.mapEquiv (adicCompletionIntegersEquivInteger w).toMulEquiv)

variable [Algebra (v.adicCompletion K) (w.adicCompletion L)]
  [ContinuousSMul (v.adicCompletion K) (w.adicCompletion L)]
  [IsScalarTower K (v.adicCompletion K) (w.adicCompletion L)]

theorem integerUnitsAddEquiv_decomposition (σ : MulAction.stabilizer Gal(L/K) w.asIdeal)
    (x : Additive (w.adicCompletionIntegers L)ˣ) :
    integerUnitsAddEquiv w (Representation.ofMulDistribMulAction
        (MulAction.stabilizer Gal(L/K) w.asIdeal) (w.adicCompletionIntegers L)ˣ σ x) =
      Representation.ofMulDistribMulAction Gal(w.adicCompletion L/v.adicCompletion K)
        𝒪[w.adicCompletion L]ˣ (decompositionMulEquiv v w σ) (integerUnitsAddEquiv w x) := by
  apply Additive.toMul.injective
  apply Units.ext
  apply Subtype.ext
  change σ • ((x.toMul : w.adicCompletionIntegers L) : w.adicCompletion L) =
    ((GroundTheory.LocalField.integerAlgEquiv (v.adicCompletion K) (w.adicCompletion L)
      (decompositionMulEquiv v w σ) _ : 𝒪[w.adicCompletion L]) : w.adicCompletion L)
  rw [GroundTheory.LocalField.coe_integerAlgEquiv_apply]
  rfl


omit [IsGalois K L] in
theorem isUnramified_adicCompletion (he : w.asIdeal.ramificationIdx (𝓞 K) = 1) :
    GroundTheory.LocalField.IsUnramified (v.adicCompletion K) (w.adicCompletion L) :=
  (GroundTheory.LocalField.isUnramified_iff _ _).2 ((ramificationIdx_integer v w).trans he)

end UnitsCard

section Unramified

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]
  (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]


open AdicLiesOver in
include v in
theorem subsingleton_cycTateZero_adicCompletionIntegers_units
    (he : w.asIdeal.ramificationIdx (𝓞 K) = 1)
    [Fintype (MulAction.stabilizer Gal(L/K) w.asIdeal)]
    (τ : MulAction.stabilizer Gal(L/K) w.asIdeal) (hτ : ∀ σ, σ ∈ Subgroup.zpowers τ) :
    Subsingleton (CycTateZero (Representation.ofMulDistribMulAction
      (MulAction.stabilizer Gal(L/K) w.asIdeal) (w.adicCompletionIntegers L)ˣ) τ) := by
  have := isUnramified_adicCompletion v w he
  have hgen := mem_zpowers_mulEquiv (decompositionMulEquiv v w) hτ
  have : Subsingleton (GroundTheory.LocalField.TateZero Gal(w.adicCompletion L/v.adicCompletion K)
      𝒪[w.adicCompletion L]ˣ) := GroundTheory.LocalField.subsingleton_tateZero_integerUnits
  have h1 : Nat.card (GroundTheory.LocalField.TateZero Gal(w.adicCompletion L/v.adicCompletion K)
      𝒪[w.adicCompletion L]ˣ) = 1 := Nat.card_eq_one_iff_unique.2 ⟨inferInstance, ⟨1⟩⟩
  rw [GroundTheory.LocalField.natCard_tateZero_eq hgen, ← Nat.card_congr
    (cycTateZeroEquivOfMulEquiv (decompositionMulEquiv v w) (integerUnitsAddEquiv w)
      (integerUnitsAddEquiv_decomposition v w) τ).toEquiv] at h1
  exact (Nat.card_eq_one_iff_unique.1 h1).1


open AdicLiesOver in
include v in
theorem subsingleton_cycTateNegOne_adicCompletionIntegers_units
    (he : w.asIdeal.ramificationIdx (𝓞 K) = 1)
    [Fintype (MulAction.stabilizer Gal(L/K) w.asIdeal)]
    (τ : MulAction.stabilizer Gal(L/K) w.asIdeal) (hτ : ∀ σ, σ ∈ Subgroup.zpowers τ) :
    Subsingleton (CycTateNegOne (Representation.ofMulDistribMulAction
      (MulAction.stabilizer Gal(L/K) w.asIdeal) (w.adicCompletionIntegers L)ˣ) τ) := by
  have := isUnramified_adicCompletion v w he
  have hgen := mem_zpowers_mulEquiv (decompositionMulEquiv v w) hτ
  have : IsCyclic Gal(w.adicCompletion L/v.adicCompletion K) :=
    ⟨⟨decompositionMulEquiv v w τ, fun g ↦ Subgroup.mem_zpowers_iff.1 (hgen g)⟩⟩
  have : Subsingleton (GroundTheory.LocalField.TateNegOne Gal(w.adicCompletion L/v.adicCompletion K)
      𝒪[w.adicCompletion L]ˣ) := GroundTheory.LocalField.subsingleton_tateNegOne_integerUnits
  have h1 : Nat.card (GroundTheory.LocalField.TateNegOne Gal(w.adicCompletion L/v.adicCompletion K)
      𝒪[w.adicCompletion L]ˣ) = 1 := Nat.card_eq_one_iff_unique.2 ⟨inferInstance, ⟨1⟩⟩
  rw [GroundTheory.LocalField.natCard_tateNegOne_eq hgen, ← Nat.card_congr
    (cycTateNegOneEquivOfMulEquiv (decompositionMulEquiv v w) (integerUnitsAddEquiv w)
      (integerUnitsAddEquiv_decomposition v w) τ).toEquiv] at h1
  exact (Nat.card_eq_one_iff_unique.1 h1).1

end Unramified

end GroundTheory.Global
