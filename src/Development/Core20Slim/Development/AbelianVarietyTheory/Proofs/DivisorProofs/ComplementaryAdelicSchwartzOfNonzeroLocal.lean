module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchroedingerOperatorHeisenbergLawApplyStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationLocalityUnitaryGroupVStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalWeilOperatorIsometrySchwartzBruhatStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEqStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicHeisenbergActsByLocalSchrodingerStatement
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
public import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Classical
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Ext
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.NonUnitalHom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Map
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Notation.Prod
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Equiv
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Torsor.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SProd
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Sets
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.Logic.Function.Basic
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Filter.Cofinite
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Group.Torsor
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.Support
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Topology.Separation.Basic
public import Mathlib.Topology.Separation.Regular
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
noncomputable section

namespace GlobalTheory.RestCofactor

variable {F : Type} [Field F] [NumberField F]

def shiftFin (v : Pl (F := F)) {κ : Type} (x₀ : κ → Fv F v) (y : κ → Af F) : κ → Af F :=
  fun i => y i + (singleFin v (x₀ i) - singleFin v (evalV F v (y i)))

theorem evalV_shiftFin (v : Pl (F := F)) {κ : Type} (x₀ : κ → Fv F v) (y : κ → Af F) (i : κ) :
    evalV F v (shiftFin v x₀ y i) = x₀ i := by
  simp only [shiftFin, map_add (f := _), map_sub, evalV_singleFin_self]
  abel

theorem shiftFin_back (v : Pl (F := F)) {κ : Type} (x₀ : κ → Fv F v) (y : κ → Af F) :
    shiftFin v (fun i => evalV F v (y i)) (shiftFin v x₀ y) = y := by
  funext i
  rw [shiftFin, evalV_shiftFin]
  simp only [shiftFin]
  abel

theorem continuous_shiftFin (v : Pl (F := F)) {κ : Type} :
    Continuous fun p : (κ → Fv F v) × (κ → Af F) => shiftFin v p.1 p.2 := by
  have hev : Continuous (evalV F v) := RestrictedProduct.continuous_eval v
  refine continuous_pi fun i => ?_
  have h2 : Continuous fun p : (κ → Fv F v) × (κ → Af F) => p.2 i := (continuous_apply i).comp continuous_snd
  have h1 : Continuous fun p : (κ → Fv F v) × (κ → Af F) => p.1 i := (continuous_apply i).comp continuous_fst
  exact h2.add (((continuous_singleFin v).comp h1).sub ((continuous_singleFin v).comp (hev.comp h2)))

theorem mem_SB_shift (v : Pl (F := F)) {κ : Type} (x₀ : κ → Fv F v) {φ' : (κ → Fv F v) → ℂ}
    (hφ' : φ' ∈ SB (κ → Fv F v)) {g : (κ → Af F) → ℂ} (hg : g ∈ SB (κ → Af F)) :
    (fun y : κ → Af F => φ' (fun i => evalV F v (y i)) * g (shiftFin v x₀ y)) ∈ SB (κ → Af F) := by
  have hev : Continuous (evalV F v) := RestrictedProduct.continuous_eval v
  have hE : Continuous fun y : κ → Af F => fun i => evalV F v (y i) :=
    continuous_pi fun i => hev.comp (continuous_apply i)
  have hS : Continuous (shiftFin v x₀) :=
    (continuous_shiftFin v).comp (continuous_const.prodMk continuous_id)
  refine ⟨(hφ'.1.comp_continuous hE).mul (hg.1.comp_continuous hS), ?_⟩
  have hK : IsCompact ((fun p : (κ → Fv F v) × (κ → Af F) => shiftFin v p.1 p.2) ''
      (tsupport φ' ×ˢ tsupport g)) := (IsCompact.prod hφ'.2 hg.2).image (continuous_shiftFin v)
  refine HasCompactSupport.intro hK fun y hy => ?_
  by_contra hne
  have ha : φ' (fun i => evalV F v (y i)) ≠ 0 := left_ne_zero_of_mul hne
  have hb : g (shiftFin v x₀ y) ≠ 0 := right_ne_zero_of_mul hne
  exact hy ⟨(fun i => evalV F v (y i), shiftFin v x₀ y),
    ⟨subset_tsupport _ ha, subset_tsupport _ hb⟩, shiftFin_back v x₀ y⟩

theorem rest_of_rest : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (v : Pl (F := F))
    (φ φ' : (κ → Fv F v) → ℂ) (r : (κ → AF F) → ℂ), φ ≠ 0 → φ' ∈ SB (κ → Fv F v) →
    Rest (evFin F v) φ r → Rest (evFin F v) φ' r := by
  intro F _ _ κ _ v φ φ' r hφ hφ' hr
  obtain ⟨x₀, hx₀⟩ := Function.ne_iff.mp hφ
  refine ⟨hr.1, ?_⟩
  let z : (κ → AF F) → κ → AF F := fun x i =>
    pairA F 0 (singleFin v (x₀ i) - singleFin v (evalV F v (x i).2))
  have hz : ∀ x, At (evFin F v) (z x) := by
    intro x u hu
    funext i
    refine Prod.ext ?_ ?_
    · change u.1 * 0 = 0
      exact mul_zero _
    · change u.2 * (singleFin v (x₀ i) - singleFin v (evalV F v (x i).2)) = 0
      refine af_ext fun w => ?_
      rw [map_mul, map_zero]
      by_cases hw : w = v
      · subst hw
        have : evalV F w u.2 = 0 := hu
        rw [this, zero_mul]
      · rw [map_sub, evalV_singleFin_ne hw, evalV_singleFin_ne hw, sub_zero, mul_zero]
  have h1 : ∀ x i, ((x + z x) i).1 = (x i).1 := fun x i => by
    change (x i).1 + 0 = (x i).1
    exact add_zero _
  have h2 : ∀ x i, ((x + z x) i).2 = shiftFin v x₀ (fun i => (x i).2) i := fun x i => rfl
  have hev : ∀ x i, evFin F v ((x + z x) i) = x₀ i := fun x i => by
    change evalV F v ((x + z x) i).2 = x₀ i
    rw [h2, evalV_shiftFin]
  let L : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ) :=
    { toFun := fun Φ x => φ' (fun i => evFin F v (x i)) * Φ (x + z x)
      map_add' := fun Φ Ψ => funext fun x => by simp only [Pi.add_apply]; ring
      map_smul' := fun c Φ => funext fun x => by
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring }
  have hL : schA F κ ≤ (schA F κ).comap L := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨f, g, hg, rfl⟩
    refine Submodule.subset_span ⟨f, _, mem_SB_shift v x₀ hφ' hg, funext fun x => ?_⟩
    change φ' (fun i => evFin F v (x i)) * pureA F f g (x + z x) = _
    simp only [pureA, h1, h2]
    change _ = _ * (φ' (fun i => evFin F v (x i)) * _)
    ring
  have key : tens (evFin F v) φ' r = (φ x₀)⁻¹ • L (tens (evFin F v) φ r) := by
    funext x
    change φ' (fun i => evFin F v (x i)) * r x =
      (φ x₀)⁻¹ * (φ' (fun i => evFin F v (x i)) * (φ (fun i => evFin F v ((x + z x) i)) * r (x + z x)))
    have hx : φ x₀ ≠ 0 := hx₀
    simp only [hev, hr.1 x (z x) (hz x)]
    rw [mul_left_comm (φ x₀)⁻¹, ← mul_assoc (φ x₀)⁻¹, inv_mul_cancel₀ hx, one_mul]
  rw [key]
  exact Submodule.smul_mem _ _ (hL hr.2)

end GlobalTheory.RestCofactor
