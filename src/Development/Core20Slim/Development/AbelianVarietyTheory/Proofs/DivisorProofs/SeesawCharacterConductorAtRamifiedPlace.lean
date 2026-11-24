module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocPart
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.GSEqZeroOfLt
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaFactorNonzero
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalCharacterSmoothUnitary
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Definitions.Foundations.NonemptyAlgHomOfNotIsField
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Classical
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Int.Order
public import Init.Data.Nat.Basic
public import Init.Data.Order.Lemmas
public import Init.Data.Zero
public import Init.Omega.Coeffs
public import Init.Omega.Constraint
public import Init.Omega.Int
public import Init.Omega.LinearCombo
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Basic
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Algebra.Order.Monoid.Unbundled.Pow
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.UnitBall
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Lattice
public import Mathlib.Order.Lattice.Nat
public import Mathlib.Order.RelClasses
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Valuation.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.RingTheory.Valuation.ValuativeRel.Basic
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes ValuativeRel
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.StdPairCone
open GlobalTheory.Doubling (absE)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.StdPairConeChars

theorem condLE_mono {F : Type} [Field F] [NumberField F] {v : Pl (F := F)} {e m : ℕ} (hem : e ≤ m)
    {χ : (Fv F v)ˣ →* ℂˣ} (h : GlobalTheory.SplitFlip.CondLE (unifAt v) e χ) : GlobalTheory.SplitFlip.CondLE (unifAt v) m χ := by
  have hϖ : GlobalTheory.SplitFlip.IsUnif (unifAt v) := (GlobalTheory.SplitFlip.exists_isUnif (k := Fv F v)).choose_spec
  have h1 : ValuativeRel.valuation (Fv F v) ((unifAt v : (Fv F v)ˣ) : Fv F v) ≤ 1 := hϖ.mem
  intro x hx
  refine h x ⟨hx.1, hx.2.trans ?_⟩
  simp only [Units.val_pow_eq_pow_val, map_pow]
  exact pow_le_pow_right_of_le_one' h1 hem

theorem nu_cond_at_ram : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W),
    IsTriple B G X om om' → ∀ v : B.P, v.1 ∈ X.T →
      GlobalTheory.SplitFlip.CondLE (unifAt v.1) (condExp (chrW X.ν (B.τ v))) (chrW X.ν (B.τ v)) ∧ 1 ≤ (condExp (chrW X.ν (B.τ v))) ∧
      chrW X.ν (B.τ v) = chrW X.α (B.τ v) / chrW X.β (B.τ v) ∧
      (∃ m, GlobalTheory.SplitFlip.CondLE (unifAt v.1) m (chrW X.α (B.τ v)) ∧ GlobalTheory.SplitFlip.CondLE (unifAt v.1) m (chrW X.β (B.τ v))) ∧
      (∀ x, ‖(chrW X.α (B.τ v) x : ℂ)‖ = 1) ∧ ∀ x, ‖(chrW X.β (B.τ v) x : ℂ)‖ = 1 := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v hvT
  have hϖ : GlobalTheory.SplitFlip.IsUnif (unifAt v.1) := (GlobalTheory.SplitFlip.exists_isUnif (k := Fv F v.1)).choose_spec
  have hα := hT.chars.heckeα.1
  have hβ := hT.chars.heckeβ.1
  have hν : Continuous X.ν := (show Continuous fun x => X.α x / X.β x from hα.div' hβ)
  have hne : {c | GlobalTheory.SplitFlip.CondLE (unifAt v.1) c (chrW X.ν (B.τ v))}.Nonempty :=
    GlobalTheory.GaussNonvanish.exists_condLE hϖ _ (GlobalTheory.StepFacNe.chrW_continuous X.ν hν (B.τ v))
  have hmem : GlobalTheory.SplitFlip.CondLE (unifAt v.1) (condExp (chrW X.ν (B.τ v))) (chrW X.ν (B.τ v)) := Nat.sInf_mem hne
  obtain ⟨eα, heα⟩ := GlobalTheory.GaussNonvanish.exists_condLE hϖ _ (GlobalTheory.StepFacNe.chrW_continuous X.α hα (B.τ v))
  obtain ⟨eβ, heβ⟩ := GlobalTheory.GaussNonvanish.exists_condLE hϖ _ (GlobalTheory.StepFacNe.chrW_continuous X.β hβ (B.τ v))
  have hram : ¬ UnrAt X.ν (splitPrime (B.τ v)) :=
    hT.chars.ram _ (by rw [splitPrime_under]; exact hvT)
  obtain ⟨x₀, hx₀, hx₀', hνx₀⟩ := GlobalTheory.StepFacNe.chrW_ram X.ν (B.τ v) hram
  have hx₀v : ValuativeRel.valuation (Fv F v.1) (x₀ : Fv F v.1) = 1 := by
    have h1 := (GlobalTheory.GaussNonvanish.val_le_one_iff v.1 _).2 hx₀
    have h2 := (GlobalTheory.GaussNonvanish.val_le_one_iff v.1 _).2 hx₀'
    have h3 : ValuativeRel.valuation (Fv F v.1) (x₀ : Fv F v.1) *
        ValuativeRel.valuation (Fv F v.1) ((x₀⁻¹ : (Fv F v.1)ˣ) : Fv F v.1) = 1 := by
      rw [← map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one]
    refine le_antisymm h1 ?_
    calc (1 : ValuativeRel.ValueGroupWithZero (Fv F v.1)) = _ := h3.symm
      _ ≤ _ := mul_le_of_le_one_right' h2
  have hc1 : 1 ≤ condExp (chrW X.ν (B.τ v)) := by
    by_contra h
    have h0 : condExp (chrW X.ν (B.τ v)) = 0 := by omega
    have hm := hmem
    rw [h0] at hm
    refine hνx₀ (hm x₀ ⟨hx₀v, ?_⟩)
    rw [pow_zero, Units.val_one, map_one]
    exact ((ValuativeRel.valuation (Fv F v.1)).map_sub _ _).trans (by simp [hx₀v])
  have hdiv : chrW X.ν (B.τ v) = chrW X.α (B.τ v) / chrW X.β (B.τ v) := by
    ext x
    simp [chrW, locChar, Chars.ν]
  refine ⟨hmem, hc1, hdiv, ⟨max eα eβ, condLE_mono (le_max_left _ _) heα, condLE_mono (le_max_right _ _) heβ⟩,
    fun x => ?_, fun x => ?_⟩
  · exact GlobalTheory.ChrWSmooth.isUnitaryChar_chrW X.α (B.τ v) x
  · exact GlobalTheory.ChrWSmooth.isUnitaryChar_chrW X.β (B.τ v) x

end GlobalTheory.StdPairConeChars
