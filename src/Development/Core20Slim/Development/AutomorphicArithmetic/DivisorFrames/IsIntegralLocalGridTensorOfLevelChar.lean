module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.Core20Slim.Development.AutomorphicArithmetic.DivisorFrames.IsIntegralUnitCharOfConductorLe
public import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.StandardOrderExtendedBasisApplyLowBlock
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ValuationDetOfMemKO
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Classical
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.List.Basic
public import Init.Data.List.Lemmas
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Group.Hom.Basic
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Hom.Instances
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Algebra.Group.Submonoid.BigOperators
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Notation.Indicator
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Block
public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Lattice
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import Mathlib.RingTheory.Valuation.Basic
public import Mathlib.RingTheory.Valuation.ValuativeRel.Basic
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.UniformSpace.Defs
public import ReciprocityTheory.NeutralLocalFields.Reciprocity

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw
  GlobalTheory.FunObj.borelSpaceKw

namespace UpperTheory.GivenInt

open GlobalTheory.StepData ValuativeRel

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

private theorem tame_int {μ : kˣ →* ℂˣ} (hμ : IsTame μ) (x : kˣ) (hx : valuation k (x : k) = 1) :
    IsIntegral ℤ ((μ x : ℂˣ) : ℂ) := by
  obtain ⟨p, hp⟩ := ValuativeRel.valuation_surjective (K := k) (uniformizer k : ValueGroupWithZero k)
  have hp0 : p ≠ 0 := by
    rintro rfl
    rw [map_zero] at hp
    exact uniformizer_ne_zero hp.symm
  refine UpperTheory.isIntegral_unitChar_of_conductor_le (Units.mk0 p hp0) 1 μ hp (fun y hy => hμ y ?_) x hx
  refine lt_of_le_of_lt hy.2 ?_
  rw [pow_one, Units.val_mk0, hp]
  exact uniformizer_lt_one

private theorem tame_det_int {a : Type*} [Fintype a] [DecidableEq a] {μ : kˣ →* ℂˣ} (hμ : IsTame μ) {g : GL a k}
    (hg : g ∈ KO k a) : IsIntegral ℤ ((μ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) :=
  tame_int hμ _ (valuation_det_of_mem_KO hg)

private theorem tame_det_inv_int {a : Type*} [Fintype a] [DecidableEq a] {μ : kˣ →* ℂˣ} (hμ : IsTame μ) {g : GL a k}
    (hg : g ∈ KO k a) : IsIntegral ℤ (((μ (Matrix.GeneralLinearGroup.det g))⁻¹ : ℂˣ) : ℂ) := by
  rw [← map_inv, ← map_inv]
  exact tame_det_int hμ (inv_mem hg)

private theorem lam_step_int {a t : Type*} [Fintype a] [DecidableEq a] [Fintype t] [DecidableEq t] (P : TypeDatum k a)
    (μ : kˣ →* ℂˣ) (hμ : IsTame μ) (hP : ∀ g, IsIntegral ℤ ((P.lam g : ℂˣ) : ℂ))
    (h : (P.step t μ hμ).J) : IsIntegral ℤ (((P.step t μ hμ).lam h : ℂˣ) : ℂ) := by
  rw [P.step_lam μ hμ h (P.corner h) (P.corner_val h), Units.val_mul, Units.val_mul]
  exact ((hP _).mul (tame_det_inv_int hμ (P.le_KO (P.corner h).2))).mul (tame_det_int hμ h.2.1)

private theorem lam_iter_int {r t : Type*} [Fintype r] [DecidableEq r] [Fintype t] [DecidableEq t] (P : TypeDatum k r)
    (μ : ℕ → kˣ →* ℂˣ) (hμ : ∀ j, IsTame (μ j)) (hP : ∀ g, IsIntegral ℤ ((P.lam g : ℂˣ) : ℂ))
    (j : ℕ) : ∀ g, IsIntegral ℤ (((P.iter t μ hμ j).lam g : ℂˣ) : ℂ) := by
  induction j with
  | zero => exact fun g => hP _
  | succ j ih => exact fun g => lam_step_int _ _ (hμ _) ih _

private theorem Phi_int {a t : Type*} [Fintype a] [DecidableEq a] (P : TypeDatum k a) (μ : kˣ →* ℂˣ) (hμ : IsTame μ)
    (hP : ∀ g, IsIntegral ℤ ((P.lam g : ℂˣ) : ℂ)) (x : Matrix (a ⊕ t) a k) :
    IsIntegral ℤ (P.Phi t μ x) := by
  by_cases h : P.Phi t μ x = 0
  · rw [h]; exact isIntegral_zero
  · obtain ⟨⟨g, hg, e⟩, h2⟩ := (P.Phi_ne_zero_iff μ).1 h
    rw [P.Phi_of_mem μ ⟨g, hg⟩ e h2]
    exact (hP _).mul (tame_det_inv_int hμ (P.le_KO hg))

private theorem parPhi_int {r s s' : Type*} [Fintype r] [DecidableEq r] (δ : kˣ →* ℂˣ)
    (hδ : ∀ x, IsIntegral ℤ ((δ x : ℂˣ) : ℂ)) (x : Matrix (r ⊕ s) (r ⊕ s') k) : IsIntegral ℤ (parPhi δ x) := by
  by_cases h : parPhi δ x = 0
  · rw [h]; exact isIntegral_zero
  · obtain ⟨⟨g, hg, e⟩, h21, h12, h22⟩ := (parPhi_ne_zero_iff δ).1 h
    rw [parPhi_of_mem δ hg e h21 h12 h22, ← map_inv]
    exact hδ _

private theorem indicator_int {X : Type*} (S : Set X) (x : X) : IsIntegral ℤ (S.indicator (1 : X → ℂ) x) := by
  classical
  rw [Set.indicator_apply]
  split_ifs
  · exact isIntegral_one
  · exact isIntegral_zero

end Local

section Global

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (w : Pl D.host.E)
variable {t : T} (hxi : ∀ x, IsIntegral ℤ ((L.xiH t).loc w x : ℂ))
include hxi

private theorem stepFn_int (j : ℕ) (x) : IsIntegral ℤ (stepFn L t w j x) := by
  unfold stepFn
  split_ifs
  · exact Phi_int _ _ (isTame_muBase w _) (lam_iter_int _ _ _ (fun _ => isIntegral_one) j) _
  · refine parPhi_int _ (fun y => ?_) _
    rw [MonoidHom.inv_apply, ← map_inv]
    exact hxi _
  · exact indicator_int _ _

private theorem givenDatum_int (B : Frames G) (Φ : G.Datum) (b : Edge) (x) :
    IsIntegral ℤ (givenDatum t w B Φ b x) := by
  rcases b with ⟨i, j⟩ | ⟨i, j⟩
  · rcases i with _ | i
    · simp only [givenDatum]
      exact stepFn_int w hxi _ _
    · simp only [givenDatum]
      exact isIntegral_zero
  · rcases j with _ | j
    · simp only [givenDatum]
      split_ifs
      · exact indicator_int _ _
      · exact isIntegral_zero
    · simp only [givenDatum]
      exact isIntegral_zero

end Global

end UpperTheory.GivenInt

theorem UpperTheory.isIntegral_localGrid_tensor_of_levelChar :
    ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T}, L.Is μ₀ → ∀ (B : Frames G) (t : T) (Φ : G.Datum) (w : Pl D.host.E) (z : (locGrid G t w).Args), IsIntegral ℤ ((givenStage t w B Φ).tensor z) := by
  intro D T L sc G μ₀ hL B t Φ w z
  obtain ⟨n, hn, ho⟩ := hL.xi_fin t
  have hxi : ∀ x, IsIntegral ℤ ((L.xiH t).loc w x : ℂ) := fun x => by
    have h1 : ((L.xiH t) ^ n).loc w x = 1 := by rw [show (L.xiH t) ^ n = 1 from ho]; rfl
    have h2 : ((L.xiH t).loc w x) ^ n = 1 := h1
    have h3 : ((L.xiH t).loc w x : ℂ) ^ n = 1 := by rw [← Units.val_pow_eq_pow_val, h2, Units.val_one]
    exact IsIntegral.of_pow hn (h3 ▸ isIntegral_one)
  show ((GlobalTheory.SplitFlip.givenPath D.R.m).map fun b => givenDatum t w B Φ b (z b)).prod ∈ integralClosure ℤ ℂ
  refine list_prod_mem fun y hy => ?_
  obtain ⟨b, -, rfl⟩ := List.mem_map.1 hy
  exact UpperTheory.GivenInt.givenDatum_int w hxi B Φ b _
