module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousComplEquivSymm
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsLocIsoRefl
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ZetaIdentityTransportLocalFieldIso
public import Init.Classical
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Nat.Basic
public import Init.Data.Sum.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Equiv
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Group.Arithmetic
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.MeasurableSpace.Embedding
public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.OuterMeasure.AE
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.Order.Filter.Basic
public import Mathlib.RingTheory.Valuation.ValuativeRel.Basic
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Instances.Matrix

@[expose] public section

open MeasureTheory ValuativeRel Matrix
open scoped Pointwise
open GlobalTheory.SplitFlip GlobalTheory.FlipMatch GlobalTheory.FlipMatch.FieldTransport GlobalTheory.PureMatch.Transport

noncomputable section
namespace GlobalTheory.PureMatch.Transport

section
variable {k k' : Type} [Field k] [Field k'] {A A' D A₂ A₂' D₂ : Type} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A'] [Fintype D] [DecidableEq D] [Fintype A₂] [DecidableEq A₂] [Fintype A₂'] [DecidableEq A₂'] [Fintype D₂] [DecidableEq D₂]

theorem gdet_glTrEquiv_ffun (j : k ≃+* k') (e : D₂ ≃ D) (g : GL D k) :
    gdet (glTrEquiv j e g) = Units.map (j : k →* k') (gdet g) := by
  apply Units.ext
  show (glTrEquiv j e g).val.det = j g.val.det
  rw [glTrEquiv_val, show trM j e e g.val = (g.val.map j).submatrix e e from rfl, det_submatrix_equiv_self]
  exact ((j : k →+* k').map_det g.val).symm

theorem invT_glTrEquiv_ffun (j : k ≃+* k') (e : D₂ ≃ D) (g : GL D k) :
    (invT (glTrEquiv j e g)).val = trM j e e (invT g).val := by
  have h1 : (invT (glTrEquiv j e g)).val = ((glTrEquiv j e g)⁻¹).valᵀ := rfl
  have h2 : (invT g).val = (g⁻¹).valᵀ := rfl
  rw [h1, h2, ← map_inv, glTrEquiv_val]
  rfl

end

theorem fFun_trM : ∀ {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] {j : k ≃+* k'} {A A' D A₂ A₂' D₂ : Type} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A'] [Fintype D] [DecidableEq D] [Fintype A₂] [DecidableEq A₂] [Fintype A₂'] [DecidableEq A₂'] [Fintype D₂] [DecidableEq D₂] [MeasurableSpace k] [BorelSpace k] [MeasurableSpace k'] [BorelSpace k'] (hj : IsLocIso j) (rA : A₂ ≃ A) (rA' : A₂' ≃ A') (cD : D₂ ≃ D) (μ₂ : Measure (GL A₂' k')) [μ₂.IsHaarMeasure] (σ₂ : A₂ ⊕ A₂' ≃ D₂) (σ : A ⊕ A' ≃ D), (∀ s, cD (σ₂ s) = σ (Sum.map rA rA' s)) → ∀ (ν₂ : k'ˣ →* ℂˣ) (ν : kˣ →* ℂˣ), (∀ x, ν x = ν₂ (Units.map (j : k →* k') x)) → ∀ (Ψ : Matrix A₂' D₂ k' → ℂ) (Z : Matrix A D k), fFun μ₂ σ₂ ν₂ Ψ (trM j rA cD Z) = fFun (pullMeas hj rA' μ₂) σ ν (fun Y => Ψ (trM j rA' cD Y)) Z := by
  intro k k' _ _ _ _ _ _ _ _ j A A' D A₂ A₂' D₂ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hj rA rA' cD μ₂ _ σ₂ σ hσ ν₂ ν hν Ψ Z
  have hcard : Fintype.card D₂ = Fintype.card D := Fintype.card_congr cD
  have hX : ∀ M : Matrix D D k, trM j rA cD (X0 k σ * M) = X0 k' σ₂ * trM j cD cD M := fun M => by
    ext r c
    rw [trM_apply, frameMatrixFirstColumnBlock_mul_apply, frameMatrixFirstColumnBlock_mul_apply, trM_apply, hσ]; rfl
  have hY : ∀ M : Matrix D D k, trM j rA' cD (Y0 k σ * M) = Y0 k' σ₂ * trM j cD cD M := fun M => by
    ext r c
    rw [trM_apply, frameMatrixSecondColumnBlock_mul_apply, frameMatrixSecondColumnBlock_mul_apply, trM_apply, hσ]; rfl
  have hS : ∀ Y : Matrix A' D k, smallF μ₂ ν₂ Ψ (trM j rA' cD Y) =
      smallF (pullMeas hj rA' μ₂) ν (fun Y => Ψ (trM j rA' cD Y)) Y := fun Y => by
    conv_lhs => rw [← map_pullMeas hj rA' μ₂]
    unfold smallF
    have := integral_map_equiv (μ := pullMeas hj rA' μ₂) (glTr hj rA').toHomeomorph.toMeasurableEquiv
      (fun g => Ψ (g.val * trM j rA' cD Y) * (ν₂ (gdet g) : ℂ) * apow (gdet g) ((Fintype.card D₂ : ℂ) / 2))
    refine Eq.trans this ?_
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    show Ψ ((glTrEquiv j rA' g).val * trM j rA' cD Y) * ν₂ (gdet (glTrEquiv j rA' g)) *
      apow (gdet (glTrEquiv j rA' g)) _ = _
    rw [gdet_glTrEquiv_ffun, apow_map hj, ← hν, glTrEquiv_val, ← trM_mul, hcard]
  by_cases h : ∃ h : GL D k, Z = X0 k σ * (invT h).val
  · obtain ⟨h, rfl⟩ := h
    rw [hX, ← invT_glTrEquiv_ffun, splitTheta_fFun_frameFirstBlock_mul, splitTheta_fFun_frameFirstBlock_mul, gdet_glTrEquiv_ffun, apow_map hj, ← hν,
      glTrEquiv_val, ← hY, hS, hcard]
  · have h' : ¬ ∃ h₂ : GL D₂ k', trM j rA cD Z = X0 k' σ₂ * (invT h₂).val := by
      rintro ⟨h₂, H⟩
      obtain ⟨g, rfl⟩ := (glTrEquiv j cD).surjective h₂
      rw [invT_glTrEquiv_ffun, ← hX] at H
      exact h ⟨g, trM_injective j rA cD H⟩
    rw [fFun, fFun, dite_eq_right h, dite_eq_right h']

end GlobalTheory.PureMatch.Transport
