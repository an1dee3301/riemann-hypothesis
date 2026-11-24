module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockV
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveFrameDatumZetaIntegralEqSmaller
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumVolShellInterTranslate
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.MirabolicSchwartzFunctionLeftGLEquivariance
public import Init.Classical
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Action.Units
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Pi
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Pointwise
public import Mathlib.Algebra.NoZeroSMulDivisors.Basic
public import Mathlib.Algebra.NoZeroSMulDivisors.Defs
public import Mathlib.Algebra.Notation.Indicator
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Pi
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Group.Arithmetic
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.MeasureTheory.OuterMeasure.AE
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Fin.Basic
public import Mathlib.Order.Monotone.Defs
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.Valuation.Integers
public import Mathlib.RingTheory.Valuation.ValuativeRel.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Instances.Matrix

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram blkU conjU UB)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple UAt ratU mat Acts SInf)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
attribute [local instance] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.measFv GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.borelFv
attribute [local instance] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.measFv GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.borelFv
open GlobalTheory.PureMatch GlobalTheory.SquareFlipReach ValuativeRel

noncomputable section

open GlobalTheory.OneSquareZeta

theorem GlobalTheory.LeftTranslateZeta.bigF_phiA_left : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]
    (a : ℕ) (A' C : Type) [Fintype A'] [DecidableEq A'] [Fintype C] [DecidableEq C] (μ : Measure (GL A' k)) [μ.IsHaarMeasure]
    (σ : Fin a ⊕ A' ≃ C) (ν : kˣ →* ℂˣ) (ϖ : kˣ) (n : ℕ) (c : C → kˣ) (Ψ : Matrix A' C k → ℂ) (g₀ : GL (Fin a) k) (h : GL C k),
    IsUnif ϖ →
    bigF (haarVol (KO k (Fin a))) ϖ ν (fun Z => phiA μ σ ν ϖ n (diagLat c) Ψ (g₀.val * Z)) (X0 k σ * (invT h).val) *
      (ν (gdet g₀) : ℂ) * apow (gdet g₀) ((Fintype.card C : ℂ) / 2) = fFun μ σ ν Ψ (X0 k σ * (invT h).val) := by
  intro k _ _ _ _ _ _ a A' C _ _ _ _ μ _ σ ν ϖ n c Ψ g₀ h hϖ

  have hlat : latA ϖ n (diagLat c) = diagLat (fun j => (ϖ ^ n)⁻¹ * (c j)⁻¹) := by
    rw [latA, dualLat_diagLat, smul_diagLat]
  have hrank : (X0 k σ * (invT h).val).rank = a := by
    rw [(rank_eq_card_iff_exists_frameMatrixFirstColumnBlock σ (X0 k σ * (invT h).val)).2 ⟨h, rfl⟩, Fintype.card_fin]

  obtain ⟨g₁, hg₁⟩ := exists_primFrame (fun j => (ϖ ^ n)⁻¹ * (c j)⁻¹) _ hrank
  rw [← hlat] at hg₁
  have hκ : (ν (gdet g₀) : ℂ) * apow (gdet g₀) ((Fintype.card C : ℂ) / 2) ≠ 0 :=
    mul_ne_zero (Units.ne_zero _) (apow_ne_zero _ _)

  have hpt : ∀ g : GL (Fin a) k,
      phiA μ σ ν ϖ n (diagLat c) Ψ (g₀.val * (g.val * (X0 k σ * (invT h).val))) * (ν (gdet g) : ℂ) *
        apow (gdet g) ((Fintype.card C : ℂ) / 2) =
      {g | g₀ * g * g₁⁻¹ ∈ KO k (Fin a)}.indicator
        (fun _ => fFun μ σ ν Ψ (X0 k σ * (invT h).val) /
          ((ν (gdet g₀) : ℂ) * apow (gdet g₀) ((Fintype.card C : ℂ) / 2))) g := by
    intro g
    have hgX : g₀.val * (g.val * (X0 k σ * (invT h).val)) = g₀.val * g.val * (X0 k σ * (invT h).val) :=
      (Matrix.mul_assoc _ _ _).symm
    rw [hgX]
    have key := fFun_mul_left (μ := μ) (σ := σ) (ν := ν) (Ψ := Ψ) (g := g₀ * g) (h := h)
    simp only [apow_mul, map_mul, Units.val_mul] at key
    by_cases hS : g₀ * g * g₁⁻¹ ∈ KO k (Fin a)
    · have hP : IsPrimFrame (latA ϖ n (diagLat c)) ((g₀ * g).val * (X0 k σ * (invT h).val)) :=
        (isPrimFrame_mul_iff hg₁ (g₀ * g)).2 hS
      rw [Units.val_mul] at hP
      rw [Set.indicator_of_mem (show g ∈ {g | g₀ * g * g₁⁻¹ ∈ KO k (Fin a)} from hS), phiA, if_pos hP,
        eq_div_iff hκ, ← key]
      ring
    · have hP : ¬ IsPrimFrame (latA ϖ n (diagLat c)) ((g₀ * g).val * (X0 k σ * (invT h).val)) :=
        fun hP => hS ((isPrimFrame_mul_iff hg₁ (g₀ * g)).1 hP)
      rw [Units.val_mul] at hP
      rw [Set.indicator_of_notMem (show g ∉ {g | g₀ * g * g₁⁻¹ ∈ KO k (Fin a)} from hS), phiA, if_neg hP]
      ring

  have hsum : (∑ᶠ m : {m : Fin a → ℤ // Antitone m}, ∫ g in shellSet ϖ m.1,
      phiA μ σ ν ϖ n (diagLat c) Ψ (g₀.val * (g.val * (X0 k σ * (invT h).val))) * (ν (gdet g) : ℂ) *
        apow (gdet g) ((Fintype.card C : ℂ) / 2) ∂haarVol (KO k (Fin a))) =
      fFun μ σ ν Ψ (X0 k σ * (invT h).val) /
        ((ν (gdet g₀) : ℂ) * apow (gdet g₀) ((Fintype.card C : ℂ) / 2)) := by
    have hint : ∀ m : {m : Fin a → ℤ // Antitone m}, (∫ g in shellSet ϖ m.1,
        phiA μ σ ν ϖ n (diagLat c) Ψ (g₀.val * (g.val * (X0 k σ * (invT h).val))) * (ν (gdet g) : ℂ) *
          apow (gdet g) ((Fintype.card C : ℂ) / 2) ∂haarVol (KO k (Fin a))) =
        (haarVol (KO k (Fin a))).real (shellSet ϖ m.1 ∩ {g | g₀ * g * g₁⁻¹ ∈ KO k (Fin a)}) •
          (fFun μ σ ν Ψ (X0 k σ * (invT h).val) /
            ((ν (gdet g₀) : ℂ) * apow (gdet g₀) ((Fintype.card C : ℂ) / 2))) := by
      intro m
      rw [integral_congr_ae (ae_of_all _ hpt)]
      refine (setIntegral_indicator ?_).trans (setIntegral_const (E := ℂ)
        (fFun μ σ ν Ψ (X0 k σ * (invT h).val) /
          ((ν (gdet g₀) : ℂ) * apow (gdet g₀) ((Fintype.card C : ℂ) / 2))))
      let : MeasurableSpace (GL (Fin a) k) := Units.instMeasurableSpace
      exact (ShellVolume.isOpen_translate g₀ g₁⁻¹).measurableSet
    rw [finsum_congr hint, ← finsum_smul,
      ShellVolume.finsum_vol_shell_inter_translate k a ϖ g₀ g₁⁻¹ hϖ, one_smul]
  unfold bigF shellSum shell
  refine (congrArg (fun s => s * (ν (gdet g₀) : ℂ) * apow (gdet g₀) ((Fintype.card C : ℂ) / 2)) hsum).trans ?_
  rw [mul_assoc]
  exact div_mul_cancel₀ _ hκ

end
