module

public import Mathlib
public import Development.Core20Slim.Development.AutomorphicArithmetic.LocalEmbeddings.ComplEquivEvW
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ZetaIdentityPersistsRowColumnChangesStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardPairLocalZetaMatchNeZeroStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardPairMembersMemSchwartzBruhatStatement
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocPart
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardPairLocalZetaMatchNeZero
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Init.Classical
public import Init.Core
public import Init.Data.Fin.Basic
public import Init.Data.Nat.Lemmas
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Hom.Basic
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Hom.Instances
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Order.IsBotOne
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fin.SuccPred
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.Valuation.Basic
public import Mathlib.RingTheory.Valuation.Integers
public import Mathlib.RingTheory.Valuation.ValuativeRel.Basic
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.Support
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.LocallyConstant.Basic

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels ComplexConjugate
open GlobalTheory.FunObj GlobalTheory.StdFrames GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.LFun.SplitTie
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep Acts SInf At piW chrW)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

section SlopeTestRemainingChoices

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

private noncomputable def subst {m n : ℕ} (g : GL (Fin m) k) (h : GL (Fin n) k) :
    Matrix (Fin m) (Fin n) k ≃ₜ Matrix (Fin m) (Fin n) k where
  toFun X := g.val * X * h.val
  invFun X := (g⁻¹).val * X * (h⁻¹).val
  left_inv X := by
    show (g⁻¹).val * (g.val * X * h.val) * (h⁻¹).val = X
    rw [Matrix.mul_assoc g.val, ← Matrix.mul_assoc (g⁻¹).val, Units.inv_mul, Matrix.one_mul, Matrix.mul_assoc,
      Units.mul_inv, Matrix.mul_one]
  right_inv X := by
    show g.val * ((g⁻¹).val * X * (h⁻¹).val) * h.val = X
    rw [Matrix.mul_assoc (g⁻¹).val, ← Matrix.mul_assoc g.val, Units.mul_inv, Matrix.one_mul, Matrix.mul_assoc,
      Units.inv_mul, Matrix.mul_one]
  continuous_toFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  continuous_invFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const

private theorem subst_SB {m n : ℕ} (g : GL (Fin m) k) (h : GL (Fin n) k) {f : Matrix (Fin m) (Fin n) k → ℂ}
    (hf : f ∈ GlobalTheory.WeilM.SB (Matrix (Fin m) (Fin n) k)) :
    (fun X => f (g.val * X * h.val)) ∈ GlobalTheory.WeilM.SB (Matrix (Fin m) (Fin n) k) :=
  ⟨hf.1.comp_continuous (subst g h).continuous, hf.2.comp_homeomorph (subst g h)⟩

private theorem subst_ne {m n : ℕ} (g : GL (Fin m) k) (h : GL (Fin n) k) {f : Matrix (Fin m) (Fin n) k → ℂ}
    {Y : Matrix (Fin m) (Fin n) k} (hf : f Y ≠ 0) : ∃ X : Matrix (Fin m) (Fin n) k, f (g.val * X * h.val) ≠ 0 := by
  obtain ⟨X, rfl⟩ := (subst g h).surjective Y
  exact ⟨X, hf⟩

open GlobalTheory.StdPairCone in
private theorem stdA_ne (ν : kˣ →* ℂˣ) (ϖ : kˣ) (c a a' : ℕ) : ∃ X, stdA ν ϖ c a a' X ≠ 0 := by
  let X : Matrix (Fin a) (Fin (a + a')) k :=
    Matrix.of fun i => Fin.append ((1 : Matrix (Fin a) (Fin a) k) i) (fun _ => 0)
  have h1 : blk₁ X = 1 := by ext i j; simp [blk₁, X]
  have h2 : blk₂ X = 0 := by ext i j; simp [blk₂, X]
  refine ⟨X, ?_⟩
  have h : (blk₁ X).det ≠ 0 ∧ IsGLO (blk₁ X) ∧ ∀ i j, blk₂ X i j ∈ GlobalTheory.SplitWeil.cball (ϖ ^ c) := by
    rw [h1, h2]
    refine ⟨by simp, ⟨fun i j => ?_, by simp⟩, fun i j => by simp [GlobalTheory.SplitWeil.cball]⟩
    rw [Matrix.one_apply]
    split_ifs
    exacts [one_mem _, zero_mem _]
  rw [stdA, dite_eq_left h]
  exact Units.ne_zero _

open GlobalTheory.StdPairCone in
private theorem stdB_ne (ν : kˣ →* ℂˣ) (ϖ : kˣ) (c a a' : ℕ) : ∃ Y, stdB ν ϖ c a a' Y ≠ 0 := by
  let X : Matrix (Fin a') (Fin (a + a')) k :=
    Matrix.of fun i => Fin.append (fun _ => 0) ((1 : Matrix (Fin a') (Fin a') k) i)
  have h1 : blk₂ X = 1 := by ext i j; simp [blk₂, X]
  have h2 : blk₁ X = 0 := by ext i j; simp [blk₁, X]
  refine ⟨X, ?_⟩
  have h : (blk₂ X).det ≠ 0 ∧ IsGLO (blk₂ X) ∧ ∀ i j, blk₁ X i j ∈ GlobalTheory.SplitWeil.cball (ϖ ^ c) := by
    rw [h1, h2]
    refine ⟨by simp, ⟨fun i j => ?_, by simp⟩, fun i j => by simp [GlobalTheory.SplitWeil.cball]⟩
    rw [Matrix.one_apply]
    split_ifs
    exacts [one_mem _, zero_mem _]
  rw [stdB, dite_eq_left h]
  exact Units.ne_zero _

end SlopeTestRemainingChoices

theorem UpperTheory.exists_scaled_standardPairSections_of_maxCompact_translate :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]
        (α β ν : kˣ →* ℂˣ) (ϖ : kˣ) (c m a a' : ℕ), GlobalTheory.SplitFlip.IsUnif ϖ → ν = α / β → 1 ≤ c → GlobalTheory.SplitFlip.CondLE ϖ c ν →
        GlobalTheory.SplitFlip.CondLE ϖ m α → GlobalTheory.SplitFlip.CondLE ϖ m β → (∀ x, ‖(α x : ℂ)‖ = 1) → (∀ x, ‖(β x : ℂ)‖ = 1) →
        ∀ (gA : GL (Fin a) k) (gB : GL (Fin a') k) (cc : GL (Fin (a + a')) k), gA ∈ GlobalTheory.SplitWeil.KO k (Fin a) →
        ∃ (lam : ℂ) (Ξ : Matrix (Fin a) (Fin (a + a')) k → ℂ) (Ψ : Matrix (Fin a') (Fin (a + a')) k → ℂ), lam ≠ 0 ∧
          (∀ X, Ξ X = GlobalTheory.StdPairCone.stdA ν ϖ c a a' (gA.val * X * (cc⁻¹).valᵀ)) ∧
          (∀ Y, Ψ Y = lam * GlobalTheory.StdPairCone.stdB ν ϖ c a a' (gB.val * Y * cc.val)) ∧
          Ξ ∈ GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin (a + a')) k) ∧ Ψ ∈ GlobalTheory.WeilM.SB (Matrix (Fin a') (Fin (a + a')) k) ∧ Ξ ≠ 0 ∧ Ψ ≠ 0 ∧
          GlobalTheory.SplitFlip.bigP (GlobalTheory.SplitFlip.haarVol (GlobalTheory.SplitWeil.KO k (Fin a))) ϖ finSumFinEquiv ν β Ξ =
            GlobalTheory.SplitFlip.smallP (GlobalTheory.SplitFlip.haarVol (GlobalTheory.SplitWeil.KO k (Fin a'))) finSumFinEquiv ν α Ψ := by
  intro k _ _ _ _ _ _ α β ν ϖ c m a a' hϖ hν hc hcν hα hβ nα nβ gA gB cc hgA
  obtain ⟨hz, -⟩ := GlobalTheory.T.standardPair_localZetaMatch_ne_zero α β ν ϖ c m a a' hϖ hν hc hcν hα hβ nα nβ
  obtain ⟨hA, hB⟩ := GlobalTheory.T.standardPair_members_mem_schwartzBruhat ν ϖ c a a' hϖ hcν
  have hab : ν * β = α := by
    rw [hν]
    ext x
    simp
  obtain ⟨lam, hl, H⟩ := GlobalTheory.T.zetaIdentity_persists_row_column_changes k a a rfl (Fin a') (Fin a') (Fin (a + a')) (Fin (a + a')) (Equiv.refl _)
    (Equiv.refl _) finSumFinEquiv finSumFinEquiv (GlobalTheory.SplitFlip.haarVol (GlobalTheory.SplitWeil.KO k (Fin a')))
    (GlobalTheory.SplitFlip.haarVol (GlobalTheory.SplitWeil.KO k (Fin a'))) ϖ ν β gA gB cc hgA
  rw [hab] at H
  have H' := H _ _ hz
  refine ⟨lam, fun X => GlobalTheory.StdPairCone.stdA ν ϖ c a a' (gA.val * X * (GlobalTheory.SplitFlip.invT cc).val),
    fun Y => lam * GlobalTheory.StdPairCone.stdB ν ϖ c a a' (gB.val * Y * cc.val), hl, fun _ => rfl, fun _ => rfl,
    subst_SB gA _ hA, (GlobalTheory.WeilM.SB _).smul_mem lam (subst_SB gB cc hB), ?_, ?_, H'⟩
  · obtain ⟨Y, hY⟩ := stdA_ne ν ϖ c a a'
    obtain ⟨X, hX⟩ := subst_ne gA (GlobalTheory.SplitFlip.invT cc) hY
    exact fun h => hX (congrFun h X)
  · obtain ⟨Y, hY⟩ := stdB_ne ν ϖ c a a'
    obtain ⟨X, hX⟩ := subst_ne gB cc hY
    exact fun h => mul_ne_zero hl hX (congrFun h X)
