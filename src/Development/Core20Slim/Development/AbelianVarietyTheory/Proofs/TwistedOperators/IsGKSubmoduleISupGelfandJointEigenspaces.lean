module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.RangeSndRel
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsAllTiedNotStable
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesHermitianUniqueOfClassification
public import Development.Core20Slim.Development.AbelianVarietyTheory.BlockTheory.HeightDefect.FinitePartTypes
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.HeightProofs.AutomorphicFormUniformLimitDiscreteSeriesSeriesStatement
public import Development.Core20Slim.Formalism.LocalToGlobal.IndefiniteReal.MultLemmas
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSumOfMemMultSpan
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.KStableOfIsGKSub
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSmoothAutomorphicFunctionTranslateAtRealPlace
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.FoundationProofs.RderMemAutFormsCuspForms
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothAutomorphicFormRightTranslateFiniteAdelic
public import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.ConjAtFixedIff
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DifferentiableOneP
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CenterActionSmoothCommuting
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RightTranslateCommutesCenterAction
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsAutFunSmOfMemGkGen
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedSmooth
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Lattice.Indexed
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.Order.Bounds.Defs
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Order.ConditionallyCompletePartialOrder.Defs
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.SetNotation
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical

noncomputable section

namespace GlobalTheory.GKEigen

theorem isGKSub_iSup_eigen : ∀ {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D) (S : D.what₂.Tau → SPar)
    (M : Formalism.IndefR.Mult.DSModel V S), IsInfFam (D := D) θ → ∀ ψ : GA D V → ℂ, IsAutFunSm θ V ψ →
    ∀ C : Finset (D.what₂.Tau × ℕ → ℂ), GlobalTheory.CuspGK.IsGKSub θ M (⨆ c ∈ C, Submodule.span ℂ
      {h | h ∈ GlobalTheory.CuspGK.gkGen θ M ψ ∧ ∀ i : D.what₂.Tau × ℕ, gelf θ V i.1 i.2 h = c i • h}) := by
  intro D θ V S M hθ ψ hψ C
  have hG : GlobalTheory.CuspGK.IsGKSub θ M (GlobalTheory.CuspGK.gkGen θ M ψ) := by
    constructor
    · intro τ g hg f hf
      exact Submodule.mem_sInf.2 fun A hA => hA.2.k τ g hg f (Submodule.mem_sInf.1 hf A hA)
    · intro τ X hX f hf
      exact Submodule.mem_sInf.2 fun A hA => hA.2.lie τ X hX f (Submodule.mem_sInf.1 hf A hA)
  have hsm : ∀ f ∈ GlobalTheory.CuspGK.gkGen θ M ψ, f ∈ GlobalTheory.Mem.AutSpace.SmFun θ V := fun f hf =>
    (GlobalTheory.KTypeAdm.isAutFunSm_of_mem_gkGen θ M hθ hψ f hf).smooth
  set T : Set (GA D V → ℂ) := ⋃ c ∈ C,
    {h | h ∈ GlobalTheory.CuspGK.gkGen θ M ψ ∧ ∀ i : D.what₂.Tau × ℕ, gelf θ V i.1 i.2 h = c i • h} with hTdef
  have hspan : (⨆ c ∈ C, Submodule.span ℂ
      {h | h ∈ GlobalTheory.CuspGK.gkGen θ M ψ ∧ ∀ i : D.what₂.Tau × ℕ, gelf θ V i.1 i.2 h = c i • h}) =
      Submodule.span ℂ T := by
    rw [hTdef, Submodule.span_iUnion₂]
  rw [hspan]
  have hTG : T ⊆ GlobalTheory.CuspGK.gkGen θ M ψ := by
    intro h hh
    rw [hTdef, Set.mem_iUnion₂] at hh
    obtain ⟨c, _, hh, _⟩ := hh
    exact hh
  have hSG : Submodule.span ℂ T ≤ GlobalTheory.CuspGK.gkGen θ M ψ := Submodule.span_le.2 hTG
  have hTk : ∀ τ g, GlobalTheory.CuspGK.InK M τ g → ∀ h ∈ T, rTr V (atTau θ V τ g) h ∈ T := by
    intro τ g hg h hh
    rw [hTdef, Set.mem_iUnion₂] at hh ⊢
    obtain ⟨c, hc, hhG, he⟩ := hh
    refine ⟨c, hc, hG.k τ g hg h hhG, fun i => ?_⟩
    rw [GlobalTheory.RegSch.CentreRight.gelf_rTr_all hθ _ i.1 i.2 (hsm h hhG), he i]
    rfl
  have hTl : ∀ τ, ∀ X ∈ lieAt V τ, ∀ h ∈ T, Rder θ V τ X h ∈ T := by
    intro τ X hX h hh
    rw [hTdef, Set.mem_iUnion₂] at hh ⊢
    obtain ⟨c, hc, hhG, he⟩ := hh
    refine ⟨c, hc, hG.lie τ X hX h hhG, fun i => ?_⟩
    rw [GlobalTheory.CuspLie.gelf_Rder hθ hX (hsm h hhG) i.1 i.2, he i, GlobalTheory.Mem.AutSpace.Rder_smul]
  refine ⟨fun τ g hg f hf => ?_, fun τ X hX f hf => ?_⟩
  · induction hf using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span (hTk τ g hg x hx)
    | zero => exact (Submodule.span ℂ T).zero_mem
    | add x y _ _ hx hy => exact (Submodule.span ℂ T).add_mem hx hy
    | smul a x _ hx => exact (Submodule.span ℂ T).smul_mem a hx
  · induction hf using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span (hTl τ X hX x hx)
    | zero =>
      rw [Formalism.IndefR.Mult.rder_zero θ V τ X]
      exact (Submodule.span ℂ T).zero_mem
    | add x y hx' hy' hx hy =>
      rw [GlobalTheory.Mem.AutSpace.Rder_add (hsm x (hSG hx')) (hsm y (hSG hy')) hX]
      exact (Submodule.span ℂ T).add_mem hx hy
    | smul a x _ hx =>
      rw [GlobalTheory.Mem.AutSpace.Rder_smul]
      exact (Submodule.span ℂ T).smul_mem a hx

end GlobalTheory.GKEigen

end
