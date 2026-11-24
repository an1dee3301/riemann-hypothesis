module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilModelCmExtension
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
public import Development.Core20Slim.Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ExistsWeilRepArchimedeanSmoothOrbit
public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerSkewPlaneUniqueDual
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityUnitary
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityReal
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Classical
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Notation.Indicator
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Notation.Prod
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Equiv
public import Mathlib.Algebra.Ring.Hom.Defs
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
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Sets
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.Order.Filter.Basic
public import Mathlib.Order.Filter.Cofinite
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Filter Topology
open GlobalTheory.AdelicU
open scoped Classical
namespace GlobalTheory.Twist.SmoothLine
theorem smooth_line_of_pure_tensor_theta : FunPr.ThetaLocalInputs → ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {Y : IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {Wd : IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Wd) (ψ : AddChar (AF F) ℂ)
    (χX χW : IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E) (om : IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Y Wd),
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ →
    IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → M.IsGood ψ → M.IsWeil ψ χX χW om →
    ∀ γ ∈ IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ Wd, ∀ (f : IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d))
      (φ : ∀ v : IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (Fin n × Fin d → Fv F v) → ℂ),
    (∀ v, φ v ∈ WeilM.SB _) → (∀ᶠ v in Filter.cofinite, φ v = M.vac v) →
    (∃ y : Fin n × Fin d → AF F, ∏ᶠ v, φ v (fun i => evFin F v (y i)) ≠ 0) →
    ∀ c : ℝ → IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d),
      (∀ t : ℝ, om (1, γ (Multiplicative.ofAdd t)) (IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = IndefiniteRowSideFullHecke.WeilTensorModels.pure (c t) φ) →
      ∃ g : IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d), Tendsto (fun t : ℝ => t⁻¹ • (c t - c 0)) (𝓝[≠] 0) (𝓝 g) := by
  intro hP F E _ _ _ _ _ σ n d Y Wd M ψ χX χW om hCM hψ hM hW γ hγ f φ hSB hvac hne c hc
  obtain ⟨c₁, c', h0, hlim, hacts⟩ := WeilArchSmooth.exists_weilRep_archimedean_smooth_orbit hP M ψ χX χW om hCM hψ hW γ hγ f
  let r : (Fin n × Fin d → AF F) → ℂ := fun x => ∏ᶠ v, φ v fun i => evFin F v (x i)
  have hstd : ∀ᶠ v in Filter.cofinite,
      φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 :=
    (hvac.and hM.std).mono fun v h => h.1.trans h.2
  have hRest : IndefiniteRowSideFullHecke.WeilTensorModels.Rest (evI F) (⇑f) r :=
    ⟨fun x z hz => finprod_add_of_at φ x z hz, TensUniq.pure_mem_schA f φ hSB hstd⟩
  obtain ⟨y, hy⟩ := hne
  have heq : ∀ t, c t = c₁ t := by
    intro t
    have h1 : IndefiniteRowSideFullHecke.WeilTensorModels.pure (c t) φ = IndefiniteRowSideFullHecke.WeilTensorModels.tens (evI F) (⇑(c₁ t)) r :=
      (hc t).symm.trans (hacts t r hRest)
    ext x
    let z : Fin n × Fin d → AF F := fun i => (show InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F from
      ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (x i),
        (show InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F from y i).2))
    have hzI : (fun i => evI F (z i)) = x := by
      funext i
      show (InfiniteAdeleRing.ringEquiv_mixedSpace F) ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (x i)) = x i
      exact RingEquiv.apply_symm_apply _ _
    have hzF : (∏ᶠ v, φ v fun i => evFin F v (z i)) = ∏ᶠ v, φ v fun i => evFin F v (y i) := rfl
    have e := congrFun h1 z
    simp only [IndefiniteRowSideFullHecke.WeilTensorModels.pure, IndefiniteRowSideFullHecke.WeilTensorModels.tens, r, hzI, hzF] at e
    exact mul_right_cancel₀ hy e
  have hc' : c = c₁ := funext heq
  subst hc'
  refine ⟨c', ?_⟩
  rw [h0]
  exact hlim
end GlobalTheory.Twist.SmoothLine
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Filter Topology
open GlobalTheory.AdelicU
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pure_tensor_theta_smooth_along_line : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {Wd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Wd) (ψ : AddChar (AF F) ℂ)
    (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Y Wd),
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ →
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → M.IsGood ψ → M.IsWeil ψ χX χW om →
    ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ Wd, ∀ (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d))
      (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (Fin n × Fin d → Fv F v) → ℂ),
    (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) → (∀ᶠ v in Filter.cofinite, φ v = M.vac v) →
    (∃ y : Fin n × Fin d → AF F, ∏ᶠ v, φ v (fun i => evFin F v (y i)) ≠ 0) →
    ∀ c : ℝ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d),
      (∀ t : ℝ, om (1, γ (Multiplicative.ofAdd t)) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (c t) φ) →
      ∃ g : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d), Tendsto (fun t : ℝ => t⁻¹ • (c t - c 0)) (𝓝[≠] 0) (𝓝 g) := by
  first | exact @_root_.GlobalTheory.Twist.SmoothLine.smooth_line_of_pure_tensor_theta | exact _root_.GlobalTheory.Twist.SmoothLine.smooth_line_of_pure_tensor_theta | (intros; apply _root_.GlobalTheory.Twist.SmoothLine.smooth_line_of_pure_tensor_theta <;> assumption)
end
