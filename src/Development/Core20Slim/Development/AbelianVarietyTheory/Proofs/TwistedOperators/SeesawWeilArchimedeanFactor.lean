module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRtensOp
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawFramesWeilEquivalence
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilModelProjectionFactorisation
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.DarbouxModelAlgebraicVectorsLeAdelicSchwartz
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLocalOperatorThetaQuotientFinitePlaceStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatchedMapsDoublingFrame
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawWeilZetaResidue
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NotForallNonemptyLocP
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Classical
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
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
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Sets
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Map
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.Order.Filter.Cofinite
public import Mathlib.Order.Filter.Defs
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.TripleAssembly.EqFin

theorem liftPure_pure {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {Z : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Z)
    (ψ : AddChar (AF F) ℂ) (hM : M.IsGood ψ) {P : Type} [AddCommGroup P] [Module ℂ P]
    (pr : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d) →ₗ[ℂ] P)
    {N : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F) → Type} [∀ v, AddCommGroup (N v)] [∀ v, Module ℂ (N v)]
    (pv : ∀ v, ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] N v) (s : ∀ v, N v)
    (hs : ∀ᶠ v in Filter.cofinite, pv v (M.vac v) = s v) (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d))
    (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (Fin n × Fin d → Fv F v) → ℂ) (hφ : ∀ v, φ v ∈ GlobalTheory.WeilM.SB _)
    (hφv : ∀ᶠ v in Filter.cofinite, φ v = M.vac v) :
    GlobalTheory.TripleAssembly.liftPure M pr pv s (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) =
      pr f ⊗ₜ GlobalTheory.SmallThetaModules.pureT s (fun v => pv v (φ v)) := by
  have H := GlobalTheory.PureLift.exists_pureLift σ Y Z M ψ hM P pr N pv s hs
  unfold GlobalTheory.TripleAssembly.liftPure
  rw [dite_eq_left H]
  exact H.choose_spec f φ hφ hφv

theorem darbAlg_stable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {Z : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Z)
    (ψ : AddChar (AF F) ℂ) (τ : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver (E := E) w) (hM : M.IsGood ψ)
    {P : Type} [AddCommGroup P] [Module ℂ P] (pr : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d) →ₗ[ℂ] P)
    {N : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F) → Type} [∀ v, AddCommGroup (N v)] [∀ v, Module ℂ (N v)]
    (pv : ∀ v, ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] N v) (s : ∀ v, N v)
    (hs : ∀ᶠ v in Filter.cofinite, pv v (M.vac v) = s v)
    (O : Module.End ℂ ((Fin n × Fin d → AF F) → ℂ)) (T₀ : Module.End ℂ (GlobalTheory.SmallThetaModules.RTens s))
    (hgen : ∀ (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)) (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (Fin n × Fin d → Fv F v) → ℂ),
      (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) → (∀ᶠ v in Filter.cofinite, φ v = M.vac v) →
      ∃ φ₁ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (Fin n × Fin d → Fv F v) → ℂ,
        (∀ v, φ₁ v ∈ GlobalTheory.WeilM.SB _) ∧ (∀ᶠ v in Filter.cofinite, φ₁ v = M.vac v) ∧
        O (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ₁ ∧
        GlobalTheory.SmallThetaModules.pureT s (fun v => pv v (φ₁ v)) = T₀ (GlobalTheory.SmallThetaModules.pureT s (fun v => pv v (φ v)))) :
    ∀ Ψ ∈ GlobalTheory.TripleAssembly.darbAlg M ψ τ, O Ψ ∈ GlobalTheory.TripleAssembly.darbAlg M ψ τ ∧
      GlobalTheory.TripleAssembly.liftPure M pr pv s (O Ψ) = LinearMap.lTensor P T₀ (GlobalTheory.TripleAssembly.liftPure M pr pv s Ψ) := by
  intro Ψ hΨ
  induction hΨ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, φ, hf, hφ, hφv, rfl⟩ := hx
    obtain ⟨φ₁, h1, h1v, hO, hT⟩ := hgen f φ hφ hφv
    refine ⟨?_, ?_⟩
    · rw [hO]; exact Submodule.subset_span ⟨f, φ₁, hf, h1, h1v, rfl⟩
    · rw [hO, liftPure_pure M ψ hM pr pv s hs f φ₁ h1 h1v, liftPure_pure M ψ hM pr pv s hs f φ hφ hφv,
        LinearMap.lTensor_tmul, hT]
  | zero => simp
  | add x y _ _ hx hy =>
    refine ⟨?_, ?_⟩
    · rw [map_add (f := _)]; exact Submodule.add_mem _ hx.1 hy.1
    · simp only [map_add (f := _), hx.2, hy.2]
  | smul c x _ hx =>
    refine ⟨?_, ?_⟩
    · rw [map_smul]; exact Submodule.smul_mem _ c hx.1
    · simp only [map_smul, hx.2]

end GlobalTheory.TripleAssembly.EqFin

namespace GlobalTheory.TripleAssembly.EqFin


end GlobalTheory.TripleAssembly.EqFin

end
