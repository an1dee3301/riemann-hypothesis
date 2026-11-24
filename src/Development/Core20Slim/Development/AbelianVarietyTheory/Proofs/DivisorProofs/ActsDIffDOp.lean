module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinHasTemperateGrowth
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchHeisenbergDerivativesExistStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchActionReadingsCompatibleStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaussianDerivative
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsArchimedeanPairNegativeSymplecticPairing
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.LagrangianEvaluationGauss
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Classical
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Ext
public import Init.Prelude
public import Init.PropLemmas
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.Algebra.Algebra.Prod
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Invertible.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Prod
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Notation.Prod
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Pi
public import Mathlib.Algebra.Ring.Prod
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
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
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Sets
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.Order.Bounds.Defs
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.RingTheory.Trace.Defs
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.ThK.EvAt0
open GlobalTheory.ThK.EvAt0.PolD

noncomputable section

open scoped Classical

namespace GlobalTheory.ThK.EvAt0.PolEv

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

section Gen

variable {n d : ℕ} {X : Spc F E n} {W : Spc F E d}

theorem at_symm (M : Model σ X W) (a b : Fin n × Fin d → mixedEmbedding.mixedSpace F) :
    At (evI F) (M.co.e.symm (fun i => liftA (a i), fun i => liftA (b i))) := by
  intro c hc
  rw [← map_smul]
  have : c • ((fun i => liftA (a i), fun i => liftA (b i)) : (Fin n × Fin d → AF F) × (Fin n × Fin d → AF F)) = 0 := by
    ext i <;> simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, Prod.fst_zero, Prod.snd_zero, Pi.zero_apply] <;>
      exact smul_liftA hc _
  rw [this, map_zero]

theorem arc_liftA {κ : Type} (a : κ → mixedEmbedding.mixedSpace F) : arc (fun i => liftA (a i)) = a := by
  funext i; exact evI_liftA (a i)

theorem actsD_iff_dOp {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (M : Model σ X W) (u : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
    (hu : At (evI F) u) (f f₁ : SInf F (Fin n × Fin d)) :
    ActsD (evI F) (M.heisLine ψ u) f f₁ ↔ f₁ = dOp (arc (M.co.e u).1) (arc (M.co.e u).2) f := by
  obtain ⟨D, hD⟩ := GlobalTheory.T.archHeisenbergDerivatives_exist F E σ _ _ _ ψ _ _ M.co hψ
  have e : D u f = dOp (arc (M.co.e u).1) (arc (M.co.e u).2) f := by
    ext x
    rw [(hD u hu f).2 x, dOp_apply]
    rfl
  have h1 : ActsD (evI F) (M.heisLine ψ u) f (D u f) :=
    (GlobalTheory.T.archActionReadings_compatible F _ f (D u f) (D u f)).1 _ (fun t => by funext x; simp [Model.heisLine, Darboux.rho, schr])
      (hD u hu f).1
  rw [← e]
  exact ⟨fun h2 => (GlobalTheory.T.archActionReadings_compatible F _ f f₁ (D u f)).2.2.1 _ h2 h1, fun h2 => h2 ▸ h1⟩

theorem isGauss_iff {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (M : Model σ X W) (τ : ∀ w : InfinitePlace F, EmbOver E w)
    (g : SInf F (Fin n × Fin d)) : M.IsGauss ψ τ g ↔ GaussD M τ g := by
  refine exists_congr fun ε => forall₂_congr fun u u' => forall₃_congr fun hu hu' _ => ⟨fun H => ?_, fun H f f' hf hf' => ?_⟩
  · exact H _ _ ((actsD_iff_dOp hψ M u hu _ _).2 rfl) ((actsD_iff_dOp hψ M u' hu' _ _).2 rfl)
  · rw [(actsD_iff_dOp hψ M u hu _ _).1 hf, (actsD_iff_dOp hψ M u' hu' _ _).1 hf']
    exact H

theorem pol_eq {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (M : Model σ X W) (τ : ∀ w : InfinitePlace F, EmbOver E w) :
    M.Pol ψ τ = sInf {N | (∀ f₀, GaussD M τ f₀ → f₀ ∈ N) ∧
      ∀ (a b : Fin n × Fin d → mixedEmbedding.mixedSpace F), ∀ f ∈ N, dOp a b f ∈ N} := by
  unfold Model.Pol
  congr 1
  ext N
  simp only [Set.mem_setOf_eq]
  refine and_congr (forall_congr' fun f₀ => imp_congr_left (isGauss_iff hψ M τ f₀)) ⟨fun H a b f hf => ?_, fun H u hu f hf f₁ h1 => ?_⟩
  · have hu := at_symm M a b
    refine H _ hu f hf _ ((actsD_iff_dOp hψ M _ hu _ _).2 ?_)
    rw [LinearEquiv.apply_symm_apply, arc_liftA, arc_liftA]
  · rw [(actsD_iff_dOp hψ M u hu _ _).1 h1]
    exact H _ _ f hf

theorem dOp_mem {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (M : Model σ X W) (τ : ∀ w : InfinitePlace F, EmbOver E w)
    (a b : Fin n × Fin d → mixedEmbedding.mixedSpace F) {f : SInf F (Fin n × Fin d)} (hf : f ∈ M.Pol ψ τ) :
    dOp a b f ∈ M.Pol ψ τ := by
  rw [pol_eq hψ] at hf ⊢
  exact Submodule.mem_sInf.2 fun N hN => hN.2 a b f (Submodule.mem_sInf.1 hf N hN)

theorem gauss_mem {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (M : Model σ X W) (τ : ∀ w : InfinitePlace F, EmbOver E w)
    {f : SInf F (Fin n × Fin d)} (hf : GaussD M τ f) : f ∈ M.Pol ψ τ := by
  rw [pol_eq hψ]
  exact Submodule.mem_sInf.2 fun N hN => hN.1 f hf

end Gen

end GlobalTheory.ThK.EvAt0.PolEv
