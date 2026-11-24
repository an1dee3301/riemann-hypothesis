module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearModelArchimedeanSchroedingerStandard
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedSpaceVecPairAsAdeles
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.IteratedLineDerivMemWeylAlg
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
public import Init.Core
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Prod
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Notation.Prod
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Equiv
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.Analysis.Normed.Lp.WithLp
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.Topology.Algebra.Module.Equiv.Basic
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix ENNReal Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_linear_model_archimedean_schroedinger_standard : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
    (β : mixedEmbedding.mixedSpace F →ₗ[ℝ] ℝ),
    (∀ a, ψ (((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm a, 0) : AdeleRing (𝓞 F) F) =
      Complex.exp (2 * Real.pi * Complex.I * β a)) →
    (∀ a, a ≠ 0 → ∃ b, β (a * b) ≠ 0) → ∀ (κ : Type) [Fintype κ],
    ∃ (n : ℕ) (Q : EuclideanSpace ℝ (Fin n) ≃L[ℝ] (κ → mixedEmbedding.mixedSpace F))
      (P : (Fin n ⊕ Fin n → ℝ) ≃ₗ[ℝ] ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F))),
      ∀ w (φ : (κ → mixedEmbedding.mixedSpace F) → ℂ),
        GlobalTheory.WeilAdm.schrInf F ψ (P w) φ ∘ Q = GlobalTheory.RealWeil.rhoFun w (φ ∘ Q) := by
  first | exact @GlobalTheory.WeilAdm.RealModel.exists_model | exact GlobalTheory.WeilAdm.RealModel.exists_model | (intros; apply GlobalTheory.WeilAdm.RealModel.exists_model <;> assumption)
