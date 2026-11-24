module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.DOpDef
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Init.Classical
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.Algebra.Algebra.Prod
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Prod
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Notation.Prod
public import Mathlib.Algebra.Order.Monoid.Unbundled.WithTop
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Pi
public import Mathlib.Algebra.Ring.Prod
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.RCLike.Lemmas
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.ENat.Basic
public import Mathlib.Data.ENat.Defs
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Sets
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Notation
public import Mathlib.Order.TypeTags
public import Mathlib.Order.WithBot
public import Mathlib.RingTheory.Finiteness.Prod
public import Mathlib.RingTheory.Trace.Defs
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.MetricSpace.Algebra
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Metrizable.Basic
public import Mathlib.Topology.Metrizable.Uniformity
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.UniformSpace.Defs
public import Mathlib.Topology.UniformSpace.Real

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Classical
open GlobalTheory.HeisOrbit

theorem GlobalTheory.HeisOrbit.dOp_contDiff_family {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (G : ℝ → SInf F κ) (Pv Qv : ℝ → (κ → mixedEmbedding.mixedSpace F)) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × (κ → mixedEmbedding.mixedSpace F) => G p.1 p.2) →
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Pv → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Qv →
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × (κ → mixedEmbedding.mixedSpace F) => GlobalTheory.HeisOrbit.dOp (Pv p.1) (Qv p.1) (G p.1) p.2) := by
  intro hG hP hQ
  have hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : (ℝ × (κ → mixedEmbedding.mixedSpace F)) × (κ → mixedEmbedding.mixedSpace F) => (G x.1.1 : (κ → mixedEmbedding.mixedSpace F) → ℂ) x.2) :=
    hG.comp ((contDiff_fst.comp contDiff_fst).prodMk contDiff_snd)
  have hD : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × (κ → mixedEmbedding.mixedSpace F) => fderiv ℝ (fun y : (κ → mixedEmbedding.mixedSpace F) => (G p.1 : (κ → mixedEmbedding.mixedSpace F) → ℂ) y) p.2) :=
    ContDiff.fderiv (f := fun (p : ℝ × (κ → mixedEmbedding.mixedSpace F)) (y : (κ → mixedEmbedding.mixedSpace F)) => (G p.1 : (κ → mixedEmbedding.mixedSpace F) → ℂ) y) hf contDiff_snd
      (le_of_eq (by simp))
  have hD' : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × (κ → mixedEmbedding.mixedSpace F) => fderiv ℝ (fun y : (κ → mixedEmbedding.mixedSpace F) => (G p.1 : (κ → mixedEmbedding.mixedSpace F) → ℂ) y) p.2 (Pv p.1)) :=
    hD.clm_apply (hP.comp contDiff_fst)
  have hS : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × (κ → mixedEmbedding.mixedSpace F) => ∑ i, p.2 i * Qv p.1 i) := by
    refine ContDiff.sum (fun i _ => ?_)
    exact ((contDiff_apply ℝ _ i).comp contDiff_snd).mul
      ((contDiff_apply ℝ _ i).comp (hQ.comp contDiff_fst))
  have hT : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × (κ → mixedEmbedding.mixedSpace F) => ((Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, p.2 i * Qv p.1 i) : ℝ) : ℂ)) := by
    have hl : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun z : mixedEmbedding.mixedSpace F => Algebra.trace ℝ (mixedEmbedding.mixedSpace F) z) :=
      (Algebra.trace ℝ (mixedEmbedding.mixedSpace F)).toContinuousLinearMap.contDiff
    exact Complex.ofRealCLM.contDiff.comp (hl.comp hS)
  have hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × (κ → mixedEmbedding.mixedSpace F) => (G p.1 : (κ → mixedEmbedding.mixedSpace F) → ℂ) p.2) := hG
  unfold GlobalTheory.HeisOrbit.dOp
  exact hD'.sub ((contDiff_const.mul hT).mul hg)
