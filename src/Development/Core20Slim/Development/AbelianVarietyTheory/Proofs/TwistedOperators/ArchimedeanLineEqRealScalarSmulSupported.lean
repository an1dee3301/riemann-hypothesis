module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.FockOrthogonalDecomposition
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsInverseChart
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Classical
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.Algebra.Algebra.Prod
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Notation.Prod
public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Equiv
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Pi
public import Mathlib.Algebra.Ring.Prod
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.WithAbs
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
public import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Topology.Algebra.Algebra
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.EMetricSpace.Defs
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.Instances.RealVectorSpace
public import Mathlib.Topology.Maps.Basic
public import Mathlib.Topology.MetricSpace.Algebra
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.MetricSpace.Isometry
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

noncomputable section

namespace GlobalTheory.LineRealAd

theorem continuous_mixedSpace_symm (K : Type) [Field K] [NumberField K] :
    Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm := by
  refine continuous_pi fun v => ?_
  rcases v.isReal_or_isComplex with hv | hv
  · rw [(InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hv).isEmbedding.continuous_iff]
    exact ((continuous_apply _).comp continuous_fst).congr fun y =>
      (congrFun (congrArg Prod.fst ((InfiniteAdeleRing.ringEquiv_mixedSpace K).apply_symm_apply y)) ⟨v, hv⟩).symm
  · rw [(InfinitePlace.Completion.isometry_extensionEmbedding v).isEmbedding.continuous_iff]
    exact ((continuous_apply _).comp continuous_snd).congr fun y =>
      (congrFun (congrArg Prod.snd ((InfiniteAdeleRing.ringEquiv_mixedSpace K).apply_symm_apply y)) ⟨v, hv⟩).symm

variable {D : D7}

theorem infPart_smul (a : AF D.host.F) (x : AE D) :
    infPart D (a • x) = (a.1 ⊗ₜ[D.host.F] (1 : D.host.E)) * infPart D x := by
  rw [Algebra.smul_def, map_mul]
  rfl

theorem finPart_smul (a : AF D.host.F) (x : AE D) :
    finPart D (a • x) = (a.2 ⊗ₜ[D.host.F] (1 : D.host.E)) * finPart D x := by
  rw [Algebra.smul_def, map_mul]
  rfl

theorem theta_realAd {θ : InfFam D} (hθ : IsInfFam θ) (ρ : D.what₂.Tau) (t : ℝ) :
    θ ρ ((GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t).1 ⊗ₜ[D.host.F] (1 : D.host.E)) = t := by
  let g : ℝ →+* ℂ := (θ ρ).comp ((Algebra.TensorProduct.includeLeftRingHom (R := D.host.F) (B := D.host.E)).comp
    ((InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F).symm.toRingHom.comp (algebraMap ℝ _)))
  have hg : Continuous g :=
    (hθ ρ).2.comp ((continuous_mixedSpace_symm _).comp (continuous_algebraMap ℝ _))
  have h : g (t • (1 : ℝ)) = t • g 1 := map_real_smul g.toAddMonoidHom hg t 1
  rw [smul_eq_mul, mul_one, map_one, Complex.real_smul, mul_one] at h
  exact h

end GlobalTheory.LineRealAd

namespace GlobalTheory.LineRealAd

theorem lineAt_realAd_smul : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ {m n : ℕ} (τ : D.what₂.Tau) (z : Matrix (Fin m) (Fin n) ℂ),
    (∀ t : ℝ, lineAt θ τ z t = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t • lineAt θ τ z 1) ∧
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) (lineAt θ τ z 1) := by
  classical
  intro D θ hθ m n τ z
  have hL : IsLineAt θ τ z (lineAt θ τ z) :=
    Classical.epsilon_spec (GlobalTheory.RealLineAt.lineAt_exists D θ hθ m n τ z)
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  have hfin : ∀ t i j, finPart D (lineAt θ τ z t i j) = 0 := fun t i j => congrFun (congrFun (hL.2.1 t) i) j
  have hcomp : ∀ t τ' i j, θ τ' (infPart D (lineAt θ τ z t i j)) =
      (if τ' = τ then (t : ℂ) • z else 0) i j := fun t τ' i j => congrFun (congrFun (hL.2.2 t τ') i) j
  refine ⟨fun t => ?_, fun u hu => ?_⟩
  · funext i j
    refine sub_eq_zero.1 (hσ.ext _ ?_ fun τ' => ?_)
    · show finPart D (lineAt θ τ z t i j - GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t • lineAt θ τ z 1 i j) = 0
      rw [RingHom.map_sub, finPart_smul, hfin, hfin, mul_zero, sub_zero]
    · show θ τ' (infPart D (lineAt θ τ z t i j - GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t • lineAt θ τ z 1 i j)) = 0
      rw [RingHom.map_sub, infPart_smul, RingHom.map_sub, RingHom.map_mul, theta_realAd hθ, hcomp, hcomp]
      split_ifs <;> simp
  · funext i j
    have hu1 : u.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F).map_eq_zero_iff.1 hu
    refine hσ.ext _ ?_ fun τ' => ?_
    · show finPart D (u • lineAt θ τ z 1 i j) = 0
      rw [finPart_smul, hfin, mul_zero]
    · show θ τ' (infPart D (u • lineAt θ τ z 1 i j)) = 0
      rw [infPart_smul, hu1, TensorProduct.zero_tmul, zero_mul, map_zero]

end GlobalTheory.LineRealAd
