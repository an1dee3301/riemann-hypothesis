module

public import Mathlib
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsCovolOne
public import Development.Core20Slim.GroundTheory.HeightsAndTheta.Theta.AdelicFourier
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TraceGramDetNeZero
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ExistsEqAdelicCharMul
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CoordinateHomeomorphRankOneTuples
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.InfiniteComponentCoordinatesAction
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.GlobalProofs.TupOfCv
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.GlobalProofs.ExistsSelfDualForm
public import Development.Core20Slim.GroundTheory.AutomorphicForms.GL2.GJMatrixAdelic
public import Development.Core20Slim.GroundTheory.GlobalFields.Adele.Topology
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Pi
public import Mathlib.Algebra.Torsor.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Cast.Pi
public import Mathlib.Data.Set.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Basic
public import Mathlib.Order.Filter.Defs
public import Mathlib.Topology.Algebra.Group.Torsor
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.Support
public import Mathlib.Topology.Compactness.LocallyCompact
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Separation.Basic
public import Mathlib.Topology.Separation.Regular
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

namespace GlobalTheory.CompanionTheory.Hypotheses₂.CompactTest

open NumberField IsDedekindDomain MeasureTheory
open GroundTheory.Global GroundTheory.Automorphic.GJMatrix GroundTheory.Heights₂.Theta
open scoped TensorProduct ENNReal Matrix NumberField.AdeleRing

theorem exists_compactSupport_ne_zero :
    ∀ (F : Type) [Field F] [NumberField F] (ι : Type) [Fintype ι] [DecidableEq ι],
      ∃ f ∈ schwartzBruhatPi (K := F) (ι := ι), HasCompactSupport f ∧ f 0 ≠ 0 := by
  intro F _ _ ι _ _
  obtain ⟨U, hUc, hU⟩ := exists_compact_mem_nhds (0 : ι → 𝔸[F])
  obtain ⟨r, -, -, hr0, hrU, hrS⟩ := GlobalTheory.CompanionTheory.Hypotheses₂.SdExist.exists_bump (K := F) 0 U hU
  refine ⟨_, hrS, HasCompactSupport.intro hUc fun x hx => ?_, ?_⟩
  · have : r x = 0 := by
      by_contra h
      exact hx (hrU x h)
    simp [this]
  · exact_mod_cast hr0.ne'

end GlobalTheory.CompanionTheory.Hypotheses₂.CompactTest
