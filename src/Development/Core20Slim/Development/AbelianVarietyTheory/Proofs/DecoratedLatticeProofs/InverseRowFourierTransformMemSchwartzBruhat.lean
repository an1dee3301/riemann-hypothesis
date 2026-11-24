module

public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFrameCol
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HermitianLinkMapAdditiveRationalEquivariant
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilCharacterSplitPlaceExistsContinuousNontrivia
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergFrameHalfInverse
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierTransformInversionLocalFieldPi
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PartialFourierInversion
public import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AddCharConductorAndHaarIntegersExist
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.UnitBall
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.RingTheory.Valuation.ValuativeRel.Basic
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.Support
public import Mathlib.Topology.Algebra.ValuativeRel.ValuativeTopology
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Compactness.LocallyCompact
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Topology.Separation.Hausdorff

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.KappaModel

theorem finv_mem_SB : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (ψk : AddChar k Circle) (ν : Measure k), Continuous ψk → ψk ≠ 1 → ν.IsAddHaarMeasure → ∀ (C : ℂ) (Φ : Matrix Unit n k → ℂ), Φ ∈ SB (Matrix Unit n k) → GlobalTheory.KappaModel.finv ψk ν C Φ ∈ SB (Matrix n Unit k) := by
  intro k _ _ _ _ _ _ n _ _ ψk ν hψ hne hν C Φ hΦ
  have := secondCountable k
  have := t2Space k
  obtain ⟨c, hc⟩ := (GlobalTheory.SplitWeil.conductor_exists k).1 ψk hψ hne
  let e : (n → k) ≃ₜ Matrix Unit n k :=
    { toFun := fun η => Matrix.of fun _ r => η r
      invFun := fun M => M ()
      left_inv := fun _ => rfl
      right_inv := fun M => by ext i j; rfl
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  let e' : Matrix n Unit k ≃ₜ (n → k) :=
    { toFun := fun x r => x r ()
      invFun := fun y => Matrix.of fun r _ => y r
      left_inv := fun M => by ext i j; rfl
      right_inv := fun _ => rfl
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  have hf : (fun η : n → k => Φ (Matrix.of fun _ r => η r)) ∈ SB (n → k) :=
    ⟨hΦ.1.comp_continuous e.continuous, hΦ.2.comp_homeomorph e⟩
  have hF := FourierPi.fourier_mem_SB (Measure.pi fun _ : n => ν) hc hf
  have eq : finv ψk ν C Φ = fun x => C * (fun y : n → k => ∫ η, Φ (Matrix.of fun _ r => η r) * (ψk (η ⬝ᵥ y) : ℂ) ∂(Measure.pi fun _ : n => ν)) (e' x) := by
    funext x; rfl
  rw [eq]
  refine ⟨?_, ?_⟩
  · exact (hF.1.comp_continuous e'.continuous).comp (fun z => C * z)
  · exact (hF.2.comp_homeomorph e').mul_left

end GlobalTheory.KappaModel
