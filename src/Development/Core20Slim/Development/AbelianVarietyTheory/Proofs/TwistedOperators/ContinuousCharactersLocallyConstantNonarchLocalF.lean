module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FourierJacobiAverage
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsOpenKerOfContinuous
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
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.UnitBall
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.RingTheory.Valuation.ValuativeRel.Basic
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage
open Filter Topology

namespace GlobalTheory.RootEx.OpenKernel


open MeasureTheory ValuativeRel Matrix in
open Filter Topology in
theorem _root_.GlobalTheory.RootEx.OpenKernel.isLocallyConstant_coe_addChar {k : Type} [Field k]
    [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (hψ : Continuous ψ) :
    IsLocallyConstant (fun x : k => (ψ x : ℂ)) := by
  by_cases h : ψ = 1
  · subst h
    simp only [AddChar.one_apply, Circle.coe_one]
    exact IsLocallyConstant.const 1
  · obtain ⟨c, hc⟩ := _root_.GlobalTheory.SplitWeil.exists_hasConductor_of_continuous ψ hψ h
    exact (_root_.GlobalTheory.SplitWeil.HasConductor.isLocallyConstant hc).comp _


open MeasureTheory ValuativeRel Matrix in
open Filter Topology in
theorem _root_.GlobalTheory.RootEx.OpenKernel.characters_locallyConstant : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], (∀ μ : kˣ →* ℂˣ, Continuous μ → IsOpen (μ.ker : Set kˣ)) ∧ ∀ ψ : AddChar k Circle, Continuous ψ → IsLocallyConstant (fun x : k => (ψ x : ℂ)) :=
  fun _ _ _ _ _ => ⟨fun μ hμ => _root_.GlobalTheory.RootEx.UniformLattices.isOpen_ker_of_continuous μ hμ,
    fun ψ hψ => _root_.GlobalTheory.RootEx.OpenKernel.isLocallyConstant_coe_addChar ψ hψ⟩

end GlobalTheory.RootEx.OpenKernel
