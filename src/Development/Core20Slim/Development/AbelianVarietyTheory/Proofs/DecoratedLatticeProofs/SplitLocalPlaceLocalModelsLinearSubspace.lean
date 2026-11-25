module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacesToAdeles
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.AllPositions
public import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Pi
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
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
public import Mathlib.Data.ENat.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.Order.Notation
public import Mathlib.Order.TypeTags
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Valuation.ValuativeRel.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LocMod.LinSpace

variable {D : D7}

theorem heisO_add' (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (u : WO S T) (f g : WO S T → ℂ) :
    heisO ψ S T u (f + g) = heisO ψ S T u f + heisO ψ S T u g := by
  funext w; simp [heisO, mul_add]

theorem heisO_smul' (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (u : WO S T) (c : ℂ) (f : WO S T → ℂ) :
    heisO ψ S T u (c • f) = c • heisO ψ S T u f := by
  funext w; simp [heisO]; ring

theorem heisO_zero' (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (u : WO S T) :
    heisO ψ S T u 0 = 0 := by
  funext w; simp [heisO]

theorem isThetaFunO_zero (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) : IsThetaFunO ψ S T 0 := {
  quasi := by intro γ w; simp
  level := ⟨⊤, isOpen_univ, fun u _ _ => heisO_zero' ψ S T u⟩
  cont := continuous_const
  smooth := by intro k L _ _ w; exact contDiff_const }

theorem isThetaFunO_add {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {f g : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) (hg : IsThetaFunO ψ S T g) : IsThetaFunO ψ S T (f + g) := {
  quasi := by intro γ w; simp [hf.quasi, hg.quasi, mul_add]
  level := by
    obtain ⟨U, hU, hUf⟩ := hf.level
    obtain ⟨V, hV, hVg⟩ := hg.level
    refine ⟨U ⊓ V, ?_, ?_⟩
    · rw [AddSubgroup.coe_inf]; exact hU.inter hV
    · intro u hu h0
      rw [heisO_add', hUf u hu.1 h0, hVg u hu.2 h0]
  cont := hf.cont.add hg.cont
  smooth := by
    intro k L hL hL' w
    exact (hf.smooth k L hL hL' w).add (hg.smooth k L hL hL' w) }

theorem isThetaFunO_smul {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {f : WO S T → ℂ} (c : ℂ)
    (hf : IsThetaFunO ψ S T f) : IsThetaFunO ψ S T (c • f) := {
  quasi := by intro γ w; simp [hf.quasi]; ring
  level := by
    obtain ⟨U, hU, hUf⟩ := hf.level
    exact ⟨U, hU, fun u hu h0 => by rw [heisO_smul', hUf u hu h0]⟩
  cont := continuous_const.mul hf.cont
  smooth := by
    intro k L hL hL' w
    exact contDiff_const.mul (hf.smooth k L hL hL' w) }

end GlobalTheory.LocMod.LinSpace


open GlobalTheory.LocMod.LinSpace in
theorem GlobalTheory.LocMod.Place.isModel_linear : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ) (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (S T : HSp D) (FS : Frame k S.rank Y') (FT : Frame k T.rank Y), p.IsModel ψ FS FT 0 ∧ ∀ T₁ T₂, p.IsModel ψ FS FT T₁ → p.IsModel ψ FS FT T₂ → p.IsModel ψ FS FT (T₁ + T₂) ∧ ∀ c : ℂ, p.IsModel ψ FS FT (c • T₁) := by
  intro D k _ _ _ _ p ψ Y Y' _ _ _ _ S T FS FT
  refine ⟨⟨fun Φ => isThetaFunO_zero ψ S T, ?_, ?_⟩, ?_⟩
  · intro x Φ Φ' _; simp [heisO_zero']
  · intro y _ Φ Φ' _; simp [heisO_zero']
  · intro T₁ T₂ h₁ h₂
    refine ⟨⟨fun Φ => isThetaFunO_add (h₁.theta Φ) (h₂.theta Φ), ?_, ?_⟩, fun c => ⟨fun Φ => isThetaFunO_smul c (h₁.theta Φ), ?_, ?_⟩⟩
    · intro x Φ Φ' h
      simp only [LinearMap.add_apply]
      rw [h₁.trans x Φ Φ' h, h₂.trans x Φ Φ' h, heisO_add']
    · intro y hy Φ Φ' h
      simp only [LinearMap.add_apply]
      rw [h₁.modul y hy Φ Φ' h, h₂.modul y hy Φ Φ' h, heisO_add']
    · intro x Φ Φ' h
      simp only [LinearMap.smul_apply]
      rw [h₁.trans x Φ Φ' h, heisO_smul']
    · intro y hy Φ Φ' h
      simp only [LinearMap.smul_apply]
      rw [h₁.modul y hy Φ Φ' h, heisO_smul']
