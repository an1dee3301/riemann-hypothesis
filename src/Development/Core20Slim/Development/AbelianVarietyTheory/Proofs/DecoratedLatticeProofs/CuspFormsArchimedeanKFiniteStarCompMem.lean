module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSmoothAutomorphicFunctionStar
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsIwasawaOfIsCompact
public import Development.AbelianVarietyTheory.Definitions.Foundations.MemL2OfBoundedContinuousInvariant
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedSmooth
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Prelude
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic

@[expose] public section

noncomputable section

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

namespace GlobalTheory.Core.Rk.CuspConj

theorem isKFinite_conj {G : Type} [Group G] {K : Subgroup G} {Φ : G → ℂ} (h : GlobalTheory.Doubling.IsKFinite K Φ) :
    GlobalTheory.Doubling.IsKFinite K fun g => conj (Φ g) := by
  unfold GlobalTheory.Doubling.IsKFinite GlobalTheory.Doubling.kSpan at *
  refine GlobalTheory.Mem.AutConj.finiteDimensional_span_star h ?_
  rintro f ⟨k, hk, rfl⟩
  refine ⟨k, hk, ?_⟩
  funext g
  show star (conj (Φ (g * k))) = Φ (g * k)
  rw [starRingEnd_apply, star_star]

theorem conj_comp_mem_A0 : ∀ (D : D7) (θ : InfFam D) (A : HSp D) (cA : CptF A), IsInfFam θ →
    ∀ u ∈ GlobalTheory.Cusp.A0 θ A cA, (fun g => conj (u g)) ∈ GlobalTheory.Cusp.A0 θ A cA := by
  intro D θ A cA hθ u hu
  have hu' : u ∈ autForms θ A (Kinf θ A cA) ⊓ cuspCont A := hu
  show (fun g => conj (u g)) ∈ autForms θ A (Kinf θ A cA) ⊓ cuspCont A
  obtain ⟨h1, h2⟩ := Submodule.mem_inf.1 hu'
  obtain ⟨hs, hk⟩ := mem_autForms.1 h1
  refine Submodule.mem_inf.2 ⟨mem_autForms.2 ⟨?_, isKFinite_conj hk⟩, conj_mem_cuspCont h2⟩
  exact GlobalTheory.Mem.AutConj.isAutFunSm_star D θ hθ A u hs

end GlobalTheory.Core.Rk.CuspConj

end
