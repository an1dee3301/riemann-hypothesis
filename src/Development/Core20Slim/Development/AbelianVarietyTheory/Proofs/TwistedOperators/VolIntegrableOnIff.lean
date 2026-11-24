module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.BplusOfEquivariant
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.Divisors.ExistsBplusNeZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Prelude
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Actions
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Countable.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Dynamics.Ergodic.Action.Basic
public import Mathlib.Dynamics.Ergodic.Action.Regular
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Group.Arithmetic
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Compactness.LocallyCompact
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Order
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj

namespace GlobalTheory.VolIdent

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem vol_nu_eq {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {t : T} (M M' : Vol G)
    (hM : M.Is t) (hM' : M'.Is t) : ∀ X : Node, X.InRange D.R.m → M.ν X = M'.ν X :=
  fun X hX => GlobalTheory.FunObjModel.isAt_unique (hM.vtx X hX) (hM'.vtx X hX)

theorem vol_setIntegral_eq {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {t : T} (M M' : Vol G)
    (hM : M.Is t) (hM' : M'.Is t) {X : Node} (hX : X.InRange D.R.m) (f : GA D (G.V X) → ℂ)
    (hf : ∀ γ ∈ GQ (G.V X), ∀ u, f (γ * u) = f u) :
    ∫ u in M.fd X, f u ∂M.ν X = ∫ u in M'.fd X, f u ∂M'.ν X := by
  obtain ⟨a1, a2, a3, a4, a5, -, a7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D (G.V X)
  have e := vol_nu_eq M M' hM hM' X hX
  have h1 := (hM.vtx X hX).haar_fund
  have h2 := (hM'.vtx X hX).haar_fund
  rw [← e] at h2 ⊢
  have := h1.1
  exact h1.2.setIntegral_eq h2.2 fun γ g => hf γ γ.2 g

theorem vol_integrableOn_iff {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {t : T} (M M' : Vol G)
    (hM : M.Is t) (hM' : M'.Is t) {X : Node} (hX : X.InRange D.R.m) (f : GA D (G.V X) → ℂ)
    (hf : ∀ γ ∈ GQ (G.V X), ∀ u, f (γ * u) = f u) :
    IntegrableOn f (M.fd X) (M.ν X) ↔ IntegrableOn f (M'.fd X) (M'.ν X) := by
  obtain ⟨a1, a2, a3, a4, a5, -, a7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D (G.V X)
  have e := vol_nu_eq M M' hM hM' X hX
  have h1 := (hM.vtx X hX).haar_fund
  have h2 := (hM'.vtx X hX).haar_fund
  rw [← e] at h2 ⊢
  have := h1.1
  exact h1.2.integrableOn_iff h2.2 fun γ g => hf γ γ.2 g

end GlobalTheory.VolIdent

end
