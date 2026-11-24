module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.RangeSndRel
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
public import Development.AbelianVarietyTheory.Definitions.Divisors.BplusOfEquivariant
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsNotRelZero
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Classical
public import Init.Core
public import Init.Data.List.Basic
public import Init.Data.List.Lemmas
public import Init.Prelude
public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Insert
public import Mathlib.Data.Finset.Union
public import Mathlib.Data.Finsupp.Basic
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Finsupp.Single
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.FlipRun

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil}

theorem pathConv_zip_fock (M : Vol G) (ρ : RealMatch W) (t : T) {e : AE D}
    (he : IsIdemSum e (locPl G t)) (hC : CuspStep W M ρ t) {X : Node} :
    ∀ {Y : Node} (p : Path T X Y), OnGrid D.R.m t p → ∀ (φ d : PureT G p), VecAll ρ e p φ d →
      ∀ (P' : PolT G p) (F : Fn G X), IsCuspListed W.θ X F →
      PathConv W M p (Path.Fam.zip (fun a (f : Sch G a) Q => W.fock a.pair f Q) d P') F ∧
      IsCuspListed W.θ Y (liftP W M p (Path.Fam.zip (fun a (f : Sch G a) Q => W.fock a.pair f Q) d P') F) := by
  intro Y p
  induction p with
  | nil =>
    intro _ _ _ _ _ _ hF
    exact ⟨trivial, hF⟩
  | snoc a p ih =>
    intro hg φ d hv P' F hF
    have hg' : OnGrid D.R.m t p := fun b hb => hg b (List.mem_append_left [a] hb)
    have ha : IsGridArrow D.R.m t a := hg a (List.mem_append_right p.arrows (List.mem_singleton_self a))
    obtain ⟨h1, h2⟩ := ih hg' φ.1 d.1 hv.1 P'.1 F hF
    obtain ⟨h3, h4⟩ := hC a ha e he φ.2 d.2 hv.2 P'.2 _ h2
    exact ⟨⟨h1, h3⟩, h4⟩

theorem mem_support_tensT {X Y : Node} {p : Path T X Y} (τi : PolT G p →₀ ℂ) (τf : TotT G p) (x : PureT G p)
    (hx : x ∈ (tensT W τi τf).support) :
    ∃ d ∈ τf.support, ∃ P' : PolT G p, x = Path.Fam.zip (fun a (f : Sch G a) Q => W.fock a.pair f Q) d P' := by
  classical
  unfold tensT at hx
  obtain ⟨P, -, hP⟩ := Finset.mem_biUnion.1 (Finsupp.support_sum hx)
  obtain ⟨d, hd, hx'⟩ := Finset.mem_biUnion.1 (Finsupp.support_sum hP)
  exact ⟨d, hd, P, Finset.mem_singleton.1 (Finsupp.support_single_subset hx')⟩

theorem totConv_tensE : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} (M : Vol G) (ρ : RealMatch W) (t : T) {e : AE D}, IsIdemSum e (locPl G t) → GlobalTheory.FlipRun.CuspStep W M ρ t → ∀ {X Y : Node} (p : Path T X Y), GlobalTheory.FlipRun.OnGrid D.R.m t p → ∀ (τ : TotT G p) (φ : PureT G p → PureT G p), (∀ d ∈ τ.support, GlobalTheory.FlipRun.VecAll ρ e p (φ d) d) → ∀ F : Fn G X, GlobalTheory.FlipRun.IsCuspListed W.θ X F → ∀ Q : GlobalTheory.FlipRun.PolE G →₀ ℂ, TotConv W M p (GlobalTheory.FlipRun.tensE W p Q τ) F := by
  intro D T L sc G W M ρ t e he hC X Y p hg τ φ hv F hF Q x hx
  obtain ⟨d, hd, P', rfl⟩ := mem_support_tensT _ τ x hx
  exact (pathConv_zip_fock M ρ t he hC p hg (φ d) d (hv d hd) P' F hF).1

end GlobalTheory.FlipRun
