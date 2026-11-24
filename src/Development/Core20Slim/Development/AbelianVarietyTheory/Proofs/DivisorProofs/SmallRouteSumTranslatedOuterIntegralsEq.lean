module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareTriple
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftPRouteSmall
public import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
public import Development.AbelianVarietyTheory.Definitions.Divisors.BplusOfEquivariant
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsNotRelZero
public import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocallyCompactSecondCountableT2
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemElt
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Actions
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Compactness.LocallyCompact
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.SmallRoute

theorem sum_integral_translates_outer_eq : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀)
    (W : G.Weil) (t : T) (i j : Fin D.R.m) (M : Vol G) (hM : M.Is t) (Θ' : TotT G (routeSmall t i j))
    (F : Fn G (.grid i (j + 1))) (hB : TotConv W M _ Θ' F) (g₁ : GA D (G.V (.grid (i + 1) j))) (z : GA D (G.V (.grid i j)) →₀ ℂ)
    (hI : ∀ d ∈ Θ'.support, ∀ k, IntegrableOn (fun u => GlobalTheory.SmallRoute.outer W M d F g₁ (u * k)) (M.fd (.grid i j)) (M.ν (.grid i j)))
    (hJ : Integrable (fun p : GA D (G.V (.grid i (j + 1))) × GA D (G.V (.grid i j)) => F p.1 * translates z (kerSmall W Θ' p.1 g₁) p.2)
      (((M.ν (.grid i (j + 1))).restrict (M.fd (.grid i (j + 1)))).prod ((M.ν (.grid i j)).restrict (M.fd (.grid i j))))),
    (Θ'.sum fun d c => c * ∫ u in M.fd (.grid i j), translates z (GlobalTheory.SmallRoute.outer W M d F g₁) u ∂M.ν (.grid i j)) =
      ∫ g in M.fd (.grid i (j + 1)), F g * ∫ u in M.fd (.grid i j),
        translates z (kerSmall W Θ' g g₁) u ∂M.ν (.grid i j) ∂M.ν (.grid i (j + 1)) := by
  intro D T L sc G μ₀ hL W t i j M hM Θ' F hB g₁ z hI hJ
  classical
  have hσ : ∀ X : Node, X.InRange D.R.m → SigmaFinite (M.ν X) := fun X hX => by
    obtain ⟨h1, h2, -⟩ := GlobalTheory.MemberAdelicTop.locallyCompact_secondCountable_t2 D (G.V X)
    haveI := (hM.vtx X hX).haar_fund.1
    infer_instance
  haveI := hσ (.grid i (j + 1)) ⟨i.2.le, j.2⟩
  haveI := hσ (.grid i j) ⟨i.2.le, j.2.le⟩
  have hpt : ∀ u, ∫ g in M.fd (.grid i (j + 1)), F g * translates z (kerSmall W Θ' g g₁) u ∂M.ν (.grid i (j + 1)) =
      Θ'.sum fun d c => c * translates z (outer W M d F g₁) u := by
    intro u
    have hint : ∀ d ∈ Θ'.support, ∀ k, IntegrableOn (fun g => W.kerA (.down t i j) d.1.2 g (u * k) * F g)
        (M.fd (.grid i (j + 1))) (M.ν (.grid i (j + 1))) := fun d hd k => (hB d hd).1.2 (u * k)
    have e : ∀ g, F g * translates z (kerSmall W Θ' g g₁) u = ∑ k ∈ z.support, ∑ d ∈ Θ'.support,
        z k * (Θ' d * (W.kerA (.right i j) d.2 (u * k) g₁ * (W.kerA (.down t i j) d.1.2 g (u * k) * F g))) := by
      intro g
      simp only [translates, kerSmall, Finsupp.sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun d _ => by ring
    simp_rw [e]
    rw [integral_finsetSum _ fun k _ => integrable_finsetSum _ fun d hd =>
      (((hint d hd k).const_mul _).const_mul _).const_mul _]
    simp_rw [integral_finsetSum _ fun d hd => (((hint d hd _).const_mul _).const_mul _).const_mul _]
    simp only [integral_const_mul, translates, outer, Finsupp.sum, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun k _ => by ring
  have hint2 : ∀ d ∈ Θ'.support, Integrable (translates z (outer W M d F g₁))
      ((M.ν (.grid i j)).restrict (M.fd (.grid i j))) := fun d hd =>
    integrable_finsetSum _ fun k _ => (hI d hd k).const_mul _
  symm
  calc ∫ g in M.fd (.grid i (j + 1)), F g * ∫ u in M.fd (.grid i j), translates z (kerSmall W Θ' g g₁) u ∂M.ν (.grid i j)
        ∂M.ν (.grid i (j + 1))
      = ∫ g in M.fd (.grid i (j + 1)), ∫ u in M.fd (.grid i j), F g * translates z (kerSmall W Θ' g g₁) u ∂M.ν (.grid i j)
        ∂M.ν (.grid i (j + 1)) := by simp_rw [integral_const_mul]
    _ = ∫ u in M.fd (.grid i j), ∫ g in M.fd (.grid i (j + 1)), F g * translates z (kerSmall W Θ' g g₁) u
        ∂M.ν (.grid i (j + 1)) ∂M.ν (.grid i j) := integral_integral_swap hJ
    _ = ∫ u in M.fd (.grid i j), (Θ'.sum fun d c => c * translates z (outer W M d F g₁) u) ∂M.ν (.grid i j) := by
        simp_rw [hpt]
    _ = _ := by
        simp only [Finsupp.sum]
        rw [integral_finsetSum _ fun d hd => (hint2 d hd).const_mul _]
        simp_rw [integral_const_mul]

end GlobalTheory.SmallRoute

end
