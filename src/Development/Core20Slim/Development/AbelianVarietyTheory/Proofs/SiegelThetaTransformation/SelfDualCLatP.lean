module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LevelStructureProperties
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsHomDivMulRefine
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MapFinNeg
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FinTensMemLatO
public import Development.Core20Slim.ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.ModelLatA
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.FactPrincipalDatum
public import Formalism.LocalRingCardinality.ConjSqrtMinusD
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.FirstCoordinateAdmissible
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Lattice.Basic
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Notation.Pi.Basic
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Basic.IsEmpty.Defs
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Finite.Range
public import Mathlib.Data.Set.Operations
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Real Classical ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Ker.Base

open ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA GlobalTheory.SW.Lev

variable {D : D7}












theorem star_mem_stdL {n : ℕ} {v : Fin n → D.host.E} (hv : v ∈ stdL D.host.E n) : star v ∈ stdL D.host.E n :=
  (GlobalTheory.SW.Base.mem_stdL _).2 fun a => int_cc D ((GlobalTheory.SW.Base.mem_stdL _).1 hv a)

theorem selfDualC_stdL {S : HSp D} (hS : S.gram = 1) : IsSelfDualC S (stdL D.host.E S.rank) := by
  have e : ∀ x y : Fin S.rank → D.host.E, ∑ i, ∑ j, star (x i) * S.gram i j * y j = ∑ i, star (x i) * y i :=
    fun x y => by simp [hS, Matrix.one_apply]
  refine ⟨Submodule.IsLattice.of_fg D.host.E (Submodule.fg_span (Set.finite_range _)), fun y => ⟨fun hy x hx => ?_, fun h => ?_⟩⟩
  · rw [e]
    exact ⟨⟨∑ i, star (x i) * y i, IsIntegral.sum _ fun i _ => ((GlobalTheory.SW.Base.mem_stdL _).1 (star_mem_stdL hx) i).mul ((GlobalTheory.SW.Base.mem_stdL _).1 hy i)⟩, rfl⟩
  · refine (GlobalTheory.SW.Base.mem_stdL _).2 fun a => ?_
    obtain ⟨b, hb⟩ := h (Pi.single a 1) (Submodule.subset_span ⟨a, rfl⟩)
    rw [e, Finset.sum_eq_single a (fun i _ hi => by simp [hi]) (by simp)] at hb
    have : y a = b := by simp [hb]
    rw [this]
    exact b.2





end GlobalTheory.Ker.Base

end
