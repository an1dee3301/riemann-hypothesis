module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.NodeAgree
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
public import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqExistsIffDsExists
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneSubIdempotentSmulMemLattice
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OneSubMemIdS
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ToEAfMulIncAMemOfIsIdemSum
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameTwistFamilySpecializationGood
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.LocalToGlobal.Columns.Adelic
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Formalism.LocalToGlobal.HeckeThetaElements.IsHeckeElt
public import Formalism.LocalToGlobal.HermitianColumns.InLocalDiscriminantKernel
public import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Classical
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.BigOperators
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Subsemigroup.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Order.Kleene
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.Logic.Function.Basic
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Tactic.LinearCombination.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.IdemSumIdeal

section Generic

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem one_sub_mem_idS_prod [StarRing E] (P : Finset (Pl E)) (d : Pl E → ℕ) {ε : E ⊗[F] Formalism.L2.Herm.Af F}
    (hε : ε ∈ Formalism.L2.Herm.intAf F E)
    (h : ∀ w ∈ P, ∃ a : E ⊗[F] Formalism.L2.Herm.Af F, GlobalTheory.InertNbr.IdemOf F w a ∧ a * ε = a) :
    ∃ t ∈ Formalism.L2.DIV.idS F (∏ w ∈ P, w.asIdeal ^ d w), (t : E ⊗[F] Formalism.L2.Herm.Af F) = 1 - ε := by
  classical
  choose! a ha hae using h
  have hone : (1 : E ⊗[F] Formalism.L2.Herm.Af F) - ε ∈ Formalism.L2.Herm.intAf F E := sub_mem (one_mem _) hε
  set t : Formalism.L2.Herm.intAf F E := ⟨1 - ε, hone⟩ with ht
  set b : Pl E → Formalism.L2.Herm.intAf F E := fun w =>
    if hw : w ∈ P then ⟨1 - a w, (ha w hw).one_sub_mem⟩ else 1 with hb
  have hbm : ∀ w ∈ P, b w ∈ Formalism.L2.DIV.idS F (w.asIdeal ^ d w) := by
    intro w hw
    have := (ha w hw).one_sub_mem_idS (d w)
    simpa [hb, hw] using this
  have hprod : ∏ w ∈ P, b w ∈ ∏ w ∈ P, Formalism.L2.DIV.idS F (w.asIdeal ^ d w) := Ideal.prod_mem_prod hbm
  have hmap : ∏ w ∈ P, Formalism.L2.DIV.idS F (w.asIdeal ^ d w) = Formalism.L2.DIV.idS F (∏ w ∈ P, w.asIdeal ^ d w) := by
    unfold Formalism.L2.DIV.idS
    exact (map_prod (Ideal.mapHom (Formalism.L2.DIV.oToS F E)) _ P).symm
  have hfix : t * ∏ w ∈ P, b w = t := by
    refine Finset.prod_induction b (fun x => t * x = t) (fun x y hx hy => by rw [← mul_assoc, hx, hy]) (mul_one t) ?_
    intro w hw
    apply Subtype.ext
    simp only [hb, hw, dif_pos, ht, Subring.coe_mul]
    linear_combination (hae w hw)
  refine ⟨t, ?_, rfl⟩
  rw [← hfix, ← hmap]
  exact Ideal.mul_mem_left _ _ hprod

end Generic

end GlobalTheory.IdemSumIdeal

namespace GlobalTheory.IdemSumIdeal

theorem idemOf_toEAf {D : D7} {a : AE D} {w : Formalism.L2.DIV.Pl D.host.E} (h : Formalism.L2.NTheta.IsIdemAt a w) :
    GlobalTheory.InertNbr.IdemOf D.host.F w (toEAf D a) := by
  refine ⟨by rw [← map_mul, h.1.1], fun x hx => ?_⟩
  rw [h.2 x hx]
  have e : toEAf D (a * incA D ((x : D.host.E)⁻¹)) = toEAf D a * Formalism.L2.Col.iA D.host.F D.host.E ((x : D.host.E)⁻¹) := by
    rw [map_mul]; rfl
  rw [← e]
  exact not_congr ⟨GlobalTheory.IdemIntegral.toEAf_mem_of_finPart_mem, GlobalTheory.PlaceDatum.finPart_mem_of_toEAf⟩

theorem isIdemSum_props : ∀ {D : D7} (e : AE D) (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (d : Formalism.L2.DIV.Pl D.host.E → ℕ),
    IsIdemSum e P → infPart D e = 0 ∧ toEAf D e ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ∧
      ∃ t ∈ Formalism.L2.DIV.idS D.host.F (∏ w ∈ P, w.asIdeal ^ d w), (t : EAf D) = 1 - toEAf D e := by
  intro D e P d h
  obtain ⟨⟨es, hes, he⟩, -⟩ := id h
  have hint : toEAf D e ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [he, map_sum]
    exact sum_mem fun w hw => (idemOf_toEAf (hes w hw)).mem
  refine ⟨?_, hint, ?_⟩
  · set_option synthInstance.maxHeartbeats 100000 in
      rw [he, map_sum]
    exact Finset.sum_eq_zero fun w hw =>
      GlobalTheory.ExportSeries.SpecGood.infPart_eq_zero_of_isIdemAt D w (es w) (hes w hw)
  · refine one_sub_mem_idS_prod P d hint fun w hw => ?_
    obtain ⟨a, ha, hae⟩ := GlobalTheory.OffIdem.idemSum_mul_idemAt h hw
    exact ⟨toEAf D a, idemOf_toEAf ha, by rw [← map_mul, hae]⟩

end GlobalTheory.IdemSumIdeal
