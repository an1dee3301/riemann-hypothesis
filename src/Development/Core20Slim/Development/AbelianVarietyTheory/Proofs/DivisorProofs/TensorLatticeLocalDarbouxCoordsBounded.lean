module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareTriple
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftPRouteSmall
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesEqPrimFrameLat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallySelfDualLatticeIndicatorIsVacuum
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorLatticeAtFinitePlaceEqIntegralSpanGenerato
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinPartIdemMulMemIff
public import Formalism.LocalRingCardinality.SpanPowerMembership.LocAtA
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Classical
public import Init.Core
public import Init.Data.Bool
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Ext
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.NonUnitalHom
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.BigOperators
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Subsemigroup.Defs
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Group.WithOne.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.Lattice.Basic
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Prod
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Notation.Prod
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Erase
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Valuation
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.Topology.Algebra.UniformRing
public import Mathlib.Topology.Algebra.Valued.ValuationTopology
public import Mathlib.Topology.Algebra.Valued.WithVal

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.LatBound

theorem exists_mul_mem_integers {F : Type} [Field F] [NumberField F] (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F))
    {T : Type} [Fintype T] (w : T → Fv F v) :
    ∃ c : Fv F v, c ≠ 0 ∧ ∀ t, c * w t ∈ v.adicCompletionIntegers F := by
  classical
  have key : ∀ x : Fv F v, ∃ c : Fv F v, c ≠ 0 ∧ c ∈ v.adicCompletionIntegers F ∧
      c * x ∈ v.adicCompletionIntegers F := by
    intro x
    by_cases hx : x ∈ v.adicCompletionIntegers F
    · exact ⟨1, one_ne_zero, one_mem _, by simpa using hx⟩
    · have hx0 : x ≠ 0 := by rintro rfl; exact hx (zero_mem _)
      refine ⟨x⁻¹, inv_ne_zero hx0, ?_, by rw [inv_mul_cancel₀ hx0]; exact one_mem _⟩
      exact ((v.adicCompletionIntegers F).mem_or_inv_mem x).resolve_left hx
  choose cw hcw0 hcwO hcw using key
  refine ⟨∏ t, cw (w t), Finset.prod_ne_zero_iff.2 fun t _ => hcw0 _, fun t => ?_⟩
  rw [← Finset.mul_prod_erase Finset.univ (fun t => cw (w t)) (Finset.mem_univ t), mul_comm (cw (w t)), mul_assoc]
  exact mul_mem (prod_mem fun t' _ => hcwO _) (hcw _)

theorem locCo_latAtV_bounded : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n d : ℕ}
    (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n) (Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F))
    {B : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) → Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) → AF F}
    {κ : Type} [Fintype κ] (co : GlobalTheory.WeilM.Darboux B κ), X.L.IsLattice E → Y.L.IsLattice E →
    ∃ c : Fv F v, c ≠ 0 ∧ ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV X Y v, ∀ i,
      c * (GlobalTheory.LatVac.locCo co v γ).1 i ∈ v.adicCompletionIntegers F ∧
      c * (GlobalTheory.LatVac.locCo co v γ).2 i ∈ v.adicCompletionIntegers F := by
  intro F E _ _ _ _ _ n d X Y v B κ _ co hX hY
  obtain ⟨M, _, g, hg⟩ := GlobalTheory.LatParam.latAtV_param X Y hX hY v
  obtain ⟨c, hc0, hc⟩ := exists_mul_mem_integers v
    (fun t : Bool × M × κ => if t.1 then (GlobalTheory.LatVac.locCo co v (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F (g t.2.1))).1 t.2.2
      else (GlobalTheory.LatVac.locCo co v (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F (g t.2.1))).2 t.2.2)
  have hsmul : ∀ (t : Fv F v) z, GlobalTheory.LatVac.locCo co v (GlobalTheory.EmbChart.atPlace v t • z) =
      t • GlobalTheory.LatVac.locCo co v z := by
    intro t z
    simp only [GlobalTheory.LatVac.locCo, AddMonoidHom.coe_mk, ZeroHom.coe_mk, map_smul]
    ext k <;> simp [smul_eq_mul, map_mul, GlobalTheory.EmbChart.evFin_atPlace]
  refine ⟨c, hc0, fun γ hγ i => ?_⟩
  obtain ⟨a, rfl⟩ := (hg γ).1 hγ
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, hsmul, Prod.fst_sum, Prod.snd_sum, Finset.sum_apply, Prod.smul_fst, Prod.smul_snd,
    Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  constructor
  · refine sum_mem fun m _ => ?_
    rw [mul_left_comm]
    exact mul_mem (a m).2 (by simpa using hc (true, m, i))
  · refine sum_mem fun m _ => ?_
    rw [mul_left_comm]
    exact mul_mem (a m).2 (by simpa using hc (false, m, i))

end GlobalTheory.LatBound
