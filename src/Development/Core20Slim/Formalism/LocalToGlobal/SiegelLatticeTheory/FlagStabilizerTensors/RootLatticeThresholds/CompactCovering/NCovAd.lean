module

public import Mathlib
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.DictRing
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.IntAdCpctOpen
public import Formalism.SatakeDualWeyl.Statement
public import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
public import Init.Classical
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Units.Basic
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Prod
public import Mathlib.Algebra.Module.Submodule.Basic
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.ZLattice.Basic
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Notation.Prod
public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Equiv
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Pi
public import Mathlib.Algebra.Ring.Prod
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.WithAbs
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Order.Lattice
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.ExistsUnique
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Sets
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
public import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.EMetricSpace.Defs
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.MetricSpace.Isometry
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Metric

namespace Formalism.L2.SG.Pf.RescaleCore.NCov

namespace AdCocptW

variable {F : Type} [Field F] [NumberField F]

theorem NCovAd_ball_compact (v : InfinitePlace F) (R : ℝ) :
    IsCompact (closedBall (0 : v.Completion) R) := by
  first
  | exact isCompact_closedBall (0 : v.Completion) R
  | exact (haveI : ProperSpace v.Completion := ProperSpace.of_locallyCompactSpace v.Completion
      isCompact_closedBall (0 : v.Completion) R)
  | exact (by
      have hi := NumberField.InfinitePlace.Completion.isometry_extensionEmbedding v
      have hc := (hi.isClosedEmbedding).isCompact_preimage (isCompact_closedBall (0 : ℂ) R)
      have e : (NumberField.InfinitePlace.Completion.extensionEmbedding v) ⁻¹' closedBall 0 R =
          closedBall (0 : v.Completion) R := by
        ext z
        simp only [Set.mem_preimage, mem_closedBall, dist_zero_right]
        rw [hi.norm_map_of_map_zero (map_zero _)]
      rw [e] at hc
      exact hc)

theorem NCovAd_inf_approx : ∃ R : ℝ, ∀ x : Ainf F, ∃ β : 𝓞 F,
    ∀ v : InfinitePlace F, ‖(x - algebraMap F (Ainf F) (β : F)) v‖ ≤ R := by
  classical
  set b := NumberField.mixedEmbedding.latticeBasis F with hb
  have hB : ∃ R : ℝ, ∀ y ∈ ZSpan.fundamentalDomain b, ‖y‖ ≤ R := by
    first
    | exact (ZSpan.fundamentalDomain_isBounded b).exists_norm_le
    | exact isBounded_iff_forall_norm_le.mp (ZSpan.fundamentalDomain_isBounded b)
  obtain ⟨R, hR⟩ := hB
  refine ⟨R, fun x => ?_⟩
  obtain ⟨⟨w, hw⟩, hwD, -⟩ := ZSpan.exist_unique_vadd_mem_fundamentalDomain b (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace F x)
  have hc' : ∃ c : Module.Free.ChooseBasisIndex ℤ (𝓞 F) → ℤ, ∑ i, c i • b i = w := by
    first
    | exact (Submodule.mem_span_range_iff_exists_fun ℤ).mp hw
    | exact Submodule.mem_span_range_iff_exists_fun.mp hw
  obtain ⟨c, hc⟩ := hc'
  let γ : 𝓞 F := ∑ i, c i • NumberField.RingOfIntegers.basis F i
  have hγ : NumberField.mixedEmbedding F (algebraMap (𝓞 F) F γ) = w := by
    rw [← hc]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [γ, map_sum, map_zsmul, hb, NumberField.mixedEmbedding.latticeBasis_apply,
      NumberField.integralBasis_apply]
  refine ⟨-γ, fun v => ?_⟩
  have hneg : ((-γ : 𝓞 F) : F) = -(algebraMap (𝓞 F) F γ) := by
    first
    | rfl
    | simp
    | (push_cast; rfl)
  set z := x - algebraMap F (Ainf F) ((-γ : 𝓞 F) : F) with hzdef
  have hz : NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace F z ∈ ZSpan.fundamentalDomain b := by
    have e : NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace F z = w + NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace F x := by
      rw [hzdef, hneg, map_neg, sub_neg_eq_add, map_add (f := _), ← hγ,
        NumberField.InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp, add_comm]
    rw [e]
    first
    | exact hwD
    | (rw [Submodule.vadd_def, vadd_eq_add] at hwD; exact hwD)
    | (simpa [Submodule.vadd_def] using hwD)
  have hn := hR _ hz
  by_cases hv : v.IsReal
  · calc ‖z v‖ = ‖(NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace F z).1 ⟨v, hv⟩‖ := by
          rw [NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
          exact ((NumberField.InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hv).norm_map_of_map_zero
            (map_zero _) _).symm
      _ ≤ ‖(NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace F z).1‖ := norm_le_pi_norm _ _
      _ ≤ ‖NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace F z‖ := norm_fst_le _
      _ ≤ R := hn
  · have hv' : v.IsComplex := NumberField.InfinitePlace.not_isReal_iff_isComplex.mp hv
    calc ‖z v‖ = ‖(NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace F z).2 ⟨v, hv'⟩‖ := by
          rw [NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
          exact ((NumberField.InfinitePlace.Completion.isometry_extensionEmbedding v).norm_map_of_map_zero
            (map_zero _) _).symm
      _ ≤ ‖(NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace F z).2‖ := norm_le_pi_norm _ _
      _ ≤ ‖NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace F z‖ := norm_snd_le _
      _ ≤ R := hn

theorem NCovAd_int_mem (β : 𝓞 F) : algebraMap F (Af F) (β : F) ∈ Formalism.UG.intAd F := by
  show ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F),
    (algebraMap F (Af F) (β : F)) v ∈ v.adicCompletionIntegers F
  intro v
  first
  | exact v.coe_mem_adicCompletionIntegers β
  | exact (v.mem_adicCompletionIntegers F).mpr (by
      rw [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
      simpa using v.valuation_le_one β)
  | exact (v.mem_adicCompletionIntegers F).mpr (by
      show Valued.v ((β : F) : v.adicCompletion F) ≤ 1
      rw [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
      simpa using v.valuation_le_one β)

theorem NCovAd_fin_approx (a : Af F) : ∃ x : F, a - algebraMap F (Af F) x ∈ Formalism.UG.intAd F := by
  obtain ⟨m, hm, hma⟩ := PIW.AdelClassFin.DictRing.af_denom a
  obtain ⟨β, y, hy, hβ⟩ := PIW.AdelClassFin.DictRing.af_approx _ hma m hm
  refine ⟨(β : F) / m, ?_⟩
  have hmF : (m : F) ≠ 0 := by exact_mod_cast hm.ne'
  have hcast : ((m : ℕ) : Af F) = algebraMap F (Af F) (m : F) := (map_natCast _ m).symm
  have hu : IsUnit ((m : ℕ) : Af F) := by
    rw [hcast]
    exact (isUnit_iff_ne_zero.2 hmF).map _
  have e1 : ((m : ℕ) : Af F) * (a - algebraMap F (Af F) ((β : F) / m)) = (m : Af F) * y := by
    rw [mul_sub, hβ, hcast, ← map_mul, mul_div_cancel₀ _ hmF,
      IsScalarTower.algebraMap_apply (𝓞 F) F (Af F)]
    ring
  rw [hu.mul_left_cancel e1]
  exact hy

end AdCocptW

end Formalism.L2.SG.Pf.RescaleCore.NCov
