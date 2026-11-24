module

public import Mathlib
public import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
public import Development.Core20Slim.Lemmata.MiscLemmasM.Imports
public import Init.Core
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Ext
public import Init.Prelude
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Hom.Instances
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Pi.Units
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Analysis.Normed.Order.Lattice
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Set.CoeSort
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Set.Operations
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.Order.Filter.Cofinite
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.Filter.Pi
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Group.Units
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Algebra.RestrictedProduct.Basic
public import Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.Topology.Maps.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Neighborhoods
public import Mathlib.Topology.Order.OrderClosed
public import Mathlib.Topology.UniformSpace.Defs
public import ReciprocityTheory.NeutralLocalFields.Reciprocity

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host RestrictedProduct Topology

namespace PI.HeckeProdW

theorem no_small (z : ℂ) (h : ∀ n : ℕ, ‖z ^ n - 1‖ < 1 / 2) : z = 1 := by
  first | exact Bl.SecondBlockLemmaN.goal1 .. | (apply Bl.SecondBlockLemmaN.goal1 <;> assumption) | (intros; apply Bl.SecondBlockLemmaN.goal1 <;> assumption) | (apply @Bl.SecondBlockLemmaN.goal1 <;> assumption) | (intros; apply @Bl.SecondBlockLemmaN.goal1 <;> assumption) | (apply @Bl.SecondBlockLemmaN.goal1 <;> first | assumption | infer_instance) | exact @Bl.SecondBlockLemmaN.goal1 z h | exact @Bl.SecondBlockLemmaN.goal1 z

variable (L : Type) [Field L] [NumberField L]

abbrev Pu : Type := (v : HeightOneSpectrum (𝓞 L)) → (v.adicCompletionIntegers L)ˣ

def gI : ((v : HeightOneSpectrum (𝓞 L)) → v.adicCompletionIntegers L) →* AdeleRing (𝓞 L) L where
  toFun x := ((1 : InfiniteAdeleRing L),
    (structureMap (fun v : HeightOneSpectrum (𝓞 L) => v.adicCompletion L)
      (fun v => v.adicCompletionIntegers L) Filter.cofinite x : FiniteAdeleRing (𝓞 L) L))
  map_one' := rfl
  map_mul' _ _ := Prod.ext (mul_one 1).symm rfl

theorem gI_cont : Continuous (gI L) := by
  show Continuous (fun x => ((1 : InfiniteAdeleRing L),
    (structureMap (fun v : HeightOneSpectrum (𝓞 L) => v.adicCompletion L)
      (fun v => v.adicCompletionIntegers L) Filter.cofinite x : FiniteAdeleRing (𝓞 L) L)))
  exact continuous_const.prodMk isEmbedding_structureMap.continuous

def Phi : Pu L →* Ideles L :=
  (Units.map (gI L)).comp (MulEquiv.piUnits (M := fun v : HeightOneSpectrum (𝓞 L) =>
    v.adicCompletionIntegers L)).symm.toMonoidHom

theorem Phi_cont : Continuous (Phi L) :=
  (Continuous.units_map _ (gI_cont L)).comp
    (ContinuousMulEquiv.piUnits (M := fun v : HeightOneSpectrum (𝓞 L) =>
      v.adicCompletionIntegers L)).symm.continuous

variable {L}

theorem exists_strictHenselian_absolutely_closed_local_ring (χ : HChar L) : ∃ T : Finset (HeightOneSpectrum (𝓞 L)),
    ∀ y : Pu L, (∀ v ∈ T, y v = 1) → χ.1 (Phi L y) = 1 := by
  set W : Set ℂˣ := {z | ‖(z : ℂ) - 1‖ < 1 / 2} with hWdef
  have hW : IsOpen W :=
    isOpen_lt (continuous_norm.comp (Units.continuous_val.sub continuous_const)) continuous_const
  have hc : Continuous (fun y => χ.1 (Phi L y)) := χ.2.1.comp (Phi_cont L)
  have h1 : (fun y => χ.1 (Phi L y)) 1 ∈ W := by
    simp only [map_one, hWdef, Set.mem_setOf_eq, Units.val_one, sub_self, norm_zero]
    norm_num
  have hmem : (fun y => χ.1 (Phi L y)) ⁻¹' W ∈ 𝓝 (1 : Pu L) :=
    hc.continuousAt.preimage_mem_nhds (hW.mem_nhds h1)
  rw [nhds_pi, Filter.mem_pi] at hmem
  obtain ⟨I, hI, t, ht, hsub⟩ := hmem
  refine ⟨hI.toFinset, fun y hy => ?_⟩
  have hyI : ∀ n : ℕ, y ^ n ∈ I.pi t := by
    intro n i hi
    rw [Pi.pow_apply, hy i (hI.mem_toFinset.2 hi), one_pow]
    exact mem_of_mem_nhds (ht i)
  refine Units.ext (no_small _ fun n => ?_)
  have h2 := hsub (hyI n)
  simp only [Set.mem_preimage, map_pow, hWdef, Set.mem_setOf_eq, Units.val_pow_eq_pow_val] at h2
  exact h2

end PI.HeckeProdW
