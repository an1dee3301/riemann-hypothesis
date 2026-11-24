module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DecayZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Group.Action.Basic
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pointwise.Set.Basic
public import Mathlib.Algebra.Group.Action.Units
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Pointwise.Set.Scalar
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Actions
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Units
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Basic.Countable.Basic
public import Mathlib.Basic.Countable.Defs
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Rat.Defs
public import Mathlib.Data.Rat.Encodable
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Dynamics.Ergodic.Action.Basic
public import Mathlib.Dynamics.Ergodic.Action.Regular
public import Mathlib.FieldTheory.Perfect
public import Mathlib.FieldTheory.Separable
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.Logic.Encodable.Basic
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Group.Arithmetic
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.AbsolutelyContinuous
public import Mathlib.MeasureTheory.Measure.Haar.DistribChar
public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Module
public import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving
public import Mathlib.MeasureTheory.Measure.Regular
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Topology.Algebra.ConstMulAction
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Compactness.LocallyCompact
public import Mathlib.Topology.Compactness.Paracompact
public import Mathlib.Topology.Metrizable.Basic
public import Mathlib.Topology.Metrizable.Urysohn
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.Separation.Regular

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.SWQ
open scoped TensorProduct NNReal ENNReal Pointwise

noncomputable section

namespace GlobalTheory.SWQ

theorem countable_of_numberField (F : Type) [Field F] [NumberField F] : Countable F :=
  Countable.of_equiv _ (Module.finBasis ℚ F).equivFun.toEquiv.symm

theorem map_unit_mul_eq (F : Type) [Field F] [NumberField F] (ν : Measure (AF F)) [ν.IsAddHaarMeasure]
    (w : (AF F)ˣ) : ν.map (fun x => w • x) = (distribHaarChar (AF F) w⁻¹ : ℝ≥0∞) • ν := by
  ext S hS
  rw [Measure.map_apply (measurable_const_smul w) hS, Set.preimage_smul, Measure.smul_apply, smul_eq_mul,
    distribHaarChar_mul]

theorem modrat_main : ∀ (F : Type) [Field F] [NumberField F] (N : ℕ) (ν : Measure (AF F)), IsCov1 ν →
    ∀ t : F, t ≠ 0 → ν.map (fun x => (algebraMap F (AF F) t) * x) = ν := by
  intro F _ _ _ ν hν t ht
  obtain ⟨hH, D, _, hD, hD1⟩ := hν
  haveI := hH
  haveI := countable_of_numberField F
  set K := (algebraMap F (AF F)).range.toAddSubgroup with hK
  haveI : Countable K := by
    refine Function.Surjective.countable (f := fun r : F => (⟨algebraMap F (AF F) r, ⟨r, rfl⟩⟩ : K)) ?_
    rintro ⟨x, ⟨r, rfl⟩⟩
    exact ⟨r, rfl⟩
  have htu : IsUnit (algebraMap F (AF F) t) := (isUnit_iff_ne_zero.mpr ht).map _
  set u : (AF F)ˣ := htu.unit with hu
  have hmul : (fun x : AF F => (algebraMap F (AF F) t) * x) = fun x => u • x := by
    funext x; rfl
  rw [hmul]

  let e : K ≃ K :=
    { toFun := fun g => ⟨algebraMap F (AF F) t⁻¹ * g, by
        obtain ⟨r, hr⟩ := g.2; exact ⟨t⁻¹ * r, by rw [map_mul, hr]⟩⟩
      invFun := fun g => ⟨algebraMap F (AF F) t * g, by
        obtain ⟨r, hr⟩ := g.2; exact ⟨t * r, by rw [map_mul, hr]⟩⟩
      left_inv := fun g => by
        ext; simp only; rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ ht, map_one, one_mul]
      right_inv := fun g => by
        ext; simp only; rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ ht, map_one, one_mul] }
  have hqmp : Measure.QuasiMeasurePreserving (MulAction.toPerm u).symm ν ν := by
    refine ⟨(measurable_const_smul u⁻¹).aemeasurable, ?_⟩
    have : ⇑(MulAction.toPerm u).symm = fun x : AF F => u⁻¹ • x := rfl
    rw [this, map_unit_mul_eq F ν u⁻¹]
    exact Measure.AbsolutelyContinuous.smul_left (Measure.AbsolutelyContinuous.refl _) _
  have hD' : IsAddFundamentalDomain K (MulAction.toPerm u '' D) ν := by
    refine hD.image_of_equiv (MulAction.toPerm u) hqmp e ?_
    intro g x
    change u • ((e g : AF F) + x) = (g : AF F) + u • x
    change algebraMap F (AF F) t * (algebraMap F (AF F) t⁻¹ * (g : AF F) + x) = (g : AF F) + algebraMap F (AF F) t * x
    rw [mul_add, ← mul_assoc, ← map_mul, mul_inv_cancel₀ ht, map_one, one_mul]
  have himg : (MulAction.toPerm u '' D) = u • D := rfl
  have h1 : ν (u • D) = 1 := by rw [← himg, hD'.measure_eq hD, hD1]
  have hchar : distribHaarChar (AF F) u = 1 := by
    have := distribHaarChar_mul ν u D
    rw [h1, hD1, mul_one] at this
    exact_mod_cast this
  rw [map_unit_mul_eq F ν u, map_inv, hchar, inv_one, ENNReal.coe_one, one_smul]

end GlobalTheory.SWQ
