module

public import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Core
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Order.IsBotOne
public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.ENNReal.Action
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Basic.NNReal.Star
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.Haar.MulEquivHaarChar
public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Module
public import Mathlib.MeasureTheory.Measure.Regular
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Compactness.LocallyCompact
public import Mathlib.Topology.Compactness.Paracompact
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Metrizable.Basic
public import Mathlib.Topology.Metrizable.Urysohn
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.Separation.Regular

@[expose] public section

open MeasureTheory Topology Matrix
open scoped ENNReal NNReal

namespace GlobalTheory.CompanionTheory.SW.NormOneHaar

variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]

def mulEquiv (u v : K) (h : u * v = 1) : K ≃ₜ+ K where
  toFun y := u * y
  invFun y := v * y
  left_inv y := by
    show v * (u * y) = y
    rw [← mul_assoc, mul_comm v u, h, one_mul]
  right_inv y := by
    show u * (v * y) = y
    rw [← mul_assoc, h, one_mul]
  map_add' x y := mul_add u x y
  continuous_toFun := continuous_const.mul continuous_id
  continuous_invFun := continuous_const.mul continuous_id

def invEquiv (σ : K →+* K) (hc : Continuous σ) (hi : ∀ y, σ (σ y) = y) : K ≃ₜ+ K where
  toFun := σ
  invFun := σ
  left_inv := hi
  right_inv := hi
  map_add' := map_add σ
  continuous_toFun := hc
  continuous_invFun := hc

variable [LocallyCompactSpace K] [MeasurableSpace K] [BorelSpace K]

theorem char_conj (σ : K →+* K) (hc : Continuous σ) (hi : ∀ y, σ (σ y) = y) (u v : K)
    (h : u * v = 1) (h' : σ u * σ v = 1) :
    addEquivAddHaarChar (mulEquiv (σ u) (σ v) h') = addEquivAddHaarChar (mulEquiv u v h) := by
  set s := invEquiv σ hc hi
  have e : mulEquiv (σ u) (σ v) h' = (s.trans (mulEquiv u v h)).trans s.symm := by
    ext y
    show σ u * y = σ (u * σ y)
    rw [map_mul, hi]
  rw [e, addEquivAddHaarChar_trans, addEquivAddHaarChar_trans, addEquivAddHaarChar_symm,
    mul_comm (addEquivAddHaarChar s), mul_assoc,
    mul_inv_cancel₀ (addEquivAddHaarChar_pos s).ne', mul_one]

theorem char_mul_eq_one (u v : K) (h : u * v = 1) (h' : v * u = 1) :
    addEquivAddHaarChar (mulEquiv u v h) * addEquivAddHaarChar (mulEquiv v u h') = 1 := by
  have e : (mulEquiv u v h).trans (mulEquiv v u h') = ContinuousAddEquiv.refl K := by
    ext y
    show v * (u * y) = y
    rw [← mul_assoc, h', one_mul]
  rw [← addEquivAddHaarChar_trans, e, addEquivAddHaarChar_refl]

theorem map_mul_eq_of_norm_one :
    ∀ (K : Type) [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] [LocallyCompactSpace K]
      [SecondCountableTopology K] [T2Space K] [MeasurableSpace K] [BorelSpace K] (σ : K →+* K),
      Continuous σ → (∀ y, σ (σ y) = y) → ∀ (lam : Measure K) [lam.IsAddHaarMeasure] (u : K),
      u * σ u = 1 → lam.map (fun y => u * y) = lam := by
  intro K _ _ _ _ _ _ _ _ σ hc hi lam _ u hu
  have hu' : σ u * σ (σ u) = 1 := by rw [← map_mul, hu, map_one]
  have hu2 : σ u * u = 1 := by rw [mul_comm, hu]
  have hconj := char_conj σ hc hi u (σ u) hu hu'
  have hprod := char_mul_eq_one u (σ u) hu hu2
  have hsame : mulEquiv (σ u) u hu2 = mulEquiv (σ u) (σ (σ u)) hu' := by
    ext y
    rfl
  rw [hsame, hconj] at hprod
  have hone : addEquivAddHaarChar (mulEquiv u (σ u) hu) = 1 := by
    have h2 : addEquivAddHaarChar (mulEquiv u (σ u) hu) ^ 2 = 1 := by rw [sq, hprod]
    exact (pow_eq_one_iff_of_nonneg zero_le two_ne_zero).1 h2
  have hmap := addEquivAddHaarChar_smul_map lam (mulEquiv u (σ u) hu)
  rw [hone, one_smul] at hmap
  exact hmap

end GlobalTheory.CompanionTheory.SW.NormOneHaar
