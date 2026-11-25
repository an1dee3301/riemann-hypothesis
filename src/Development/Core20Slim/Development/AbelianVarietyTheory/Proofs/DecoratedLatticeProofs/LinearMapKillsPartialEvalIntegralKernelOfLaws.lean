module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsRead
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchwartzBruhatLinearFunctional
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousCharactersLocallyConstantNonarchLocalF
public import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import Init.ByCases
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.NeZero
public import Init.Data.Zero
public import Init.Ext
public import Init.Prelude
public import Init.SimpLemmas
public import Init.SizeOf
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Notation.Prod
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.UnitBall
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Disjoint
public import Mathlib.Data.Finset.Empty
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Sets
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Basis
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Prod.Basic
public import Mathlib.Data.Subtype
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.OuterMeasure.AE
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.Order.Disjoint
public import Mathlib.Order.Filter.Basic
public import Mathlib.RingTheory.Valuation.ValuativeRel.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.Support
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.LocallyConstant.Basic

@[expose] public section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData

noncomputable section
namespace GlobalTheory.FlatFactor.KerEngine

def pullSB {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) : SB Y →ₗ[ℂ] SB X where
  toFun Φ := ⟨Φ.1 ∘ e, Φ.2.1.comp_continuous e.continuous, Φ.2.2.comp_homeomorph e⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem pullSB_apply {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) (Φ : SB Y) (x : X) :
    (pullSB e Φ).1 x = Φ.1 (e x) := rfl

section Trip
variable {k : Type} [Field k] {m m' : Type} [Fintype m] [DecidableEq m] [Fintype m'] [DecidableEq m']

abbrev Rest (ev it : Finset (m × m')) := {e : m × m' // e ∉ it ∧ e ∉ ev}

def toTrip (ev it : Finset (m × m')) (β t : Matrix m m' k) :
    (Rest ev it → k) × ({e // e ∈ ev} → k) × ({e // e ∈ it} → k) :=
  (fun i => t i.1.1 i.1.2, fun i => t i.1.1 i.1.2 - β i.1.1 i.1.2, fun i => t i.1.1 i.1.2)

def ofTrip (ev it : Finset (m × m')) (β : Matrix m m' k)
    (x : (Rest ev it → k) × ({e // e ∈ ev} → k) × ({e // e ∈ it} → k)) : Matrix m m' k :=
  Matrix.of fun r q => if h : (r, q) ∈ it then x.2.2 ⟨(r, q), h⟩
    else if h' : (r, q) ∈ ev then β r q + x.2.1 ⟨(r, q), h'⟩ else x.1 ⟨(r, q), h, h'⟩

theorem ofTrip_toTrip (ev it : Finset (m × m')) (β t : Matrix m m' k) : ofTrip ev it β (toTrip ev it β t) = t := by
  ext r q
  simp only [ofTrip, toTrip, Matrix.of_apply]
  split_ifs <;> ring

theorem toTrip_ofTrip (ev it : Finset (m × m')) (hd : Disjoint ev it) (β : Matrix m m' k)
    (x : (Rest ev it → k) × ({e // e ∈ ev} → k) × ({e // e ∈ it} → k)) : toTrip ev it β (ofTrip ev it β x) = x := by
  obtain ⟨x₀, x₁, x₂⟩ := x
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> funext i
  · have h := i.2
    simp only [toTrip, ofTrip, Matrix.of_apply, dif_neg h.1, dif_neg h.2]
  · have h : i.1 ∉ it := Finset.disjoint_left.mp hd i.2
    simp only [toTrip, ofTrip, Matrix.of_apply, dif_neg h, dif_pos i.2]
    ring
  · simp only [toTrip, ofTrip, Matrix.of_apply, dif_pos i.2]

variable [TopologicalSpace k] [IsTopologicalRing k]

def trip (ev it : Finset (m × m')) (hd : Disjoint ev it) (β : Matrix m m' k) :
    Matrix m m' k ≃ₜ (Rest ev it → k) × ({e // e ∈ ev} → k) × ({e // e ∈ it} → k) where
  toFun := toTrip ev it β
  invFun := ofTrip ev it β
  left_inv := ofTrip_toTrip ev it β
  right_inv := toTrip_ofTrip ev it hd β
  continuous_toFun := by
    refine Continuous.prodMk ?_ (Continuous.prodMk ?_ ?_) <;> refine continuous_pi fun i => ?_
    · exact continuous_id.matrix_elem _ _
    · exact (continuous_id.matrix_elem _ _).sub continuous_const
    · exact continuous_id.matrix_elem _ _
  continuous_invFun := by
    refine continuous_matrix fun r q => ?_
    simp only [ofTrip, Matrix.of_apply]
    split_ifs
    · exact (continuous_apply _).comp (continuous_snd.comp continuous_snd)
    · exact continuous_const.add ((continuous_apply _).comp (continuous_fst.comp continuous_snd))
    · exact (continuous_apply _).comp continuous_fst

theorem trip_apply (ev it : Finset (m × m')) (hd : Disjoint ev it) (β t : Matrix m m' k) :
    trip ev it hd β t = toTrip ev it β t := rfl

end Trip

end GlobalTheory.FlatFactor.KerEngine

namespace GlobalTheory.FlatFactor.KerEngine
open GlobalTheory.FlatFactor

section Laws
variable {k : Type} [Field k] {m m' : Type} [Fintype m] [DecidableEq m] [Fintype m'] [DecidableEq m']

theorem sum_single_apply (it : Finset (m × m')) (a : m × m' → k) (r : m) (q : m') :
    (∑ e ∈ it, Matrix.single e.1 e.2 (a e)) r q = if (r, q) ∈ it then a (r, q) else 0 := by
  rw [Matrix.sum_apply]
  have : ∀ e : m × m', Matrix.single e.1 e.2 (a e) r q = if (r, q) = e then a e else 0 := by
    rintro ⟨x, y⟩
    simp only [Matrix.single_apply, Prod.mk.injEq]
    split_ifs <;> aesop
  simp_rw [this, Finset.sum_ite_eq]

theorem toTrip_add (ev it : Finset (m × m')) (hd : Disjoint ev it) (β t : Matrix m m' k) (a : {e // e ∈ it} → k) :
    toTrip ev it β (t + ∑ e ∈ it, Matrix.single e.1 e.2 (if h : e ∈ it then a ⟨e, h⟩ else 0)) =
      toTrip ev it β t + (0, 0, a) := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> funext i
  · have h := i.2
    simp only [toTrip, Matrix.add_apply, sum_single_apply, h.1, if_false, add_zero,
      Pi.add_apply, Pi.zero_apply] <;> simp
  · have h : i.1 ∉ it := Finset.disjoint_left.mp hd i.2
    simp only [toTrip, Matrix.add_apply, sum_single_apply, h, if_false, add_zero,
      Pi.add_apply, Pi.zero_apply] <;> simp
  · simp only [toTrip, Matrix.add_apply, sum_single_apply, i.2, if_true, dif_pos,
      Pi.add_apply, Pi.zero_apply, zero_add] <;> simp

theorem ofTrip_zero (ev it : Finset (m × m')) (β : Matrix m m' k) (x₀ : Rest ev it → k) (a : {e // e ∈ it} → k) :
    ofTrip ev it β (x₀, 0, a) = fill ev it β (ofTrip ev it β (x₀, 0, 0)) a := by
  ext r q
  simp only [ofTrip, fill, Matrix.of_apply]
  split_ifs <;> simp

end Laws

theorem kerRed_of_laws : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k), Continuous ψ → ψ ≠ 1 → ν.IsAddHaarMeasure → ∀ (m m' : Type) [Fintype m] [DecidableEq m] [Fintype m'] [DecidableEq m'] (M : Type) [AddCommGroup M] [Module ℂ M] (l : SB (Matrix m m' k) →ₗ[ℂ] M) (β : Matrix m m' k) (ev it : Finset (m × m')), Disjoint ev it → (∀ (b : m × m' → k) (Θ Θ' : SB (Matrix m m' k)), (∀ t, Θ'.1 t = (ψ (∑ e ∈ ev, b e * (t e.1 e.2 - β e.1 e.2)) : ℂ) * Θ.1 t) → l Θ' = l Θ) → (∀ (a : m × m' → k) (Θ Θ' : SB (Matrix m m' k)), (∀ t, Θ'.1 t = Θ.1 (t + ∑ e ∈ it, Matrix.single e.1 e.2 (a e))) → l Θ' = l Θ) → GlobalTheory.FlatFactor.KerRed ν ev it β l := by
  intro k _ _ _ _ _ _ ψ ν hψc hψ1 hν m m' _ _ _ _ M _ _ l β ev it hd h1 h2 Θ hΘ
  let e := trip (k := k) ev it hd β
  let l' := l ∘ₗ pullSB e
  have hback : pullSB e (pullSB e.symm Θ) = Θ := by
    ext t
    simp [pullSB_apply]
  have key := GlobalTheory.CoinvSB.kernel k ψ ν hψc hψ1 hν (Rest ev it) {x // x ∈ ev} {x // x ∈ it} M l' ?_ ?_
    (pullSB e.symm Θ) ?_
  · simpa [l', hback] using key
  · intro b Φ Φ' hΦ
    refine h1 (fun e => if h : e ∈ ev then b ⟨e, h⟩ else 0) (pullSB e Φ) (pullSB e Φ') fun t => ?_
    rw [pullSB_apply, pullSB_apply, hΦ]
    congr 3
    simp only [e, trip_apply, toTrip, dotProduct]
    rw [← Finset.sum_coe_sort ev]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [i.2]
  · intro a Φ Φ' hΦ
    refine h2 (fun e => if h : e ∈ it then a ⟨e, h⟩ else 0) (pullSB e Φ) (pullSB e Φ') fun t => ?_
    rw [pullSB_apply, pullSB_apply, hΦ]
    simp only [e, trip_apply]
    rw [toTrip_add ev it hd β t a]
  · intro x₀
    have hr := hΘ (ofTrip ev it β (x₀, 0, 0))
    simp only [red] at hr
    rw [← hr]
    refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
    simp only [pullSB_apply]
    rw [← ofTrip_zero]
    rfl

end GlobalTheory.FlatFactor.KerEngine
