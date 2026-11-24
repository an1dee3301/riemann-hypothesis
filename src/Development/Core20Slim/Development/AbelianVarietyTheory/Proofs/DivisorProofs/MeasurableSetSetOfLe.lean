module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.AuxiliaryVectorUniformizerExponent
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesEqPrimFrameLat
public import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import Development.AbelianVarietyTheory.Definitions.Foundations.SecondCountableAndT2LocalField
public import Development.AbelianVarietyTheory.Definitions.Foundations.SimpleSum
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoxFunctionDiagonalAction
public import Init.Classical
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.List.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pointwise.Set.Basic
public import Mathlib.Algebra.Group.Action.Units
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pointwise.Set.Scalar
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.GroupWithZero.Units.Lemmas
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Order.IsBotOne
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Countable.Basic
public import Mathlib.Basic.Countable.Defs
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.ENNReal.BigOperators
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Empty
public import Mathlib.Data.Finset.Insert
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Sets
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Int.Cast.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Int.Init
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Lattice
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.Valuation.Basic
public import Mathlib.RingTheory.Valuation.Integers
public import Mathlib.RingTheory.Valuation.ValuativeRel.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.ValuativeRel.ValuativeTopology
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Compactness.LocallyCompact
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Separation.Hausdorff

@[expose] public section

open MeasureTheory ValuativeRel Matrix

noncomputable section
namespace GlobalTheory.OriginBox
open GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx

section Generic
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem apow_zpow (x : kˣ) (n : ℤ) (z : ℂ) : apow (x ^ n) z = apow x (n * z) := by
  induction n using Int.induction_on with
  | zero => simp
  | succ n ih =>
    rw [_root_.zpow_add_one, apow_mul, ih, ← apow_add]; push_cast; ring_nf
  | pred n ih =>
    rw [_root_.zpow_sub_one, apow_mul, ih, apow_inv, ← apow_add]; push_cast; ring_nf

theorem prod_apow_list (ϖ : kˣ) {α : Type*} (l : List α) (f : α → ℂ) :
    (l.map fun b => apow ϖ (f b)).prod = apow ϖ (l.map f).sum := by
  induction l with
  | nil => simp
  | cons b l ih => rw [List.map_cons, List.prod_cons, ih, ← apow_add]; simp

theorem prod_apow_finset (ϖ : kˣ) {α : Type*} (s : Finset α) (f : α → ℂ) :
    ∏ i ∈ s, apow ϖ (f i) = apow ϖ (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.prod_insert hi, Finset.sum_insert hi, ih, ← apow_add]

end Generic
end GlobalTheory.OriginBox

namespace GlobalTheory.OriginBox
open GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx

section Vol
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem setOf_le_eq_preimage (u : kˣ) :
    {x : k | valuation k x ≤ valuation k (u : k)} = (fun x => ((u⁻¹ : kˣ) : k) * x) ⁻¹' (𝒪[k] : Set k) := by
  ext x
  have h0 : 0 < valuation k (u : k) := zero_lt_iff.2 (by simp)
  simp only [Set.mem_setOf_eq, Set.mem_preimage, SetLike.mem_coe, Valuation.mem_integer_iff, map_mul,
    Units.val_inv_eq_inv_val, map_inv₀]
  rw [inv_mul_le_one₀ h0]

variable [MeasurableSpace k] [BorelSpace k]

theorem measurableSet_setOf_le (u : kˣ) : MeasurableSet {x : k | valuation k x ≤ valuation k (u : k)} := by
  rw [setOf_le_eq_preimage]
  exact (Model.isOpen_int.preimage (continuous_const.mul continuous_id)).measurableSet

theorem vol_setOf_le (ν : Measure k) (hν : IsUnitVol ν) (u : kˣ) :
    ν {x : k | valuation k x ≤ valuation k (u : k)} = ENNReal.ofReal (nabs k u) := by
  rw [← Model.nabs_vol ν hν u, setOf_le_eq_preimage]
  congr 1
  ext x
  rw [Set.mem_smul_set_iff_inv_smul_mem]
  rfl

theorem measurableSet_box (G : Grid k) (ϖ : kˣ) (a a' : ℤ) : MeasurableSet (box G ϖ a a') :=
  MeasurableSet.univ_pi fun _ => MeasurableSet.univ_pi fun _ => measurableSet_setOf_le _

open Classical in
theorem vol_box (G : Grid k) (ν : Measure k) (hν : IsUnitVol ν) (ϖ : kˣ) (a a' : ℤ) :
    (varsVol G ν (box G ϖ a a')).toReal = ∏ j, ∏ v, nabs k (ϖ ^ boxExp G a a' j v) := by
  obtain ⟨_, _⟩ := Model.secondCountable_and_t2_local_field (k := k)
  have := hν.1
  rw [varsVol, box, Measure.pi_pi, ENNReal.toReal_prod]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [Measure.pi_pi, ENNReal.toReal_prod]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [vol_setOf_le ν hν, ENNReal.toReal_ofReal (Model.nabs_pos _).le]

end Vol
end GlobalTheory.OriginBox

namespace GlobalTheory.OriginBox
open GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx

section Expo
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem prod_zpow_units {α : Type*} (ϖ : kˣ) (s : Finset α) (f : α → ℤ) : ∏ i ∈ s, ϖ ^ f i = ϖ ^ ∑ i ∈ s, f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.prod_insert hi, Finset.sum_insert hi, ih, _root_.zpow_add]

variable (G : Grid k)

def vtxDet (a a' : ℤ) (X : ℕ × ℕ) : ℤ :=
  if X.1 = G.m then ∑ x : Fin (G.rank (G.m, X.2)), vtxExp a a' (G.m - 1 - X.2) (topRank G X.2) x else 0


open Classical in
def expo (a a' : ℤ) : ℤ :=
  ((oppositePath G.m).map fun b => vtxDet G a a' b.src * G.rank b.tgt - vtxDet G a a' b.tgt * G.rank b.src).sum -
    2 * ∑ j, ∑ v, boxExp G a a' j v

variable {G}

theorem gdet_eq (ϖ : kˣ) (a a' : ℤ) (g : G.VertexGroup) (hg : ∀ j, g (G.m, j) = colDiag G ϖ a a' j)
    (hg' : ∀ i j, i ≠ G.m → g (i, j) = 1) (X : ℕ × ℕ) : gdet (g X) = ϖ ^ vtxDet G a a' X := by
  obtain ⟨i, j⟩ := X
  by_cases hi : i = G.m
  · rw [show (i, j) = (G.m, j) by rw [hi], hg, vtxDet, if_pos rfl, colDiag, gdet, det_diagGL, prod_zpow_units]
  · rw [hg' i j hi, vtxDet, if_neg hi]
    simp

end Expo
end GlobalTheory.OriginBox
