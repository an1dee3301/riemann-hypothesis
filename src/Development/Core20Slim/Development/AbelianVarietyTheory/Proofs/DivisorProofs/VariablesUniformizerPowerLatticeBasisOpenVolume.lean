module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemVarLat
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import Development.AbelianVarietyTheory.Definitions.Foundations.SimpleSum
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasurableSetSetOfLe
public import Init.Classical
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Units
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Algebra.Order.Archimedean.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Order.IsBotOne
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.Finite.Prod
public import Mathlib.Basic.Finite.Sum
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Sets
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Set.Operations
public import Mathlib.GroupTheory.ArchimedeanDensely
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.Haar.DistribChar
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Order.Filter.AtTopBot.Defs
public import Mathlib.Order.Filter.Basic
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.Filter.Finite
public import Mathlib.Order.Filter.Pi
public import Mathlib.Order.Lattice
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.Valuation.Basic
public import Mathlib.RingTheory.Valuation.Integers
public import Mathlib.RingTheory.Valuation.RankOne
public import Mathlib.RingTheory.Valuation.ValuativeRel.Basic
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Topology.Algebra.ConstMulAction
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.ValuativeRel.ValuativeTopology
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Compactness.LocallyCompact
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter

@[expose] public section

open MeasureTheory ValuativeRel GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.UnfoldLoss

namespace GlobalTheory.UnfoldLoss.LatVol

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem varLat_eq_pi (G : Grid k) (ϖ : kˣ) (n : ℕ) :
    (varLat G ϖ n : Set (Vars G)) = Set.univ.pi fun _ => Set.univ.pi fun _ => cball (ϖ ^ n) := by
  ext e
  exact ⟨fun h j _ r _ => h j r, fun h j r => h j trivial r trivial⟩

theorem eventually_cball_subset {ϖ : kˣ} (hϖ : IsUnif ϖ) {U : Set k} (hU : U ∈ nhds (0 : k)) :
    ∀ᶠ n : ℕ in Filter.atTop, cball (ϖ ^ n) ⊆ U := by
  obtain ⟨γ, hγ⟩ := (IsValuativeTopology.mem_nhds_zero_iff U).mp hU
  have h1 : valuation k (ϖ : k) < 1 := hϖ ▸ uniformizer_lt_one
  haveI : MulArchimedean (ValueGroupWithZero k) := ValuativeRel.isRankLeOne_iff_mulArchimedean.mp inferInstance
  obtain ⟨N, hN⟩ := exists_pow_lt₀ h1 γ
  refine Filter.eventually_atTop.2 ⟨N, fun n hn z hz => hγ ?_⟩
  have hz' : valuation k z ≤ valuation k ((ϖ ^ n : kˣ) : k) := hz
  rw [Units.val_pow_eq_pow_val, map_pow] at hz'
  exact (hz'.trans (pow_le_pow_of_le_one zero_le h1.le hn)).trans_lt hN

theorem varLat_basis_open_vol : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]
    (G : Grid k) (ν : Measure k), IsUnitVol ν → ∀ ϖ : kˣ, IsUnif ϖ →
    (∀ s ∈ nhds (0 : Vars G), ∃ n : ℕ, (varLat G ϖ n : Set (Vars G)) ⊆ s) ∧
    ∀ n : ℕ, IsOpen (varLat G ϖ n : Set (Vars G)) ∧ varsVol G ν (varLat G ϖ n : Set (Vars G)) ≠ ⊤ ∧
      (varsVol G ν).real (varLat G ϖ n : Set (Vars G)) = ((resCard k : ℝ)⁻¹) ^ (n * varCount G) := by
  intro k _ _ _ _ _ _ G ν hν ϖ hϖ
  classical
  refine ⟨fun s hs => ?_, fun n => ?_⟩
  · rw [nhds_pi, Filter.mem_pi'] at hs
    obtain ⟨I, t, ht, hts⟩ := hs
    have key : ∀ j, ∀ᶠ n : ℕ in Filter.atTop, (Set.univ.pi fun _ => cball (ϖ ^ n)) ⊆ t j := fun j => by
      have hj := ht j
      rw [nhds_pi, Filter.mem_pi'] at hj
      obtain ⟨J, u, hu, hut⟩ := hj
      filter_upwards [Filter.eventually_all.2 fun r => eventually_cball_subset hϖ (hu r)] with n hn e he
      exact hut fun r _ => hn r (he r trivial)
    obtain ⟨n, hn⟩ := (Filter.eventually_all.2 key).exists
    refine ⟨n, fun e he => hts fun j _ => hn j fun r _ => he j r⟩
  · haveI := hν.1
    haveI := secondCountable k
    have h1 : ((distribHaarChar k ϖ : NNReal) : ℝ) = (resCard k : ℝ)⁻¹ :=
      nabs_uniformiser hϖ.irreducible rfl
    have hv : varsVol G ν (varLat G ϖ n : Set (Vars G)) =
        ((distribHaarChar k ϖ ^ (n * varCount G) : NNReal) : ENNReal) := by
      rw [varLat_eq_pi, varsVol, Measure.pi_pi]
      simp only [Measure.pi_pi, measure_cball, hν.2, mul_one, Finset.prod_const, Finset.card_univ, map_pow,
        varCount, ← Nat.card_eq_fintype_card, ENNReal.coe_pow, ← pow_mul, Finset.prod_pow_eq_pow_sum, Finset.mul_sum]
    refine ⟨?_, ?_, ?_⟩
    · rw [varLat_eq_pi]
      exact isOpen_set_pi Set.finite_univ fun _ _ => isOpen_set_pi Set.finite_univ fun _ _ => isOpen_cball _
    · rw [hv]; exact ENNReal.coe_ne_top
    · rw [Measure.real, hv, ENNReal.coe_toReal, NNReal.coe_pow, h1]

end GlobalTheory.UnfoldLoss.LatVol
