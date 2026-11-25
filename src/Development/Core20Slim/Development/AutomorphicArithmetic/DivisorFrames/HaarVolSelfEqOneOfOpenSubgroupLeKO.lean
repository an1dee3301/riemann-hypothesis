module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.Core20Slim.Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ScaledIntegerPeriodic
public import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import Init.Core
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
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.ENNReal.Inv
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Nonempty
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Group.Arithmetic
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.Haar.Basic
public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Module
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.Valuation.ValuativeRel.Basic
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Group.Units
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.Sets.Compacts

@[expose] public section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip
open scoped Pointwise

theorem UpperTheory.haarVol_self_eq_one_of_openSubgroup_le_KO :
    ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] {n : Type} [Fintype n] [DecidableEq n] (J : Subgroup (GL n k)), IsOpen (J : Set (GL n k)) → J ≤ KO k n → haarVol (J.map invT) (J : Set (GL n k)) = 1 := by
  intro k _ _ _ _ _ _ n _ _ J hJ hJK
  have hc : Continuous (invT : GL n k →* GL n k) := by
    rw [Units.continuous_iff]
    constructor
    · exact (Units.continuous_coe_inv).matrix_transpose
    · exact (Units.continuous_val).matrix_transpose
  let e : GL n k ≃* GL n k :=
    { toFun := invT, invFun := invT, left_inv := invT_invT, right_inv := invT_invT,
      map_mul' := invT.map_mul }
  have hec : Continuous e := hc
  have hes : Continuous e.symm := hc
  have hem : Measurable e := hec.measurable
  haveI : (Measure.map e (Measure.haar : Measure (GL n k))).IsHaarMeasure :=
    MulEquiv.isHaarMeasure_map _ e hec hes
  have hKOpre : e ⁻¹' (KO k n : Set (GL n k)) = KO k n := by
    ext g
    constructor
    · intro hg
      have := invT_mem_KO (k := k) (g := invT g) hg
      rwa [invT_invT] at this
    · intro hg
      exact invT_mem_KO hg
  have hJpre : e ⁻¹' ((J.map invT : Subgroup (GL n k)) : Set (GL n k)) = J := by
    ext g
    simp only [Set.mem_preimage, SetLike.mem_coe, Subgroup.mem_map]
    constructor
    · rintro ⟨x, hx, hxg⟩
      have hxg' : invT x = invT g := hxg
      have : x = g := by
        have h2 := congrArg invT hxg'
        rwa [invT_invT, invT_invT] at h2
      exact this ▸ hx
    · intro hg
      exact ⟨g, hg, rfl⟩
  obtain ⟨hA0, hAt⟩ := haar_ne_zero_ne_top (Measure.haar : Measure (GL n k)) (isOpen_KO (k := k) (n := n)) le_rfl
  set A := (Measure.haar : Measure (GL n k)) (KO k n) with hA
  have hmapKO : Measure.map e (Measure.haar : Measure (GL n k)) (KO k n) = A := by
    rw [Measure.map_apply hem isOpen_KO.measurableSet, hKOpre]
  have hinv0 : A⁻¹ ≠ 0 := ENNReal.inv_ne_zero.mpr hAt
  have hinvt : A⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr hA0
  haveI : (A⁻¹ • Measure.map e (Measure.haar : Measure (GL n k))).IsHaarMeasure :=
    Measure.IsHaarMeasure.smul (μ := _) hinv0 hinvt
  haveI : (A⁻¹ • (Measure.haar : Measure (GL n k))).IsHaarMeasure :=
    Measure.IsHaarMeasure.smul (μ := _) hinv0 hinvt
  have h1 := eq_haarVol (A⁻¹ • Measure.map e (Measure.haar : Measure (GL n k))) (isOpen_KO (k := k) (n := n)) le_rfl
    (by rw [Measure.smul_apply, hmapKO, smul_eq_mul, ENNReal.inv_mul_cancel hA0 hAt])
  have h2 := eq_haarVol (A⁻¹ • (Measure.haar : Measure (GL n k))) (isOpen_KO (k := k) (n := n)) le_rfl
    (by rw [Measure.smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel hA0 hAt])
  have hmap : Measure.map e (Measure.haar : Measure (GL n k)) = Measure.haar := by
    have h3 := h1.trans h2.symm
    ext s hs
    have h4 := congrArg (fun μ : Measure (GL n k) => A • μ s) h3
    simp only [Measure.smul_apply, smul_eq_mul, ← mul_assoc, ENNReal.mul_inv_cancel hA0 hAt, one_mul] at h4
    exact h4
  have hJ' := (isOpen_map_invT hJ hJK).1
  have heq : (Measure.haar : Measure (GL n k)) ((J.map invT : Subgroup (GL n k)) : Set (GL n k)) =
      (Measure.haar : Measure (GL n k)) J := by
    rw [← hmap, Measure.map_apply hem hJ'.measurableSet, hJpre]
    rw [hmap]
  obtain ⟨hJ0, hJt⟩ := haar_ne_zero_ne_top (Measure.haar : Measure (GL n k)) hJ hJK
  unfold haarVol
  rw [Measure.smul_apply, smul_eq_mul, heq, ENNReal.inv_mul_cancel hJ0 hJt]
