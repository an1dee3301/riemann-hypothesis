module

public import Mathlib
public import Development.Core20Slim.Development.AutomorphicArithmetic.LocalEmbeddings.ArchSz
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnderMemAndPlaceAboveEqOfMem
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlLatCongMove
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralDetCharInvertibleMatrixBallMemSubfield
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.PartialFourierSumInverseOfLatticeDepth
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.Divisors.OmAUnipFourierInv
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import Init.Classical
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.IsField
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Subsemigroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.ZeroLEOne
public import Mathlib.Algebra.Quotient
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.ENNReal.Real
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Quotient.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Group.Arithmetic
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.OuterMeasure.Basic
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Notation
public import Mathlib.Order.SetNotation
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.Valuation.Basic
public import Mathlib.RingTheory.Valuation.Integers
public import Mathlib.RingTheory.Valuation.ValuativeRel.Basic
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Instances.Matrix

@[expose] public section

open MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SplitWeil ValuativeRel GlobalTheory.ConjSize

open GlobalTheory.FunObj.GivenAdm in
theorem UpperTheory.haarVol_KO_le_resCard_pow_of_congruence_le :
    ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] {A : Type} [Fintype A] [DecidableEq A] {J : Subgroup (GL A k)}, IsOpen (J : Set (GL A k)) → J ≤ GlobalTheory.SplitWeil.KO k A → ∀ {ϖ : kˣ} {e : ℕ}, IsUnif ϖ → glLatCong (ϖ ^ e) (GlobalTheory.SplitFlip.stdLat k A) ≤ J → (haarVol J).real (GlobalTheory.SplitWeil.KO k A : Set (GL A k)) ≤ (resCard k : ℝ) ^ (e * Fintype.card A * Fintype.card A) := by
  intro k _ _ _ _ _ _ A _ _ J hJo hJK ϖ e hϖ hN
  classical
  let red : GL A k → Matrix A A (Res k e) := fun g i j =>
    if h : (g : Matrix A A k) i j ∈ 𝒪[k] then Ideal.Quotient.mk (𝓂[k] ^ e) ⟨_, h⟩ else 0
  have key : ∀ g ∈ KO k A, ∀ h ∈ KO k A, red g = red h →
      h⁻¹ * g ∈ glLatCong (ϖ ^ e) (GlobalTheory.SplitFlip.stdLat k A) := by
    intro g hg h hh hgh
    rw [GlobalTheory.FunObj.GivenAdm.mem_glLatCong]
    refine ⟨mul_mem (inv_mem hh) hg, ?_⟩
    have hg' := (mem_KO_iff g).1 hg
    have hh' := (mem_KO_iff h).1 hh
    have e1 : ((h⁻¹ * g : GL A k) : Matrix A A k) - 1
        = ((h⁻¹ : GL A k) : Matrix A A k) * ((g : Matrix A A k) - (h : Matrix A A k)) := by
      rw [Matrix.mul_sub, Units.val_mul, ← Units.val_mul h⁻¹ h, inv_mul_cancel, Units.val_one]
    rw [e1]
    refine GlobalTheory.FunObj.GivenAdm.CongM.mul_left ?_ (fun i j => hh'.2 i j)
    intro i j
    have hij := congrFun (congrFun hgh i) j
    simp only [red, dif_pos (hg'.1 i j), dif_pos (hh'.1 i j)] at hij
    rw [Ideal.Quotient.eq] at hij
    have hv := (Model.val_le_iff_mem hϖ e _).1 hij
    simpa [Matrix.sub_apply] using hv
  haveI := isHaarMeasure_haarVol hJo hJK
  have hNJ : haarVol J (glLatCong (ϖ ^ e) (GlobalTheory.SplitFlip.stdLat k A) : Set (GL A k)) ≤ 1 := by
    rw [← haarVol_self hJo hJK]
    exact measure_mono hN
  have piece : ∀ M : Matrix A A (Res k e), haarVol J {g | g ∈ KO k A ∧ red g = M} ≤ 1 := by
    intro M
    by_cases hne : ∃ g0, g0 ∈ KO k A ∧ red g0 = M
    · obtain ⟨g0, hg0, hM⟩ := hne
      calc haarVol J {g | g ∈ KO k A ∧ red g = M}
          ≤ haarVol J ((fun h => g0⁻¹ * h) ⁻¹'
              (glLatCong (ϖ ^ e) (GlobalTheory.SplitFlip.stdLat k A) : Set (GL A k))) := by
            apply measure_mono
            rintro g ⟨hg, hgM⟩
            exact key g hg g0 hg0 (hgM.trans hM.symm)
        _ = haarVol J (glLatCong (ϖ ^ e) (GlobalTheory.SplitFlip.stdLat k A) : Set (GL A k)) :=
            measure_preimage_mul _ _ _
        _ ≤ 1 := hNJ
    · calc haarVol J {g | g ∈ KO k A ∧ red g = M} ≤ haarVol J ∅ := by
            apply measure_mono
            intro g hg
            exact absurd ⟨g, hg⟩ hne
        _ = 0 := measure_empty
        _ ≤ 1 := zero_le_one
  have hKO : haarVol J (KO k A : Set (GL A k))
      ≤ (Fintype.card (Matrix A A (Res k e)) : ENNReal) := by
    calc haarVol J (KO k A : Set (GL A k))
        ≤ haarVol J (⋃ M ∈ (Finset.univ : Finset (Matrix A A (Res k e))),
            {g | g ∈ KO k A ∧ red g = M}) := by
          apply measure_mono
          intro g hg
          simp only [Set.mem_iUnion]
          exact ⟨red g, Finset.mem_univ _, hg, rfl⟩
      _ ≤ ∑ M ∈ (Finset.univ : Finset (Matrix A A (Res k e))),
            haarVol J {g | g ∈ KO k A ∧ red g = M} := measure_biUnion_finset_le _ _
      _ ≤ ∑ M ∈ (Finset.univ : Finset (Matrix A A (Res k e))), (1 : ENNReal) :=
          Finset.sum_le_sum (fun M _ => piece M)
      _ = (Fintype.card (Matrix A A (Res k e)) : ENNReal) := by
          simp [Finset.card_univ]
  have hcard : Fintype.card (Matrix A A (Res k e))
      = resCard k ^ (e * Fintype.card A * Fintype.card A) := by
    have h1 : Fintype.card (Matrix A A (Res k e))
        = Fintype.card (Res k e) ^ (Fintype.card A * Fintype.card A) := by
      rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card, Fintype.card_eq_nat_card]
      show Nat.card (A → A → Res k e) = _
      rw [Nat.card_fun, Nat.card_fun, ← pow_mul, mul_comm]
    rw [h1, GlobalTheory.FlipMatch.FourierInv.card_res_pow, ← pow_mul, mul_assoc]
  rw [measureReal_def]
  have := ENNReal.toReal_mono (by simp) hKO
  rw [hcard] at this
  simpa using this
