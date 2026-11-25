module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorIntMMemSB
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalCharacterSmoothUnitary
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.GSEqZeroOfLt
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsSplitChartSplitChart
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import Development.AbelianVarietyTheory.Definitions.Foundations.NonemptyAlgHomOfNotIsField
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsOpenKerOfContinuous
public import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Classical
public import Init.Core
public import Init.Data.Function
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.Algebra.Group.WithOne.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.GroupWithZero.WithZero
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Valuation.Basic
public import Mathlib.RingTheory.Valuation.ValuativeRel.Basic
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Algebra.Valued.ValuationTopology
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

namespace GlobalTheory.ChrWLocal

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
open ValuativeRel

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem valuation_eq_one_iff {v : Pl F} (x : Fv F v) :
    valuation (Fv F v) x = 1 ↔ Valued.v x = 1 := by
  have : (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  exact (isEquiv (valuation (v.adicCompletion F))
    (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ)))).eq_one_iff_eq_one

theorem isUnram_chrW_iff (χ : Chr F E) {v : Pl F} (t : E →ₐ[F] Fv F v) :
    GlobalTheory.SplitWeil.IsUnram (chrW χ t) ↔ UnrAt χ (splitPrime t) := by
  constructor
  · intro h y hy
    obtain ⟨a, ha⟩ := (SplitTie.complMap_bijective t (splitPrime_under t)).2 (y : _)
    have hv : Valued.v a = 1 := by
      rw [← SplitTie.valued_complMap t (splitPrime_under t), ha]; exact hy
    have h0 : a ≠ 0 := by rintro rfl; simp at hv
    have h1 := h (Units.mk0 a h0) ((valuation_eq_one_iff _).2 hv)
    rw [← h1]
    exact congrArg (locChar χ _) (Units.ext ha.symm)
  · intro h x hx
    exact h _ (show Valued.v (complMap (splitPrime_under t) (x : Fv F v)) = 1 by
      rw [SplitTie.valued_complMap t (splitPrime_under t)]; exact (valuation_eq_one_iff _).1 hx)

theorem chrW_local : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (χ : Chr F E),
    IsHecke F E χ →
    ∀ (v : Pl F) (t : E →ₐ[F] Fv F v), IsSmU (chrW χ t) ∧ (∃ e, GlobalTheory.SplitFlip.CondLE (unifAt v) e (chrW χ t)) ∧
      (GlobalTheory.SplitWeil.IsUnram (chrW χ t) ↔ UnrAt χ (splitPrime t)) := by
  intro F E _ _ _ _ _ χ hχ v t
  have hc := GlobalTheory.ChrWSmooth.continuous_chrW hχ.1 t
  refine ⟨⟨GlobalTheory.RootEx.UniformLattices.isOpen_ker_of_continuous _ hc, GlobalTheory.ChrWSmooth.isUnitaryChar_chrW χ t⟩, ?_,
    isUnram_chrW_iff χ t⟩
  exact GlobalTheory.GaussNonvanish.exists_condLE (GlobalTheory.SplitFlip.exists_isUnif (k := Fv F v)).choose_spec _
    (Units.continuous_val.comp hc)

end GlobalTheory.ChrWLocal
