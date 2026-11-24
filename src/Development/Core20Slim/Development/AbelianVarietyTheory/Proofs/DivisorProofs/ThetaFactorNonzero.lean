module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsSplitChartSplitChart
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.GSEqZeroOfLt
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Foundations.NonemptyAlgHomOfNotIsField
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSplitChartOne
public import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Core
public import Init.Data.Function
public import Init.Data.Int.Basic
public import Init.Data.Order.Lemmas
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.Algebra.Group.WithOne.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.GroupWithZero.Units.Lemmas
public import Mathlib.Algebra.GroupWithZero.WithZero
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Order.Monoid.Unbundled.TypeTags
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.RelClasses
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Valuation.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.Tactic.Push
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Algebra.Valued.ValuationTopology
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

namespace GlobalTheory.StepFacNe

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun


open NumberField IsDedekindDomain in
theorem _root_.GlobalTheory.StepFacNe.chrW_continuous {F E : Type} [Field F] [NumberField F]
    [Field E] [NumberField E] [Algebra F E]
    (χ : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E) (h : Continuous χ) {v : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)}
    (τ : E →ₐ[F] _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) :
    Continuous (fun x : (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v)ˣ => (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.chrW χ τ x : ℂ)) := by
  unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.chrW
  have h1 := _root_.GlobalTheory.LFun.continuous_locChar h (_root_.GlobalTheory.AdelicU.splitPrime τ)
  have h2 := Continuous.units_map
    (_root_.GlobalTheory.LFun.complMap (_root_.GlobalTheory.AdelicU.splitPrime_under τ)).toMonoidHom
    (_root_.GlobalTheory.LFun.SplitChart.continuous_complMap (_root_.GlobalTheory.AdelicU.splitPrime_under τ))
  exact h1.comp h2


open NumberField IsDedekindDomain in
theorem _root_.GlobalTheory.StepFacNe.chrW_ram {F E : Type} [Field F]
    [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (χ : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E) {v : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)} (τ : E →ₐ[F] _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v)
    (h : ¬ _root_.GlobalTheory.LFun.UnrAt χ (_root_.GlobalTheory.AdelicU.splitPrime τ)) :
    ∃ x : (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v)ˣ, (x : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) ∈ v.adicCompletionIntegers F ∧
      ((x⁻¹ : (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v)ˣ) : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) ∈ v.adicCompletionIntegers F ∧
        _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.chrW χ τ x ≠ 1 := by
  have hw := _root_.GlobalTheory.AdelicU.splitPrime_under τ
  unfold _root_.GlobalTheory.LFun.UnrAt at h
  push_neg at h
  obtain ⟨y, hy1, hy2⟩ := h
  unfold _root_.Formalism.L2.Host.IsUnitAt at hy1
  obtain ⟨a, ha⟩ := (_root_.GlobalTheory.LFun.SplitTie.complMap_bijective τ hw).2 (y : _)
  have hv : Valued.v a = 1 := by
    rw [← _root_.GlobalTheory.LFun.SplitTie.valued_complMap τ hw, ha]
    exact hy1
  have ha0 : a ≠ 0 := by
    rintro rfl
    simp at hv
  refine ⟨Units.mk0 a ha0, ?_, ?_, ?_⟩
  · rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    simp [hv]
  · rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    simp [hv]
  · intro h1
    apply hy2
    have hy : Units.map (_root_.GlobalTheory.LFun.complMap hw).toMonoidHom (Units.mk0 a ha0) = y :=
      Units.ext (by simpa using ha)
    unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.chrW at h1
    rw [MonoidHom.comp_apply, hy] at h1
    exact h1

end GlobalTheory.StepFacNe
