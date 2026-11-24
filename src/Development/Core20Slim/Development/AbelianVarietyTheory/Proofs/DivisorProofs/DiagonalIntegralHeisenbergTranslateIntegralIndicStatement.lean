module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalIntegralHeisenbergTranslateIntegralIndic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagWZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyIntegralPointsIndicatorIsVacuum
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Core
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Notation.Indicator
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Notation.Prod
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels MeasureTheory GlobalTheory.LatVac GlobalTheory.InertVacLag GlobalTheory.InertLagChar
open scoped TensorProduct Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.diagonal_integral_heisenberg_translate_integral_indicator : ∀ (F : Type) [Field F] [NumberField F] (v : Pl (F := F)) (κ : Type) [Fintype κ] (ψ : AddChar (AF F) ℂ), PsiUnr ψ v → (2 : 𝓞 F) ∉ v.asIdeal →
    ∀ (μ : @Measure (κ → Fv F v) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    ∃ φ₀ ∈ SB (κ → Fv F v), ∃ c : ℂ, c ≠ 0 ∧ ∃ U : Set ((κ → Fv F v) × (κ → Fv F v)), IsOpen U ∧ IsCompact U ∧ 0 ∈ U ∧
      ∀ w, diagW (psiAt ψ v) μ (boxFun φ₀ φ₀) w = U.indicator (fun _ => c) w := by
  first | exact @GlobalTheory.InertLagInd.diagW_box_indicator | exact GlobalTheory.InertLagInd.diagW_box_indicator | (intros; apply GlobalTheory.InertLagInd.diagW_box_indicator <;> assumption)
