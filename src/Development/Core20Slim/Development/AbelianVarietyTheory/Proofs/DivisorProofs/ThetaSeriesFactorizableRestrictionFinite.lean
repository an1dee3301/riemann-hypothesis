module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFactorPureTensorComponentAtPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStdCharNegOneOfStandardTraceAdelicAddChar
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicRapidDecayOfMemAdelicSchwartzSpace
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendByZeroMemSchA
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RapidDecayAdelicIntegrablePeriodisationContinuou
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TotallyRealSelfAnnihilatorAdeleCharacter
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqZeroOfFourierEqZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DecayZero
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Countable.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Logic.Function.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.SummationFilter
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun

noncomputable section
namespace GlobalTheory.SplitSvN
open MeasureTheory Matrix ComplexConjugate




variable {F : Type} [Field F] [NumberField F]

theorem schA_facts (hF : IsTotallyReal F) {κ : Type} [Fintype κ] [MeasurableSpace (κ → AF F)] [BorelSpace (κ → AF F)]
    {Φ : (κ → AF F) → ℂ} (hΦ : Φ ∈ schA F κ) : Continuous Φ ∧ (∃ C, ∀ x, ‖Φ x‖ ≤ C) ∧
      ∀ μ : Measure (κ → AF F), μ.IsAddHaarMeasure → Integrable Φ μ := by
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  haveI : BorelSpace (AF F) := ⟨rfl⟩
  let j : Fin (Fintype.card κ) ≃ κ := (Fintype.equivFin κ).symm
  let r : (κ → AF F) ≃ₜ+ (Fin (Fintype.card κ) → AF F) :=
    { toFun := fun x => x ∘ j
      invFun := fun y => y ∘ j.symm
      left_inv := fun x => funext fun i => by simp
      right_inv := fun y => funext fun i => by simp
      map_add' := fun _ _ => rfl
      continuous_toFun := continuous_pi fun i => continuous_apply _
      continuous_invFun := continuous_pi fun i => continuous_apply _ }
  have hd := GlobalTheory.SchwartzDecay.decay_of_mem_schA F _ _ (GlobalTheory.RestrSchA.mem_schA_comp_extend F j j.injective Φ hΦ)
  set Φ' := fun y : Fin (Fintype.card κ) → AF F => Φ (Function.extend j y 0) with hΦ'
  have e : Φ = Φ' ∘ r := funext fun x => by
    show Φ x = Φ (Function.extend j (x ∘ j) 0)
    congr 1
    funext i
    obtain ⟨k, rfl⟩ := j.surjective i
    rw [j.injective.extend_apply]
    rfl
  refine ⟨e ▸ hd.1.comp r.continuous, ?_, fun μ hμ => ?_⟩
  · obtain ⟨C, hC⟩ := hd.2.2 0
    exact ⟨C, fun x => by rw [e]; simpa using hC (r x)⟩
  · have hi := (GlobalTheory.decay_integrable_periodise F _ hF Φ' hd).1 (μ.map r) (r.isAddHaarMeasure_map μ)
    rw [e]
    exact hi.comp_measurable r.continuous.measurable










end GlobalTheory.SplitSvN

end
