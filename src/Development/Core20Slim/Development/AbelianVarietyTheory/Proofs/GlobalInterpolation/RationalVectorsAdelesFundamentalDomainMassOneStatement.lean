module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RationalVectorsAdelesFundamentalDomainMassOne
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DecayZero
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Core
public import Init.Data.Function
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Subgroup.Actions
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Defs.Filter

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.SWQ
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rationalVectors_adeles_fundamentalDomain_mass_one : ∀ (F : Type) [Field F] [NumberField F] (N : ℕ) (ν : Measure (AF F)), IsCov1 ν → (muV N ν).IsAddHaarMeasure ∧ (∀ u : (Fin N → AF F), u ∈ (AddSubgroup.closure (Set.range (rat : (Fin N → F) → (Fin N → AF F)))) ↔ ∃ ξ, u = rat ξ) ∧ Function.Injective (rat : (Fin N → F) → (Fin N → AF F)) ∧ (∃ K : Set (Fin N → AF F), IsCompact K ∧ ∀ u, ∃ ξ, u - rat ξ ∈ K) ∧ ∃ D : Set (Fin N → AF F), MeasurableSet D ∧ IsAddFundamentalDomain (AddSubgroup.closure (Set.range (rat : (Fin N → F) → (Fin N → AF F)))) D (muV N ν) ∧ muV N ν D = 1 := by
  first | exact @GlobalTheory.SWQ.rat_lattice_fundamentalDomain | exact GlobalTheory.SWQ.rat_lattice_fundamentalDomain | (intros; apply GlobalTheory.SWQ.rat_lattice_fundamentalDomain <;> assumption)
