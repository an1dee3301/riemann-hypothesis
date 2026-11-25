module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicRapidDecayOfMemAdelicSchwartzSpace
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoMulInvOf
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DecayZero
public import Init.Prelude
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SWQ GlobalTheory.ThetaTransform
open scoped Matrix Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicRapidDecay_of_mem_adelicSchwartzSpace : ∀ (F : Type) [Field F] [NumberField F] (N : ℕ), ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin N), Decay Φ := by
  first | exact @GlobalTheory.SchwartzDecay.decay_of_mem_schA | exact GlobalTheory.SchwartzDecay.decay_of_mem_schA | (intros; apply GlobalTheory.SchwartzDecay.decay_of_mem_schA <;> assumption)
