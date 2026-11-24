module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsScaleFractionalIdealIntegralAvoidMaximals
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Maximal
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs

@[expose] public section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_scale_fractionalIdeal_integral_avoid_maximals : ∀ (E : Type) [Field E] [NumberField E] (I : Submodule (𝓞 E) E), I.FG → I ≠ ⊥ →
    ∀ (ι : Type) [Fintype ι] (Q : ι → Ideal (𝓞 E)), (∀ i, (Q i).IsMaximal) →
    ∃ s : E, s ≠ 0 ∧ (∀ a ∈ I, IsIntegral ℤ (s * a)) ∧ ∀ i, ∃ a ∈ I, ∃ o : 𝓞 E, (o : E) = s * a ∧ o ∉ Q i := by
  first | exact @GlobalTheory.exists_scale_integral_not_le_maximal | exact GlobalTheory.exists_scale_integral_not_le_maximal | (intros; apply GlobalTheory.exists_scale_integral_not_le_maximal <;> assumption)
