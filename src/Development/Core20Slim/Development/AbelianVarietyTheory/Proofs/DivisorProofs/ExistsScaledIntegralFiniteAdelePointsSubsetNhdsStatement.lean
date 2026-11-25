module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsScaledIntegralFiniteAdelePointsSubsetNhds
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenScaledInt
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Filter.Defs
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Defs.Filter

@[expose] public section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.EvAdm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_scaledIntegralFiniteAdelePoints_subset_nhds : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (W : Set (κ → FiniteAdeleRing (𝓞 F) F)),
    W ∈ 𝓝 (0 : κ → FiniteAdeleRing (𝓞 F) F) → ∃ a : F, a ≠ 0 ∧ (scaledInt F κ a : Set (κ → FiniteAdeleRing (𝓞 F) F)) ⊆ W := by
  first | exact @GlobalTheory.EvAdm.exists_scaledInt_subset_of_mem_nhds | exact GlobalTheory.EvAdm.exists_scaledInt_subset_of_mem_nhds | (intros; apply GlobalTheory.EvAdm.exists_scaledInt_subset_of_mem_nhds <;> assumption)
