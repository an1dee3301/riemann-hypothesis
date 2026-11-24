module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.DixmierSchurOfRankLeAleph0
public import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolActs
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Nontrivial.Defs
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.LinearAlgebra.Dimension.Basic
public import Mathlib.Order.Notation
public import Mathlib.SetTheory.Cardinal.Defs
public import Mathlib.SetTheory.Cardinal.Order

@[expose] public section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_smul_one_of_commute_irreducible_of_countable_rank : ∀ (V ι : Type) [AddCommGroup V] [Module ℂ V] (ρ : ι → Module.End ℂ V) (T : Module.End ℂ V), Nontrivial V → Module.rank ℂ V ≤ Cardinal.aleph0 →
    (∀ N : Submodule ℂ V, (∀ i, ∀ x ∈ N, ρ i x ∈ N) → N = ⊥ ∨ N = ⊤) → (∀ i, T * ρ i = ρ i * T) → ∃ c : ℂ, T = c • 1 := by
  first | exact @GlobalTheory.dixmier_schur_of_rank_le_aleph0 | exact GlobalTheory.dixmier_schur_of_rank_le_aleph0 | (intros; apply GlobalTheory.dixmier_schur_of_rank_le_aleph0 <;> assumption)
