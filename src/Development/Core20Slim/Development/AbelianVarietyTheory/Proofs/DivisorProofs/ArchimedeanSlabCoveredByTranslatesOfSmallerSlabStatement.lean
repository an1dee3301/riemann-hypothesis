module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanSlabCoveredByTranslatesOfSmallerSlab
public import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.WordAppend
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousMixedSymm
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Notation.Prod
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix ENNReal
open scoped Classical
open GlobalTheory.ArchDecay

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedeanSlab_covered_by_translates_of_smaller_slab : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ], ∃ c : ℕ, ∀ m : ℕ, 0 < m → slab F κ m ⊆ slab F κ 1 ∧ ∃ R : Finset (κ → AF F), R.card ≤ m ^ c ∧ (∀ r ∈ R, arch F r = 0) ∧ ∀ w ∈ slab F κ 1, ∃ r ∈ R, w - r ∈ slab F κ m := by
  first | exact @GlobalTheory.ArchDecay.slab_subset_and_cover | exact GlobalTheory.ArchDecay.slab_subset_and_cover | (intros; apply GlobalTheory.ArchDecay.slab_subset_and_cover <;> assumption)
