module

public import Mathlib
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdeleRingCocompactDiscreteNumberField
public import Init.Core
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Topology.Defs.Filter

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adele_ring_cocompact_discrete_number_field : ∀ (F : Type) [Field F] [NumberField F], (∃ C : Set (AdeleRing (𝓞 F) F), IsCompact C ∧ ∀ y, ∃ l : F, y - algebraMap F (AdeleRing (𝓞 F) F) l ∈ C) ∧ (∀ C : Set (AdeleRing (𝓞 F) F), IsCompact C → {l : F | algebraMap F (AdeleRing (𝓞 F) F) l ∈ C}.Finite) ∧ NoncompactSpace (AdeleRing (𝓞 F) F) := by
  first | exact @GlobalTheory.CompanionTheory.Adelic.FieldCocompact.discrete_cocompact | exact GlobalTheory.CompanionTheory.Adelic.FieldCocompact.discrete_cocompact | (intros; apply GlobalTheory.CompanionTheory.Adelic.FieldCocompact.discrete_cocompact <;> assumption)
