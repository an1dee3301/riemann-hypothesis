module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatHeckeCharacterTrivialCongruentUnits
public import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterIdeleCharacterMatchUnique
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterUnramifiedAeAndExistsLevel
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdeleCharacterTrivialOnLocalUnits
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
public import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Hom.Instances
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Group.WithOne.Defs
public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Order.Monoid.Unbundled.TypeTags
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.WithAbs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Valuation
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Valuation.Basic
public import Mathlib.Topology.Algebra.Valued.ValuationTopology
public import Mathlib.Topology.Algebra.Valued.WithVal
public import Mathlib.Topology.UniformSpace.Completion
public import ReciprocityTheory.NeutralLocalFields.Reciprocity

@[expose] public section

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nat_heckeCharacter_trivial_congruent_units : ∀ (L : Type) [Field L] [NumberField L] (χ : Formalism.L2.Host.HChar L), ∃ M : ℕ, 0 < M ∧ ∀ a : Neutral.B1.Ideles L, a ∈ GlobalTheory.Mem.Chr.unitIdl L → (∀ w, (a : AdeleRing (𝓞 L) L).1 w = 1) → (∀ P : HeightOneSpectrum (𝓞 L), Valued.v ((a : AdeleRing (𝓞 L) L).2 P - 1) ≤ Valued.v ((M : L) : P.adicCompletion L)) → χ.1 a = 1 := by
  first | exact @GlobalTheory.Mem.HeckeLevel.exists_level_nat | exact GlobalTheory.Mem.HeckeLevel.exists_level_nat | (intros; apply GlobalTheory.Mem.HeckeLevel.exists_level_nat <;> assumption)
