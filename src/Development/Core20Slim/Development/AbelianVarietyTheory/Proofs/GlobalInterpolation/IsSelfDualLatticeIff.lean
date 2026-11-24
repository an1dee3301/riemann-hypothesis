module

public import Mathlib
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FibOfZero
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SelfDualUnramifiedPlaces
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.DualExponentDensity
public import Init.Data.Int.Basic
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Group.WithOne.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Countable.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Finite
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.Valued.NormedValued
public import Mathlib.Topology.Algebra.Valued.ValuedField
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Compactness.LocallyCompact
public import Mathlib.Topology.Connected.Separation
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.EMetricSpace.Defs
public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.UniformSpace.Cauchy
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

noncomputable section
namespace GlobalTheory.LocalDensityCompare

section Top
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))

@[reducible] def nontrivNormed : NontriviallyNormedField (Fv F v) :=
  { (inferInstance : NormedField (Fv F v)) with
    non_trivial := by
      obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
      have h1 := (NumberField.FinitePlace.norm_lt_one_iff_mem F v x).2 hx
      have h0 : NumberField.FinitePlace.embedding v (algebraMap (𝓞 F) F x) ≠ 0 := by
        rw [map_ne_zero]
        exact RingOfIntegers.coe_ne_zero_iff.2 hx0
      refine ⟨(NumberField.FinitePlace.embedding v (algebraMap (𝓞 F) F x))⁻¹, ?_⟩
      rw [norm_inv]
      exact (one_lt_inv₀ (norm_pos_iff.2 h0)).2 h1 }

theorem modTop : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩
theorem topRing : IsTopologicalRing (Fv F v ⊗[F] E) :=
  haveI := modTop (E := E) v
  IsModuleTopology.isTopologicalRing (Fv F v) _
theorem lcs : LocallyCompactSpace (Fv F v ⊗[F] E) ∧ SecondCountableTopology (Fv F v ⊗[F] E) ∧
    T2Space (Fv F v ⊗[F] E) := by
  haveI := GlobalTheory.AdelicUnitaryTop.properSpace_adicCompletion F v
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (Fv F v)
  exact ⟨e.isClosedEmbedding.locallyCompactSpace, e.secondCountableTopology, e.isEmbedding.t2Space⟩

variable (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)





end Top

section Dict
variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))




variable {F E}





end Dict



end GlobalTheory.LocalDensityCompare
