module

public import Mathlib
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.HypJ
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ArithmeticUnitaryGroupDiscrete
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelesLocallyCompactSecondCountable
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicUnitaryGroupLocallyCompactStatement
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsStrictMeasurableFundamentalSetOfDiscrete
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import Init.Core
public import Init.Data.NeZero
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Torsor.Defs
public import Mathlib.Basic.Countable.Defs
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.ExistsUnique
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Nonempty
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Group.Defs
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.Haar.Basic
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Module
public import Mathlib.MeasureTheory.Measure.NullMeasurable
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Filter.Defs
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.Sets.Compacts

@[expose] public section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW

theorem haar_fundamental_exist : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → (∃ μ, IsHaarH F E σ M J μ) ∧ ∀ μ, IsHaarH F E σ M J μ → (∃ 𝓕, IsFDH F E σ M J μ 𝓕) ∧ (∃ 𝓕, MeasurableSet 𝓕 ∧ IsFDH F E σ M J μ 𝓕 ∧ ∀ h : HA (AF F) σ J, ∃ γ : HA (AF F) σ J, HA.mat (AF F) σ J γ ∈ HFin (AF F) σ J ∧ γ * h ∈ 𝓕) ∧ ∀ 𝓕, IsFDH F E σ M J μ 𝓕 → μ 𝓕 ≠ 0 := by
  intro F E _ _ _ _ _ σ hσ M J hJ
  obtain ⟨⟨hlc, hsc, ht2⟩, -⟩ := GlobalTheory.CompanionTheory.AdeleTop.adele_top F
  haveI := hlc
  haveI := hsc
  haveI := ht2
  obtain ⟨htg, hlcH, hscH, ht2H, hbH, -⟩ := GlobalTheory.T.adelic_unitary_group_locally_compact F E σ hσ M J hJ (AF F)
  haveI := htg
  haveI := hlcH
  haveI := hscH
  haveI := ht2H
  haveI := hbH
  obtain ⟨hcount, U, hU, hUd⟩ := rational_countable_discrete F E σ hσ M J hJ
  haveI := hcount
  let Γ : Subgroup (HA (AF F) σ J) := HFinIn (AF F) σ J
  have hmem : ∀ γ : HA (AF F) σ J, γ ∈ Γ → HA.mat (AF F) σ J γ ∈ HFin (AF F) σ J :=
    fun γ hγ => Subgroup.mem_subgroupOf.1 hγ
  obtain ⟨-, D, hD, hDs⟩ := GlobalTheory.exists_strict_measurable_fundamental_set_of_discrete
    (HA (AF F) σ J) Γ ⟨U, hU, fun γ hγ hγU => hUd γ hγU (hmem γ hγ)⟩
  have hfd : ∀ μ : Measure (HA (AF F) σ J), IsFDH F E σ M J μ D := fun μ =>
    IsFundamentalDomain.mk' hD.nullMeasurableSet hDs
  refine ⟨⟨Measure.haar, inferInstanceAs (Measure.IsHaarMeasure _)⟩, fun μ hμ => ?_⟩
  haveI : μ.IsHaarMeasure := hμ
  refine ⟨⟨D, hfd μ⟩, ⟨D, hD, hfd μ, fun h => ?_⟩, fun 𝓕 h𝓕 => ?_⟩
  · obtain ⟨γ, hγ, -⟩ := hDs h
    exact ⟨γ, hmem _ γ.2, hγ⟩
  · haveI : MeasurableConstSMul (HFinIn (AF F) σ J) (HA (AF F) σ J) :=
      ⟨fun c => (continuous_const.mul continuous_id :
        Continuous fun x : HA (AF F) σ J => (show HA (AF F) σ J from c.1) * x).measurable⟩
    haveI : SMulInvariantMeasure (HFinIn (AF F) σ J) (HA (AF F) σ J) μ :=
      ⟨fun c s hs => measure_preimage_mul μ (show HA (AF F) σ J from c.1) s⟩
    have h𝓕' : IsFundamentalDomain (HFinIn (AF F) σ J) 𝓕 μ := h𝓕
    exact h𝓕'.measure_ne_zero (NeZero.ne μ)

end GlobalTheory.CompanionTheory.SW
