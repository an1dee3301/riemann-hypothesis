module

public import Mathlib
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.HypJ
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.RationalGramAdelicCompactFiniteStatement
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CompactPartClosedOrbit
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelesLocallyCompactSecondCountable
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRing
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicUnitaryGroupLocallyCompactStatement
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.WittExtensionRationalToAdelicStatement
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Finsupp.SMul
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Free
public import Mathlib.RingTheory.Trace.Defs
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Compactness.LocallyCompact
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.Separation.Hausdorff

@[expose] public section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.Proper

theorem compact_gram_fibre :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
      IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
      ∀ (n : ℕ) (X : Fin n → Fin M → E), (gramE σ J X).det ≠ 0 →
      ∀ Ω : Set (Fin n → Fin M → AF F ⊗[F] E), IsCompact Ω →
      ∃ C : Set (HA (AF F) σ J), IsCompact C ∧
        ∀ Y ∈ Ω, gramR (AF F) σ J Y = (gramE σ J X).map (inclR (AF F)) →
          ∃ c ∈ C, actW (AF F) σ J c (ratTup (AF F) X) = Y := by
  intro F E _ _ _ _ _ σ hσ M J hJ n X hX Ω hΩ
  obtain ⟨⟨hlc, hsc, ht2⟩, -⟩ := GlobalTheory.CompanionTheory.AdeleTop.adele_top F
  haveI := hlc
  haveI := hsc
  haveI := ht2
  obtain ⟨htg, hlcH, hscH, ht2H, -, hact⟩ := GlobalTheory.T.adelic_unitary_group_locally_compact F E σ hσ M J hJ (AF F)
  haveI := htg
  haveI := hlcH
  haveI := hscH
  haveI := ht2H
  obtain ⟨-, hlcK, -, ht2K, -, -, -, -, -, hgram⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hσ (AF F)
  haveI := hlcK
  haveI := ht2K
  obtain ⟨hcont, h1, hmul, hinv⟩ := hact n
  obtain ⟨-, hrat, -⟩ := GlobalTheory.T.rational_gram_adelic_compact_finite F E σ hσ M J hJ
  have hZ : IsClosed {Y : Fin n → Fin M → AF F ⊗[F] E |
      gramR (AF F) σ J Y = (gramE σ J X).map (inclR (AF F))} :=
    isClosed_eq (hgram n M J) continuous_const
  have hZx : ∀ Y : Fin n → Fin M → AF F ⊗[F] E,
      Y ∈ {Y : Fin n → Fin M → AF F ⊗[F] E |
        gramR (AF F) σ J Y = (gramE σ J X).map (inclR (AF F))} ↔
      ∃ g : HA (AF F) σ J, actW (AF F) σ J g (ratTup (AF F) X) = Y := by
    intro Y
    constructor
    · intro hY
      exact GlobalTheory.T.witt_extension_rational_to_adelic F E σ hσ M J hJ n X Y hX hY
    · rintro ⟨g, rfl⟩
      show gramR (AF F) σ J _ = _
      rw [hinv, hrat]
  obtain ⟨C, hC, hCY⟩ := GlobalTheory.CompanionTheory.Adelic.compact_part_closed_orbit (HA (AF F) σ J)
    (Fin n → Fin M → AF F ⊗[F] E) (fun g Y => actW (AF F) σ J g Y) hcont h1 hmul _
    (ratTup (AF F) X) hZ hZx Ω hΩ
  exact ⟨C, hC, fun Y hY hg => hCY Y hY hg⟩

end GlobalTheory.CompanionTheory.SW.Proper
