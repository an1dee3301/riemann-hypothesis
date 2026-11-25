module

public import Mathlib
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EMatMulNegCol
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.GlobalProofs.FibreMassEq
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CompletionIsLocalRing
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRing
public import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import Init.Classical
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Insert
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Finsupp.SMul
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Sets
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.CoeSort
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Image
public import Mathlib.Data.Set.Insert
public import Mathlib.Data.Set.Lattice.Indexed
public import Mathlib.Data.Set.Operations
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.SetNotation
public import Mathlib.RingTheory.Artinian.Defs
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Free
public import Mathlib.RingTheory.Trace.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.OpenSubgroup
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open scoped Matrix NNReal ENNReal TensorProduct
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.WhitFree GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.AvgFree MeasureTheory

namespace GlobalTheory.CompanionTheory.AvgFree

theorem exists_lattice_of_compact {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
    (O : Subring K) (hOc : IsCompact (O : Set K)) (hOo : IsOpen (O : Set K)) {C : Set K} (hC : IsCompact C) :
    ∃ L : Submodule O K, IsCompact (L : Set K) ∧ IsOpen (L : Set K) ∧ C ⊆ (L : Set K) := by
  classical
  obtain ⟨t, ht⟩ := hC.elim_finite_subcover (fun x : K => (fun y => y - x) ⁻¹' (O : Set K))
    (fun x => hOo.preimage (continuous_id.sub continuous_const))
    (fun x _ => Set.mem_iUnion.2 ⟨x, by simpa using O.zero_mem⟩)
  let s : Finset K := insert 1 t
  let L : Submodule O K := Submodule.span O (s : Set K)
  have h1 : (1 : K) ∈ L := Submodule.subset_span (by simp [s])
  have hO : ∀ a ∈ O, a ∈ L := fun a ha => by
    have := L.smul_mem (⟨a, ha⟩ : O) h1
    simpa [Subring.smul_def] using this
  refine ⟨L, ?_, ?_, ?_⟩
  · haveI : CompactSpace O := isCompact_iff_compactSpace.1 hOc
    have hr : (L : Set K) = Set.range (fun c : s → O => ∑ i, (c i : K) * (i : K)) := by
      ext x
      have hs : (s : Set K) = Set.range (Subtype.val : s → K) := by simp
      change x ∈ Submodule.span O (s : Set K) ↔ _
      rw [hs, Submodule.mem_span_range_iff_exists_fun]
      rfl
    rw [hr]
    refine isCompact_range ?_
    fun_prop
  · have hopen : IsOpen ((L.toAddSubgroup : AddSubgroup K) : Set K) := by
      refine AddSubgroup.isOpen_mono (H₁ := O.toAddSubgroup) (fun a ha => hO a ha) hOo
    exact hopen
  · intro x hx
    obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.1 (ht hx)
    have hyL : y ∈ L := Submodule.subset_span (by simp [s, hy])
    have : x = (x - y) + y := by ring
    rw [this]
    exact L.add_mem (hO _ hxy) hyL

end GlobalTheory.CompanionTheory.AvgFree

theorem GlobalTheory.CompanionTheory.AvgFree.exists_lattice_tupIn : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) (O : Subring (Fv F v ⊗[F] E)), IsCompact (O : Set (Fv F v ⊗[F] E)) → IsOpen (O : Set (Fv F v ⊗[F] E)) → ∀ (n M : ℕ) (A : Set (Fin n → Fin M → (Fv F v ⊗[F] E))), IsCompact A → ∃ L : Submodule O (Fv F v ⊗[F] E), IsCompact (L : Set (Fv F v ⊗[F] E)) ∧ IsOpen (L : Set (Fv F v ⊗[F] E)) ∧ A ⊆ tupIn (Fv F v) (L : Set (Fv F v ⊗[F] E)) := by
  intro F E _ _ _ _ _ σ hσ v O hOc hOo n M A hA
  obtain ⟨r1, r2, r3, r4, -⟩ := GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v
  haveI := r1
  haveI := r2
  haveI := r3
  haveI := r4
  obtain ⟨a1, -⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hσ (Fv F v)
  haveI := a1
  have hC : IsCompact (⋃ i : Fin n, ⋃ k : Fin M, (fun X : Fin n → Fin M → Fv F v ⊗[F] E => X i k) '' A) :=
    isCompact_iUnion fun i => isCompact_iUnion fun k => hA.image (by fun_prop)
  obtain ⟨L, h1, h2, h3⟩ := exists_lattice_of_compact O hOc hOo hC
  refine ⟨L, h1, h2, fun X hX i k => h3 ?_⟩
  exact Set.mem_iUnion₂.2 ⟨i, k, X, hX, rfl⟩
