module

public import Mathlib
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement
public import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import Init.Core
public import Init.Data.Fin.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Prod
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.Countable.Basic
public import Mathlib.Basic.Countable.Defs
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Basic.Unique
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Finsupp.SMul
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Image
public import Mathlib.Data.Set.Operations
public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.MeasurableSpace.Embedding
public import Mathlib.MeasureTheory.Measure.Comap
public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Free
public import Mathlib.RingTheory.Trace.Defs
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Compactness.LocallyCompact
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.Separation.Hausdorff

@[expose] public section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW

theorem map_curry_pi_pi {R : Type} [MeasurableSpace R] (lam : Measure R) [SigmaFinite lam] (M d : ℕ) :
    (Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin d => lam).map
      (fun (Y : Fin M → Fin d → R) (p : Fin M × Fin d) => Y p.1 p.2) =
      Measure.pi fun _ : Fin M × Fin d => lam := by
  have hm : Measurable (fun (Y : Fin M → Fin d → R) (p : Fin M × Fin d) => Y p.1 p.2) := by
    fun_prop
  symm
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.map_apply hm (MeasurableSet.univ_pi hs)]
  have hpre : (fun (Y : Fin M → Fin d → R) (p : Fin M × Fin d) => Y p.1 p.2) ⁻¹' Set.univ.pi s =
      Set.univ.pi fun i : Fin M => Set.univ.pi fun k : Fin d => s (i, k) := by
    ext Y
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_imp_iff, Prod.forall]
  rw [hpre, Measure.pi_pi]
  simp only [Measure.pi_pi]
  rw [Fintype.prod_prod_type]

theorem coordW_one_map_coords : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R] [SecondCountableTopology R] [T2Space R] [MeasurableSpace R] [BorelSpace R], ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∀ (M : ℕ) (lam : Measure R), lam.IsAddHaarMeasure → (Measurable fun (X : Fin 1 → Fin M → R ⊗[F] E) (p : Fin M × Fin d) => (Algebra.TensorProduct.basis R b).repr (X 0 p.1) p.2) ∧ (coordW R b lam 1 M).map (fun X (p : Fin M × Fin d) => (Algebra.TensorProduct.basis R b).repr (X 0 p.1) p.2) = Measure.pi fun _ => lam := by
  intro F E _ _ _ _ _ σ hσ R _ _ _ _ _ _ _ _ _ d b M lam hlam
  obtain ⟨-, -, -, -, -, -, hom, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hσ R
  have : BorelSpace (R ⊗[F] E) := ⟨rfl⟩
  have hh := hom d b
  let e : (R ⊗[F] E) ≃ᵐ (Fin d → R) := (hh.homeomorph _).toMeasurableEquiv
  have hce : (⇑e : (R ⊗[F] E) → Fin d → R) =
      fun y k => (Algebra.TensorProduct.basis R b).repr y k := rfl
  have hK : (coordK R b lam).map e = Measure.pi fun _ => lam := by
    have h := e.measurableEmbedding.map_comap (Measure.pi fun _ : Fin d => lam)
    rw [e.surjective.range_eq, Measure.restrict_univ] at h
    rw [coordK, ← hce]
    exact h
  have hK' : coordK R b lam = (Measure.pi fun _ : Fin d => lam).map e.symm := by
    rw [← hK, Measure.map_map e.symm.measurable e.measurable]
    simp
  have : SigmaFinite (coordK R b lam) := by
    rw [hK']; exact e.symm.sigmaFinite_map
  have hmpK : MeasurePreserving e (coordK R b lam) (Measure.pi fun _ : Fin d => lam) :=
    ⟨e.measurable, hK⟩
  have h1 : MeasurePreserving (fun (X : Fin 1 → Fin M → R ⊗[F] E) => X default)
      (coordW R b lam 1 M) (Measure.pi fun _ : Fin M => coordK R b lam) :=
    measurePreserving_funUnique (Measure.pi fun _ : Fin M => coordK R b lam) (Fin 1)
  have h2 : MeasurePreserving (fun (Y : Fin M → R ⊗[F] E) (i : Fin M) => e (Y i))
      (Measure.pi fun _ : Fin M => coordK R b lam)
      (Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin d => lam) :=
    measurePreserving_pi _ _ fun _ => hmpK
  have h3 : MeasurePreserving (fun (Y : Fin M → Fin d → R) (p : Fin M × Fin d) => Y p.1 p.2)
      (Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin d => lam)
      (Measure.pi fun _ : Fin M × Fin d => lam) :=
    ⟨by fun_prop, map_curry_pi_pi lam M d⟩
  have h := h3.comp (h2.comp h1)
  exact ⟨h.measurable, h.map_eq⟩

end GlobalTheory.CompanionTheory.SW
