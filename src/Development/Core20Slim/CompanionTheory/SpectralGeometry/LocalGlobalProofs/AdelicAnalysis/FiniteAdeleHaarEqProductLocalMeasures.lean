module

public import Mathlib
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.FiniteAdeleHaarPiRestrictedProduct
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CompletionIsLocalRing
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRing
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelesLocallyCompactSecondCountable
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SiegelWeilMeasureOfCongruentTarget
public import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.PropLemmas
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.NonUnitalHom
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Group.WithOne.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Countable.Basic
public import Mathlib.Basic.Countable.Defs
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Logic.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Finsupp.SMul
public import Mathlib.Data.Finsupp.SMulWithZero
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Prod.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.MeasurableSpace.Embedding
public import Mathlib.MeasureTheory.Measure.Comap
public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Mathlib.RingTheory.Artinian.Defs
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Free
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.RingTheory.Trace.Defs
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Algebra.Nonarchimedean.Basic
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.Valued.NormedValued
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Compactness.LocallyCompact
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.WBox

section Gen

variable {F E : Type} [Field F] [Field E] [Algebra F E]

def cK (R : Type) [CommRing R] [Algebra F R] {d : ℕ} (b : Module.Basis (Fin d) F E) (y : R ⊗[F] E)
    (k : Fin d) : R :=
  (Algebra.TensorProduct.basis R b).repr y k

theorem cK_map {R R' : Type} [CommRing R] [Algebra F R] [CommRing R'] [Algebra F R'] {d : ℕ}
    (b : Module.Basis (Fin d) F E) (f : R →ₐ[F] R') (y : R ⊗[F] E) (k : Fin d) :
    cK R' b (Algebra.TensorProduct.map f (AlgHom.id F E) y) k = f (cK R b y k) := by
  induction y with
  | add x y hx hy =>
    simp only [cK] at hx hy ⊢
    simp [map_add (f := _), hx, hy]
  | tmul r e =>
    simp [cK, Algebra.TensorProduct.basis_repr_tmul, Algebra.smul_def]

variable (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [SecondCountableTopology R]
  [MeasurableSpace R] [BorelSpace R] {d : ℕ} {b : Module.Basis (Fin d) F E}

def eK (hK : IsHomeomorph (cK (F := F) (E := E) R b)) : (R ⊗[F] E) ≃ᵐ (Fin d → R) :=
  haveI : BorelSpace (R ⊗[F] E) := ⟨rfl⟩
  (hK.homeomorph _).toMeasurableEquiv

def eW (hK : IsHomeomorph (cK (F := F) (E := E) R b)) (n M : ℕ) :
    (Fin n → Fin M → R ⊗[F] E) ≃ᵐ (Fin n × Fin M × Fin d → R) where
  toFun X p := eK R hK (X p.1 p.2.1) p.2.2
  invFun Y a i := (eK R hK).symm fun k => Y (a, i, k)
  left_inv X := by
    funext a i
    simp
  right_inv Y := by
    funext p
    simp
  measurable_toFun := Measurable.of_eval fun p =>
    (measurable_pi_apply p.2.2).comp ((eK R hK).measurable.comp
      ((measurable_pi_apply p.2.1).comp (measurable_pi_apply p.1)))
  measurable_invFun := Measurable.of_eval fun a => Measurable.of_eval fun i =>
    (eK R hK).symm.measurable.comp (Measurable.of_eval fun k => measurable_pi_apply (a, i, k))

theorem eW_apply (hK : IsHomeomorph (cK (F := F) (E := E) R b)) (n M : ℕ)
    (X : Fin n → Fin M → R ⊗[F] E) (p : Fin n × Fin M × Fin d) :
    eW R hK n M X p = cK R b (X p.1 p.2.1) p.2.2 := rfl

theorem coordK_eq (hK : IsHomeomorph (cK (F := F) (E := E) R b)) (lam : Measure R) :
    coordK R b lam = (Measure.pi fun _ : Fin d => lam).map (eK R hK).symm := by
  rw [MeasurableEquiv.map_symm]
  rfl

theorem sigmaFinite_coordK (hK : IsHomeomorph (cK (F := F) (E := E) R b)) (lam : Measure R)
    [SigmaFinite lam] : SigmaFinite (coordK R b lam) := by
  rw [coordK_eq R hK lam]
  exact (eK R hK).symm.measurableEmbedding.sigmaFinite_map

theorem map_coordW (hK : IsHomeomorph (cK (F := F) (E := E) R b)) (lam : Measure R) [SigmaFinite lam]
    (n M : ℕ) :
    MeasurePreserving (eW R hK n M) (coordW R b lam n M)
      (Measure.pi fun _ : Fin n × Fin M × Fin d => lam) := by
  haveI := sigmaFinite_coordK R hK lam
  refine ⟨(eW R hK n M).measurable, ?_⟩
  symm
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.map_apply (eW R hK n M).measurable (MeasurableSet.univ_pi hs)]
  have hset : (eW R hK n M) ⁻¹' Set.pi Set.univ s =
      Set.pi Set.univ fun a => Set.pi Set.univ fun i =>
        (eK R hK) ⁻¹' Set.pi Set.univ fun k => s (a, i, k) := by
    ext X
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_true_left]
    exact ⟨fun h a i k => h (a, i, k), fun h p => h p.1 p.2.1 p.2.2⟩
  have hK1 : ∀ t : Fin d → Set R, (∀ k, MeasurableSet (t k)) →
      coordK R b lam ((eK R hK) ⁻¹' Set.pi Set.univ t) = ∏ k, lam (t k) := by
    intro t ht
    rw [coordK_eq R hK lam, Measure.map_apply (eK R hK).symm.measurable
      ((eK R hK).measurable (MeasurableSet.univ_pi ht))]
    have : (eK R hK).symm ⁻¹' ((eK R hK) ⁻¹' Set.pi Set.univ t) = Set.pi Set.univ t := by
      ext x
      simp
    rw [this, Measure.pi_pi]
  rw [hset, coordW, Measure.pi_pi]
  simp_rw [Measure.pi_pi]
  simp_rw [hK1 _ (fun k => hs _)]
  rw [Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [Fintype.prod_prod_type]

end Gen

theorem coordW_box : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)), (∀ v, IsStdV v (lam v)) → ∀ (lf : Measure (Af F)), lf.IsAddHaarMeasure → lf {x | ∀ v, x v ∈ v.adicCompletionIntegers F} = 1 → ∀ (n M : ℕ) (S : Finset (HeightOneSpectrum (𝓞 F))) (A : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin n → Fin M → Fv F v ⊗[F] E)), (∀ v, MeasurableSet (A v)) → coordW (Af F) b lf n M {X | (∀ v ∈ S, projV v X ∈ A v) ∧ ∀ v, v ∉ S → projV v X ∈ latV b v} = ∏ v ∈ S, coordW (Fv F v) b (lam v) n M (A v) := by
  intro F E _ _ _ _ _ σ hσ d b lam hlam lf hlf h1 n M S A hA
  obtain ⟨-, hAfLC, hAfSC, hAfT2⟩ := GlobalTheory.CompanionTheory.AdeleTop.adele_top F
  have hloc := fun v => GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v
  haveI : ∀ v, IsTopologicalRing (Fv F v) := fun v => (hloc v).1
  haveI : ∀ v, LocallyCompactSpace (Fv F v) := fun v => (hloc v).2.1
  haveI : ∀ v, SecondCountableTopology (Fv F v) := fun v => (hloc v).2.2.1
  haveI : ∀ v, T2Space (Fv F v) := fun v => (hloc v).2.2.2.1
  haveI : ∀ v, BorelSpace (Fv F v) := fun v => ⟨rfl⟩
  haveI : ∀ v, (lam v).IsAddHaarMeasure := fun v => (hlam v).1
  haveI : BorelSpace (Af F) := ⟨rfl⟩
  have hKf : IsHomeomorph (cK (F := F) (E := E) (Af F) b) :=
    (GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hσ (Af F)).2.2.2.2.2.2.1 d b
  have hKv : ∀ v, IsHomeomorph (cK (F := F) (E := E) (Fv F v) b) := fun v =>
    (GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hσ (Fv F v)).2.2.2.2.2.2.1 d b
  have mf := map_coordW (Af F) hKf lf n M
  have mv := fun v => map_coordW (Fv F v) (hKv v) (lam v) n M
  let A' : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin n × Fin M × Fin d → Fv F v) := fun v =>
    (eW (Fv F v) (hKv v) n M).symm ⁻¹' A v
  have hA' : ∀ v, MeasurableSet (A' v) := fun v => (eW (Fv F v) (hKv v) n M).symm.measurable (hA v)
  have hcomm : ∀ (v : HeightOneSpectrum (𝓞 F)) (X : Fin n → Fin M → Af F ⊗[F] E)
      (p : Fin n × Fin M × Fin d),
      evalV F v (eW (Af F) hKf n M X p) = eW (Fv F v) (hKv v) n M (projV v X) p := by
    intro v X p
    rw [eW_apply, eW_apply, projV, cK_map]
  have hset : {X : Fin n → Fin M → Af F ⊗[F] E | (∀ v ∈ S, projV v X ∈ A v) ∧
      ∀ v, v ∉ S → projV v X ∈ latV b v} =
      (eW (Af F) hKf n M) ⁻¹' {x | (∀ v ∈ S, (fun i => evalV F v (x i)) ∈ A' v) ∧
        ∀ v, v ∉ S → ∀ i, evalV F v (x i) ∈ v.adicCompletionIntegers F} := by
    ext X
    simp only [Set.mem_setOf_eq, Set.mem_preimage, hcomm]
    refine and_congr (forall₂_congr fun v _ => ?_) (forall₂_congr fun v _ => ?_)
    · simp [A']
    · exact ⟨fun h p => h p.1 p.2.1 p.2.2, fun h a i k => h (a, i, k)⟩
  rw [hset, mf.measure_preimage_equiv,
    GlobalTheory.CompanionTheory.SW.AfBox.pi_box F lam hlam lf hlf h1 (Fin n × Fin M × Fin d) S A' hA']
  exact Finset.prod_congr rfl fun v _ => (mv v).symm.measure_preimage_equiv (A v)

end GlobalTheory.CompanionTheory.SW.WBox
