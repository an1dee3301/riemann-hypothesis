module

public import Mathlib
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsUnitHermOfDet
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoordForm
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.GlobalProofs.ArchimedeanHaarScalingNorm
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.GlobalProofs.ExistsAdelicHaarCovolumeOne
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.SelfDualMap
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualProdIff
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CoordinateHaarMeasure
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import Init.Core
public import Init.Data.Prod
public import Init.Data.Sum.Basic
public import Init.Data.Sum.Lemmas
public import Init.Data.Zero
public import Init.Prelude
public import Init.PropLemmas
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Countable.Basic
public import Mathlib.Basic.Countable.Defs
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Logic.Basic
public import Mathlib.Basic.SProd
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Countable
public import Mathlib.CategoryTheory.FinCategory.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Finsupp.SMul
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Sets
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Dimension.Finrank
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
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Fin.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Free
public import Mathlib.RingTheory.Trace.Defs
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Compactness.LocallyCompact
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.Separation.Hausdorff

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.SiegelND.Coef GlobalTheory.CompanionTheory.SiegelND.Coef.TestN
open scoped TensorProduct ENNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Coef.TestN.CoordMeas

theorem map_comp_comap {H Y Z : Type} [MeasurableSpace H] [MeasurableSpace Y] [MeasurableSpace Z]
    (e : H ≃ᵐ Y) (ν : Measure Y) {c : Y → Z} (hc : Measurable c) :
    (Measure.comap e ν).map (c ∘ e) = ν.map c := by
  rw [← MeasurableEquiv.map_symm, ← Measure.map_map hc e.measurable,
    Measure.map_map e.measurable e.symm.measurable]
  have : (⇑e ∘ ⇑e.symm) = id := funext e.apply_symm_apply
  rw [this, Measure.map_id]

theorem map_prod_box {R K P : Type} [MeasurableSpace R] [MeasurableSpace K] [Fintype P] {n d : ℕ}
    (lam : Measure R) [SigmaFinite lam] (κ : Measure K) [SigmaFinite κ] (r : K → Fin d → R)
    (hr : Measurable r) (hκ : κ.map r = Measure.pi fun _ => lam) :
    ((Measure.pi fun _ : Fin n => lam).prod (Measure.pi fun _ : P => κ)).map
        (fun x : (Fin n → R) × (P → K) =>
          (Sum.elim x.1 (fun q : Fin d × P => r (x.2 q.2) q.1) : Fin n ⊕ (Fin d × P) → R)) =
      Measure.pi fun _ : Fin n ⊕ (Fin d × P) => lam := by
  have hc : Measurable (fun x : (Fin n → R) × (P → K) =>
      (Sum.elim x.1 (fun q : Fin d × P => r (x.2 q.2) q.1) : Fin n ⊕ (Fin d × P) → R)) := by
    refine measurable_pi_iff.2 fun i => ?_
    rcases i with i | q
    · exact (measurable_pi_apply i).comp measurable_fst
    · exact (measurable_pi_apply q.1).comp
        (hr.comp ((measurable_pi_apply q.2).comp measurable_snd))
  symm
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.map_apply hc (MeasurableSet.univ_pi hs)]
  have hset : (fun x : (Fin n → R) × (P → K) =>
      (Sum.elim x.1 (fun q : Fin d × P => r (x.2 q.2) q.1) : Fin n ⊕ (Fin d × P) → R)) ⁻¹'
        Set.pi Set.univ s =
      (Set.pi Set.univ fun i : Fin n => s (Sum.inl i)) ×ˢ
        (Set.pi Set.univ fun p : P => r ⁻¹' Set.pi Set.univ fun k : Fin d => s (Sum.inr (k, p))) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_true_left, Set.mem_prod,
      Sum.forall, Sum.elim_inl, Sum.elim_inr, Prod.forall]
    exact and_congr Iff.rfl ⟨fun h p k => h k p, fun h k p => h p k⟩
  have hκs : ∀ p : P, κ (r ⁻¹' Set.pi Set.univ fun k : Fin d => s (Sum.inr (k, p))) =
      ∏ k : Fin d, lam (s (Sum.inr (k, p))) := fun p => by
    rw [← Measure.map_apply hr (MeasurableSet.univ_pi fun k => hs _), hκ, Measure.pi_pi]
  rw [hset, Measure.prod_prod, Measure.pi_pi, Measure.pi_pi, Fintype.prod_sum_type,
    Fintype.prod_prod_type]
  simp only [hκs]
  rw [Finset.prod_comm]

end GlobalTheory.CompanionTheory.SiegelND.Coef.TestN.CoordMeas

namespace GlobalTheory.CompanionTheory.SiegelND.Coef.TestN

open GlobalTheory.CompanionTheory.SiegelND.Coef.TestN.CoordMeas

theorem coordHerm_map_hCo : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R] [SecondCountableTopology R] [T2Space R] [MeasurableSpace R] [BorelSpace R] (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R), lam.IsAddHaarMeasure → ∀ n : ℕ, (GlobalTheory.CompanionTheory.SW.coordHerm R σ b lam n).map (hCo R σ b) = Measure.pi fun _ : Idx n d => lam := by
  intro F E _ _ _ _ _ σ hcm R _ _ _ _ _ _ _ _ _ d b lam hlam n
  obtain ⟨t1, t2, t3, t4, t5, t6, t7, -, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hcm R
  have h2 : Module.finrank F E = 2 := hcm.2.2.1
  obtain ⟨hinv, δ, hδ, hσδ⟩ := GlobalTheory.CompanionTheory.SW.HaarCoord.conj_facts hcm
  haveI : BorelSpace (R ⊗[F] E) := ⟨rfl⟩
  haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  haveI : ContinuousSMul R (R ⊗[F] E) := IsModuleTopology.toContinuousSMul R _
  haveI : BorelSpace (HeckeCharacterZeroLocus.SiegelWeilU.HermR R σ n) := ⟨rfl⟩
  obtain ⟨hK, -, -⟩ := GlobalTheory.CompanionTheory.SW.coord_measures_haar F E σ hcm R d b lam hlam
  haveI : SigmaFinite (GlobalTheory.CompanionTheory.SW.coordK R b lam) := inferInstance

  let r : R ⊗[F] E → Fin d → R := fun y k => (Algebra.TensorProduct.basis R b).repr y k
  let Tr : (R ⊗[F] E) ≃ₜ (Fin d → R) := (t7 d b).homeomorph r
  have hr : Measurable r := Tr.toMeasurableEquiv.measurable
  have hκ : (GlobalTheory.CompanionTheory.SW.coordK R b lam).map r = Measure.pi fun _ => lam := by
    have := map_comp_comap Tr.toMeasurableEquiv (Measure.pi fun _ => lam) (c := id) measurable_id
    rw [Measure.map_id] at this
    exact this

  let T := (GlobalTheory.CompanionTheory.SW.HaarCoord.hermCoord_isHomeomorph R hinv h2 hδ hσδ n t5 t6).homeomorph
    (GlobalTheory.CompanionTheory.SW.HaarCoord.hermCoord R σ n)
  have hbox := map_prod_box (n := n) (P := {p : Fin n × Fin n // p.1 < p.2}) lam
    (GlobalTheory.CompanionTheory.SW.coordK R b lam) r hr hκ
  have hc : Measurable (fun x : (Fin n → R) × ({p : Fin n × Fin n // p.1 < p.2} → R ⊗[F] E) =>
      (Sum.elim x.1 (fun q : Fin d × {p : Fin n × Fin n // p.1 < p.2} => r (x.2 q.2) q.1) : Idx n d → R)) := by
    refine measurable_pi_iff.2 fun i => ?_
    rcases i with i | q
    · exact (measurable_pi_apply i).comp measurable_fst
    · exact (measurable_pi_apply q.1).comp
        (hr.comp ((measurable_pi_apply q.2).comp measurable_snd))
  have hm := map_comp_comap T.toMeasurableEquiv
    ((Measure.pi fun _ : Fin n => lam).prod
      (Measure.pi fun _ : {p : Fin n × Fin n // p.1 < p.2} => GlobalTheory.CompanionTheory.SW.coordK R b lam)) hc
  rw [hbox] at hm
  have hfun : hCo R σ b = (fun x : (Fin n → R) × ({p : Fin n × Fin n // p.1 < p.2} → R ⊗[F] E) =>
      (Sum.elim x.1 (fun q : Fin d × {p : Fin n × Fin n // p.1 < p.2} => r (x.2 q.2) q.1) : Idx n d → R)) ∘
      T.toMeasurableEquiv := by
    funext S i
    rcases i with i | q <;> rfl
  rw [hfun]
  exact hm

end GlobalTheory.CompanionTheory.SiegelND.Coef.TestN
