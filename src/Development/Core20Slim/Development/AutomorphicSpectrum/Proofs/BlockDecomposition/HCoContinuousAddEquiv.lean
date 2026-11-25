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
public import Init.Data.Sum.Basic
public import Init.Data.Zero
public import Init.Ext
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Finsupp.SMul
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Prod.Basic
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Free
public import Mathlib.RingTheory.Trace.Defs
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Continuous
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

namespace GlobalTheory.CompanionTheory.SiegelND.Coef.TestN

theorem hCo_continuousAddEquiv : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R] [SecondCountableTopology R] [T2Space R] (d : ℕ) (b : Module.Basis (Fin d) F E) (n : ℕ), ∃ e : HermR R σ n ≃ₜ+ (Idx n d → R), ∀ S, e S = hCo R σ b S := by
  intro F E _ _ _ _ _ σ hCM R _ _ _ _ _ _ _ d b n
  obtain ⟨t1, t2, t3, t4, t5, t6, t7, -, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hCM R
  obtain ⟨hinv, δ, hδ, hσδ⟩ := GlobalTheory.CompanionTheory.SW.HaarCoord.conj_facts hCM
  have hfin : Module.finrank F E = 2 := hCM.2.2.1
  haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  haveI : ContinuousSMul R (R ⊗[F] E) := IsModuleTopology.toContinuousSMul R _
  haveI : ContinuousAdd (R ⊗[F] E) := IsModuleTopology.toContinuousAdd R _
  let h1 : HermR R σ n ≃ₜ (Fin n → R) × ({p : Fin n × Fin n // p.1 < p.2} → R ⊗[F] E) :=
    (GlobalTheory.CompanionTheory.SW.HaarCoord.hermCoord_isHomeomorph R hinv hfin hδ hσδ n t5 t6).homeomorph _
  let h2 : (R ⊗[F] E) ≃ₜ (Fin d → R) := (t7 d b).homeomorph _
  have h2a : ∀ y k, h2 y k = (Algebra.TensorProduct.basis R b).repr y k := fun _ _ => rfl
  let G : ((Fin n → R) × ({p : Fin n × Fin n // p.1 < p.2} → R ⊗[F] E)) ≃ₜ (Idx n d → R) :=
    { toFun := fun x => Sum.elim x.1 (fun q => h2 (x.2 q.2) q.1)
      invFun := fun f => (fun i => f (Sum.inl i), fun p => h2.symm fun k => f (Sum.inr (k, p)))
      left_inv := by
        rintro ⟨x, y⟩
        refine Prod.ext rfl ?_
        funext p
        exact h2.symm_apply_apply (y p)
      right_inv := by
        intro f
        funext q
        rcases q with i | ⟨k, p⟩
        · rfl
        · simp
      continuous_toFun := by
        refine continuous_pi fun q => ?_
        rcases q with i | ⟨k, p⟩
        · exact (continuous_apply i).comp continuous_fst
        · exact (continuous_apply k).comp
            (h2.continuous.comp ((continuous_apply p).comp continuous_snd))
      continuous_invFun := by
        refine Continuous.prodMk (continuous_pi fun i => continuous_apply _) (continuous_pi fun p => ?_)
        exact h2.symm.continuous.comp (continuous_pi fun k => continuous_apply _) }
  let H : HermR R σ n ≃ₜ (Idx n d → R) := h1.trans G
  have hH : ∀ S, H S = hCo R σ b S := by
    intro S
    funext q
    rcases q with i | ⟨k, p⟩ <;> rfl
  refine ⟨{ toEquiv := H.toEquiv
            map_add' := ?_
            continuous_toFun := H.continuous
            continuous_invFun := H.symm.continuous }, hH⟩
  intro S T
  show H (S + T) = H S + H T
  rw [hH, hH, hH]
  funext q
  rcases q with i | ⟨k, p⟩
  · simp [hCo, map_add (f := _), mul_add]
  · simp [hCo, map_add (f := _)]

end GlobalTheory.CompanionTheory.SiegelND.Coef.TestN
