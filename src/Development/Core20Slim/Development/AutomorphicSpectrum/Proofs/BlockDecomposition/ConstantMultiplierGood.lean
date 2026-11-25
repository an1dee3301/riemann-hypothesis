module

public import Mathlib
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.DictInf
public import Development.Core20Slim.Development.AutomorphicArithmetic.LocalEmbeddings.OppLagr
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
public import Development.Core20Slim.Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.AdelicHomeomorphisms.IsTopologicalGroupG2
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.ConvGrOf
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.IsEpCont
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.StripEntire
public import Development.Core20Slim.Development.WeilBound.ThetaLifts.LatticeBasics.HypothesesE
public import Formalism.LocalToGlobal.IndefiniteReal.PHeisFC
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.Core20Slim.GroundTheory.GlobalFields.IdeleGroups.IdeleNorms
public import Development.Core20Slim.GroundTheory.GlobalFields.IdeleGroups.InfiniteProjInfiniteEmbeddingOfNe
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.NonUnitalHom
public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Subsemigroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Group.Units.Equiv
public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Notation.Prod
public import Mathlib.Algebra.Order.Positive.Ring
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Equiv
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Embedding
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Unramified.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

namespace GlobalTheory.CompanionTheory.RgEisCM

open scoped TensorProduct NNReal Matrix NumberField.AdeleRing
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
open PositivityTheory.RgEis

section Transport

variable {R R' : Type} [CommRing R] [CommRing R'] {ι : Type} [Fintype ι] [DecidableEq ι]

def glEquiv (e : R ≃+* R') : GL ι R ≃* GL ι R' := Units.mapEquiv (RingEquiv.mapMatrix e).toMulEquiv

theorem coe_glEquiv (e : R ≃+* R') (g : GL ι R) :
    ((glEquiv e g : GL ι R') : Matrix ι ι R') = (g : Matrix ι ι R).map e := rfl

theorem coe_glEquiv_inv (e : R ≃+* R') (g : GL ι R) :
    (((glEquiv e g)⁻¹ : GL ι R') : Matrix ι ι R') = ((g⁻¹ : GL ι R) : Matrix ι ι R).map e := by
  rw [← map_inv]; rfl

theorem mem_stab_iff (e : R ≃+* R') (s : Set ι) (g : GL ι R) :
    g ∈ stab R s ↔ glEquiv e g ∈ stab R' s := by
  change (∀ r ∉ s, ∀ c ∈ s, _ ∧ _) ↔ (∀ r ∉ s, ∀ c ∈ s, _ ∧ _)
  simp only [coe_glEquiv, coe_glEquiv_inv, Matrix.map_apply, EmbeddingLike.map_eq_zero_iff]

variable {E : Type} [Field E]

theorem mem_kGL_iff (A : Ad E R) (B : Ad E R') (e : R ≃+* R') (hO : ∀ x, x ∈ A.O ↔ e x ∈ B.O)
    (hφ : ∀ w, ∃ w', ∀ x, A.φ w x = B.φ w' (e x)) (hφ' : ∀ w', ∃ w, ∀ x, A.φ w x = B.φ w' (e x)) (g : GL ι R) :
    g ∈ A.kGL ι ↔ glEquiv e g ∈ B.kGL ι := by
  change ((∀ r c, _ ∧ _) ∧ ∀ w, _) ↔ ((∀ r c, _ ∧ _) ∧ ∀ w, _)
  simp only [coe_glEquiv, coe_glEquiv_inv, Matrix.map_apply, hO]
  refine and_congr_right fun _ => ⟨fun h w' => ?_, fun h w => ?_⟩
  · obtain ⟨w, hw⟩ := hφ' w'
    have : ((g : Matrix ι ι R).map e).map (B.φ w') = (g : Matrix ι ι R).map (A.φ w) := by
      ext r c; simp [hw]
    rw [this]; exact h w
  · obtain ⟨w', hw⟩ := hφ w
    have : (g : Matrix ι ι R).map (A.φ w) = ((g : Matrix ι ι R).map e).map (B.φ w') := by
      ext r c; simp [hw]
    rw [this]; exact h w'

theorem iwa_transport (A : Ad E R) (B : Ad E R') (e : R ≃+* R') (hk : ∀ g : GL ι R, g ∈ A.kGL ι ↔ glEquiv e g ∈ B.kGL ι)
    (s : Set ι) (h : Iwa (stab R' s) (B.kGL ι)) : Iwa (stab R s) (A.kGL ι) := by
  intro g
  obtain ⟨p, hp, k, hk', hg⟩ := h (glEquiv e g)
  refine ⟨(glEquiv e).symm p, ?_, (glEquiv e).symm k, ?_, ?_⟩
  · rw [mem_stab_iff e]; simpa using hp
  · rw [hk]; simpa using hk'
  · apply (glEquiv e).injective
    simp [hg]

variable [TopologicalSpace R] [TopologicalSpace R']

theorem continuous_glEquiv (e : R ≃+* R') (h : Continuous e) : Continuous (glEquiv (ι := ι) e) :=
  Continuous.units_map _ (Continuous.matrix_map continuous_id h)

theorem kcpt_transport (A : Ad E R) (B : Ad E R') (e : R ≃+* R') (h1 : Continuous e) (h2 : Continuous e.symm)
    (hk : ∀ g : GL ι R, g ∈ A.kGL ι ↔ glEquiv e g ∈ B.kGL ι) (h : IsCompact (B.kGL ι : Set (GL ι R'))) :
    IsCompact (A.kGL ι : Set (GL ι R)) := by
  let H : GL ι R ≃ₜ GL ι R' :=
    { toEquiv := (glEquiv e).toEquiv
      continuous_toFun := continuous_glEquiv e h1
      continuous_invFun := continuous_glEquiv e.symm h2 }
  have : (A.kGL ι : Set (GL ι R)) = H ⁻¹' (B.kGL ι : Set (GL ι R')) := by
    ext g; exact hk g
  rw [this]
  exact H.isCompact_preimage.2 h

end Transport

section CM

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem cA_inclR (σ : E →ₐ[F] E) (x : E) :
    cA σ (inclR (F := F) (AF F) x) = inclR (F := F) (AF F) (σ x) := by
  simp [cA, inclR, Algebra.TensorProduct.map_tmul]

theorem cA_cA {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (z : AE F E) : cA σ (cA σ z) = z := by
  induction z using TensorProduct.inductionOn with
  | tmul a x => simp [cA, Algebra.TensorProduct.map_tmul, GlobalTheory.OppLagr.conj_conj h]
  | add x y hx hy => simp [map_add (f := _), hx, hy]

theorem continuous_cA (σ : E →ₐ[F] E) : Continuous (cA σ) := by
  haveI : Module.Finite (AF F) (AE F E) := inferInstance
  exact IsModuleTopology.continuous_of_linearMap (cA σ).toLinearMap

theorem cA_mem_intHat (σ : E →ₐ[F] E) {z : AE F E} (hz : z ∈ intHat F E) : cA σ z ∈ intHat F E := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, h1, h2, o, rfl⟩ := hz
    have ho : IsIntegral ℤ (σ (o : E)) := (RingOfIntegers.isIntegral_coe o).map σ
    refine AddSubgroup.subset_closure ⟨a, h1, h2, (⟨σ o, ho⟩ : 𝓞 E), ?_⟩
    rw [map_smul, cA_inclR]
    rfl
  | zero => simp [zero_mem]
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | neg x _ hx => rw [map_neg]; exact neg_mem hx

end CM

theorem cmGood : StdGood → Dict → DictInf → CMGood := by
  intro hS hD hI F E _ _ _ _ _ σ χ c hcm _ hχ hres
  have hs := hS E
  obtain ⟨d1, d2, d3, d4, -⟩ := hD F E
  have hO : ∀ x, x ∈ (adCM σ χ).O ↔ eqv F E x ∈ (adStd E).O := fun x => Iff.rfl
  have hk : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (g : GL ι (AE F E)),
      g ∈ (adCM σ χ).kGL ι ↔ glEquiv (eqv F E) g ∈ (adStd E).kGL ι := fun ι _ _ g =>
    mem_kGL_iff _ _ _ hO (fun w => ⟨w, fun _ => rfl⟩) (fun w => ⟨w, fun _ => rfl⟩) g
  have hu : Continuous (Units.map (eqv F E).toRingHom.toMonoidHom) := Continuous.units_map _ d1
  have hi : ∀ x : Eˣ, Units.map (eqv F E).toRingHom.toMonoidHom (Units.map (inclR (F := F) (AF F)).toMonoidHom x) =
      Units.map (adStd E).i.toMonoidHom x := fun x => Units.ext (d3 x)
  obtain ⟨ξ, hξ⟩ := GlobalTheory.OppLagr.exists_isQuad hcm
  refine ⟨⟨?_, ?_, ?_, ?_, hχ.1, hχ.2, ?_, ?_⟩, cA_cA hcm, continuous_cA σ, ?_, ?_, ?_, ?_⟩
  · intro x y hxy
    apply hs.iinj
    change algebraMap E 𝔸[E] x = algebraMap E 𝔸[E] y
    rw [← d3, ← d3]
    exact congrArg _ hxy
  · intro x y
    change (adStd E).lg (Units.map _ (x * y)) = _
    rw [map_mul]
    exact hs.lgmul _ _
  · exact hs.lgcont.comp hu
  · intro x
    exact (congrArg (adStd E).lg (hi x)).trans (hs.lgi x)
  · intro ι _ _
    exact kcpt_transport _ _ (eqv F E) d1 d2 (hk ι) (hs.kcpt ι)
  · intro ι _ _ s
    exact iwa_transport _ _ (eqv F E) (hk ι) s (hs.iwa ι s)
  · intro x hx
    have h1 : finOne F • x ∈ intHat F E := (d4 x).1 hx
    refine (d4 _).2 ?_
    have h2 := cA_mem_intHat σ h1
    rwa [map_smul] at h2
  · intro w x
    exact (hI F E σ hcm).1 w x
  · intro x
    exact ⟨σ x, cA_inclR σ x⟩
  · intro x
    exact ResEtaPow.map_conj hξ hres x

end GlobalTheory.CompanionTheory.RgEisCM
