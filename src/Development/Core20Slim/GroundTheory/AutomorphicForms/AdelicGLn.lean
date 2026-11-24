module

public import Mathlib
public import Development.Core20Slim.GroundTheory.GlobalFields.LocalFieldAtPlace
public import Development.Core20Slim.GroundTheory.GlobalFields.Adele.Topology
public import Development.Core20Slim.GroundTheory.GlobalFields.Adele.Discrete
public import Development.Core20Slim.GroundTheory.GlobalFields.Adele.Compact
public import GroundTheory.AutomorphicForms.GLnLocal
public import GroundTheory.AutomorphicForms.LocallyProfinite
public import Development.Core20Slim.GroundTheory.AutomorphicForms.RestrictedProductMatrix
public import GroundTheory.GlobalFields.Adele.Approximation
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Opposite
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Submonoid.Units
public import Mathlib.Algebra.Group.Subsemigroup.Defs
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.Algebra.Group.WithOne.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Notation.Prod
public import Mathlib.Algebra.Opposites
public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.WithAbs
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SProd
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
public import Mathlib.Order.Filter.Cofinite
public import Mathlib.Order.Filter.Defs
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Valuation.Integers
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.RingTheory.Valuation.ValuativeRel.Basic
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Algebra.Group.Units
public import Mathlib.Topology.Algebra.RestrictedProduct.Basic
public import Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.Valued.ValuationTopology
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Compactness.LocallyCompact
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open NumberField IsDedekindDomain Topology Filter Set
open scoped NumberField.AdeleRing RestrictedProduct

namespace GroundTheory.Automorphic

noncomputable section

instance locallyCompactSpace_matrix {m R : Type*} [Finite m] [TopologicalSpace R]
    [LocallyCompactSpace R] : LocallyCompactSpace (Matrix m m R) :=
  inferInstanceAs (LocallyCompactSpace (m → m → R))

namespace AdelicGLn

variable (K : Type*) [Field K] [NumberField K] (n : ℕ)

abbrev AdelicMatrix : Type _ := Matrix (Fin n) (Fin n) 𝔸[K]

abbrev AdelicGL : Type _ := GL (Fin n) 𝔸[K]

abbrev InfiniteAdelicGL : Type _ := GL (Fin n) (InfiniteAdeleRing K)

abbrev FiniteAdelicGL : Type _ := GL (Fin n) (FiniteAdeleRing (𝓞 K) K)


def det : AdelicGL K n →* (𝔸[K])ˣ :=
  Matrix.GeneralLinearGroup.det

@[simp]
theorem coe_det (g : AdelicGL K n) : (det K n g : 𝔸[K]) = (g : AdelicMatrix K n).det :=
  rfl

theorem continuous_det : Continuous (det K n) := by
  refine Units.continuous_iff.2 ⟨Continuous.matrix_det (Units.continuous_val (M := AdelicMatrix K n)),
    ?_⟩
  have : (fun g : AdelicGL K n => (((det K n g)⁻¹ : (𝔸[K])ˣ) : 𝔸[K])) =
      fun g => ((g⁻¹ : AdelicGL K n) : AdelicMatrix K n).det := by
    funext g
    rw [← map_inv]
    rfl
  rw [this]
  exact Continuous.matrix_det (Units.continuous_coe_inv (M := AdelicMatrix K n))

def prodEquiv : AdelicGL K n ≃ₜ* InfiniteAdelicGL K n × FiniteAdelicGL K n :=
  glProdEquiv (Fin n) (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K)

@[simp]
theorem prodEquiv_apply_fst (g : AdelicGL K n) (a b : Fin n) :
    (prodEquiv K n g).1 a b = (g a b).1 :=
  rfl

@[simp]
theorem prodEquiv_apply_snd (g : AdelicGL K n) (a b : Fin n) :
    (prodEquiv K n g).2 a b = (g a b).2 :=
  rfl

def infiniteEquiv : InfiniteAdelicGL K n ≃ₜ* Π w : InfinitePlace K, GL (Fin n) w.Completion :=
  glPiEquiv (Fin n) fun w : InfinitePlace K => w.Completion

omit [NumberField K] in
@[simp]
theorem infiniteEquiv_apply (g : InfiniteAdelicGL K n) (w : InfinitePlace K) (a b : Fin n) :
    infiniteEquiv K n g w a b = g a b w :=
  rfl

theorem mem_integralMatrices_adicCompletion (v : HeightOneSpectrum (𝓞 K))
    (M : Matrix (Fin n) (Fin n) (v.adicCompletion K)) :
    M ∈ GLnLocal.integralMatrices (v.adicCompletion K) n ↔
      ∀ a b, M a b ∈ v.adicCompletionIntegers K := by
  rw [GLnLocal.mem_integralMatrices]
  simp only [GroundTheory.Global.mem_valuationInteger_iff]

def finiteRestrictedEquiv :
    FiniteAdelicGL K n ≃ₜ* Πʳ v : HeightOneSpectrum (𝓞 K),
      [GL (Fin n) (v.adicCompletion K), GLnLocal.integralGL (v.adicCompletion K) n] :=
  (RestrictedProduct.matrixUnitsEquiv (Fin n)
    (R := fun v : HeightOneSpectrum (𝓞 K) => v.adicCompletion K)
    (B := fun v => v.adicCompletionIntegers K)
    (C := fun v => GLnLocal.integralMatrices (v.adicCompletion K) n)
    (mem_integralMatrices_adicCompletion K n)
    (fun v => Valued.isOpen_valuationSubring (v.adicCompletion K))).trans
    (RestrictedProduct.congrSetsMul fun v => by
      rw [GLnLocal.integralGL_eq_units]
      rfl)

@[simp]
theorem finiteRestrictedEquiv_apply (g : FiniteAdelicGL K n) (v : HeightOneSpectrum (𝓞 K))
    (a b : Fin n) :
    (finiteRestrictedEquiv K n g v : GL (Fin n) (v.adicCompletion K)) a b = g a b v :=
  rfl

def restrictedProductEquiv :
    AdelicGL K n ≃ₜ* (Π w : InfinitePlace K, GL (Fin n) w.Completion) ×
      Πʳ v : HeightOneSpectrum (𝓞 K),
        [GL (Fin n) (v.adicCompletion K), GLnLocal.integralGL (v.adicCompletion K) n] :=
  (prodEquiv K n).trans
    { toMulEquiv := MulEquiv.prodCongr (infiniteEquiv K n).toMulEquiv
        (finiteRestrictedEquiv K n).toMulEquiv
      continuous_toFun := ((infiniteEquiv K n).continuous.comp continuous_fst).prodMk
        ((finiteRestrictedEquiv K n).continuous.comp continuous_snd)
      continuous_invFun := ((infiniteEquiv K n).symm.continuous.comp continuous_fst).prodMk
        ((finiteRestrictedEquiv K n).symm.continuous.comp continuous_snd) }

theorem eventually_mem_integralGL (g : AdelicGL K n) :
    ∀ᶠ v in cofinite, (restrictedProductEquiv K n g).2 v ∈
      GLnLocal.integralGL (v.adicCompletion K) n :=
  ((restrictedProductEquiv K n g).2).2

def integralFiniteMatrices : Subring (Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 K) K)) :=
  (RingHom.mapMatrix (GroundTheory.Global.integralFiniteAdeles (𝓞 K) K).subtype).range

theorem mem_integralFiniteMatrices {M : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 K) K)} :
    M ∈ integralFiniteMatrices K n ↔
      ∀ a b, M a b ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 K) K := by
  constructor
  · rintro ⟨N, rfl⟩ a b
    exact (N a b).2
  · intro h
    exact ⟨Matrix.of fun a b => ⟨M a b, h a b⟩, rfl⟩

def integralFiniteGL : Subgroup (FiniteAdelicGL K n) :=
  (integralFiniteMatrices K n).toSubmonoid.units

theorem mem_integralFiniteGL_iff {g : FiniteAdelicGL K n} :
    g ∈ integralFiniteGL K n ↔
      (∀ a b, g a b ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 K) K) ∧
        ∀ a b, (g⁻¹ : FiniteAdelicGL K n) a b ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 K) K := by
  rw [integralFiniteGL, Submonoid.mem_units_iff, Subring.mem_toSubmonoid,
    Subring.mem_toSubmonoid, mem_integralFiniteMatrices, mem_integralFiniteMatrices]

theorem mem_integralFiniteGL_iff_forall {g : FiniteAdelicGL K n} :
    g ∈ integralFiniteGL K n ↔
      ∀ v, finiteRestrictedEquiv K n g v ∈ GLnLocal.integralGL (v.adicCompletion K) n := by
  have hinv : ∀ v a b, ((finiteRestrictedEquiv K n g v)⁻¹ : GL (Fin n) (v.adicCompletion K)) a b =
      (g⁻¹ : FiniteAdelicGL K n) a b v := fun v a b => by
    rw [← RestrictedProduct.inv_apply, ← map_inv]
    rfl
  simp only [mem_integralFiniteGL_iff, GLnLocal.mem_integralGL_iff, hinv,
    finiteRestrictedEquiv_apply, GroundTheory.Global.mem_valuationInteger_iff,
    GroundTheory.Global.mem_integralFiniteAdeles]
  constructor
  · rintro ⟨h1, h2⟩ v
    exact ⟨fun a b => h1 a b v, fun a b => h2 a b v⟩
  · intro h
    exact ⟨fun a b v => (h v).1 a b, fun a b v => (h v).2 a b⟩


theorem isCompact_integralFiniteMatrices :
    IsCompact (integralFiniteMatrices K n :
      Set (Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 K) K))) := by
  have : (integralFiniteMatrices K n : Set (Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 K) K))) =
      Set.pi univ fun _ => Set.pi univ fun _ =>
        (GroundTheory.Global.integralFiniteAdeles (𝓞 K) K : Set (FiniteAdeleRing (𝓞 K) K)) := by
    exact Set.ext fun M =>
      ⟨fun h a _ b _ => (mem_integralFiniteMatrices K n).1 h a b,
        fun h => (mem_integralFiniteMatrices K n).2 fun a b => h a (mem_univ a) b (mem_univ b)⟩
  rw [this]
  exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ =>
    GroundTheory.Global.isCompact_integralFiniteAdeles K


theorem isCompact_integralFiniteGL :
    IsCompact (integralFiniteGL K n : Set (FiniteAdelicGL K n)) := by
  have h := (isCompact_integralFiniteMatrices K n).prod
    (MulOpposite.opHomeomorph.symm.isCompact_preimage.2 (isCompact_integralFiniteMatrices K n))
  convert Units.isClosedEmbedding_embedProduct.isCompact_preimage h using 1
  ext u
  simp only [SetLike.mem_coe, integralFiniteGL, Submonoid.mem_units_iff, Set.mem_preimage,
    Set.mem_prod, Units.embedProduct_apply, Subring.mem_toSubmonoid]
  exact Iff.rfl

theorem totallyDisconnectedSpace_of_injective {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [TotallyDisconnectedSpace Y] {f : X → Y} (hf : Continuous f)
    (hinj : Function.Injective f) : TotallyDisconnectedSpace X :=
  ⟨fun s _ hs => Set.subsingleton_of_image hinj s
    (isTotallyDisconnected_of_totallyDisconnectedSpace _ _ (Set.subset_univ _)
      (hs.image f hf.continuousOn))⟩

instance totallyDisconnectedSpace_finite : TotallyDisconnectedSpace (FiniteAdelicGL K n) :=
  totallyDisconnectedSpace_of_injective
    (f := fun g v => finiteRestrictedEquiv K n g v)
    (continuous_pi fun v =>
      (_root_.RestrictedProduct.continuous_eval v).comp (finiteRestrictedEquiv K n).continuous)
    fun _ _ hgh => (finiteRestrictedEquiv K n).injective
      (Subtype.ext (funext fun v => congrFun hgh v))


def diagonal : GL (Fin n) K →* AdelicGL K n :=
  Units.map (algebraMap K 𝔸[K]).mapMatrix.toMonoidHom

@[simp]
theorem diagonal_apply (γ : GL (Fin n) K) (a b : Fin n) :
    diagonal K n γ a b = algebraMap K 𝔸[K] (γ a b) :=
  rfl


def rationalGL : Subgroup (AdelicGL K n) :=
  (diagonal K n).range

theorem exists_isOpen_inter_eq_zero :
    ∃ V : Set 𝔸[K], IsOpen V ∧ (0 : 𝔸[K]) ∈ V ∧ ∀ k : K, algebraMap K 𝔸[K] k ∈ V → k = 0 := by
  have := GroundTheory.Global.discreteTopology_principalSubgroup K
  obtain ⟨V, hVo, hV⟩ := isOpen_induced_iff.1
    (isOpen_discrete ({0} : Set (NumberField.AdeleRing.principalSubgroup (𝓞 K) K)))
  refine ⟨V, hVo, ?_, fun k hk => ?_⟩
  · have : (0 : NumberField.AdeleRing.principalSubgroup (𝓞 K) K) ∈ Subtype.val ⁻¹' V := by
      rw [hV]; rfl
    exact this
  · have : (⟨algebraMap K 𝔸[K] k, ⟨k, rfl⟩⟩ : NumberField.AdeleRing.principalSubgroup (𝓞 K) K) ∈
        Subtype.val ⁻¹' V := hk
    rw [hV, Set.mem_singleton_iff, Subtype.ext_iff] at this
    exact NumberField.AdeleRing.algebraMap_injective (𝓞 K) K (this.trans (map_zero _).symm)

theorem discreteTopology_rationalGL : DiscreteTopology (rationalGL K n) := by
  obtain ⟨V, hVo, hV0, hV⟩ := exists_isOpen_inter_eq_zero K
  let W : Set (AdelicGL K n) :=
    ⋂ a, ⋂ b, (fun g : AdelicGL K n => (g : AdelicMatrix K n) a b - (1 : AdelicMatrix K n) a b) ⁻¹' V
  have hWo : IsOpen W := isOpen_iInter_of_finite fun a => isOpen_iInter_of_finite fun b =>
    hVo.preimage
      ((Continuous.matrix_elem (Units.continuous_val (M := AdelicMatrix K n)) a b).sub
        continuous_const)
  refine discreteTopology_of_isOpen_singleton_one (isOpen_induced_iff.2 ⟨W, hWo, ?_⟩)
  ext ⟨g, γ, rfl⟩
  simp only [W, Set.mem_preimage, Set.mem_iInter, Set.mem_singleton_iff]
  constructor
  · intro h
    have hγ : γ = 1 := by
      have hsub : ((diagonal K n γ : AdelicGL K n) : AdelicMatrix K n) - 1 =
          (algebraMap K 𝔸[K]).mapMatrix ((γ : Matrix (Fin n) (Fin n) K) - 1) := by
        rw [map_sub, map_one]
        rfl
      refine Units.ext <| Matrix.ext fun a b => ?_
      have h1 := h a b
      rw [← Matrix.sub_apply, hsub] at h1
      have h2 := hV _ h1
      rw [Matrix.sub_apply, sub_eq_zero] at h2
      exact h2
    subst hγ
    exact Subtype.ext (map_one _)
  · intro h a b
    have : (diagonal K n γ : AdelicGL K n) = 1 := congrArg Subtype.val h
    rw [this, Units.val_one, sub_self]
    exact hV0


end AdelicGLn

end

end GroundTheory.Automorphic
