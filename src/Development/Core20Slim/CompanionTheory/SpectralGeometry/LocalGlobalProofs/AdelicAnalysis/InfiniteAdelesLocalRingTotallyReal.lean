module

public import Mathlib
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import Init.Core
public import Init.Data.Function
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Subsemigroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Group.Units.Equiv
public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.ZeroLEOne
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Equiv
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Pi
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.WithAbs
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Order.Lattice
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.Analysis.Normed.Ring.Units
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Countable.Defs
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Logic.Function.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.SetNotation
public import Mathlib.RingTheory.Artinian.Defs
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.RingTheory.Bialgebra.Basic
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.FiniteLength
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.Nilpotent.Defs
public import Mathlib.RingTheory.SimpleModule.Basic
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Basic
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.EMetricSpace.Defs
public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.Maps.Basic
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.MetricSpace.Isometry
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Metrizable.Basic
public import Mathlib.Topology.Metrizable.Uniformity
public import Mathlib.Topology.Order.OrderClosed
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.UniformSpace.Defs
public import Mathlib.Topology.UniformSpace.Pi
public import Mathlib.Topology.UniformSpace.Real

@[expose] public section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.LocInf

def posU (ι : Type) : Subgroup (ι → ℝ)ˣ where
  carrier := {u | ∀ i, 0 < (u : ι → ℝ) i}
  mul_mem' := fun {a b} ha hb i => by
    simpa using mul_pos (ha i) (hb i)
  one_mem' := fun i => by simp
  inv_mem' := by
    intro u hu i
    have h1 : ((u⁻¹ : (ι → ℝ)ˣ) : ι → ℝ) i * (u : ι → ℝ) i = 1 := by
      have := congrFun (u.inv_mul) i
      simpa using this
    exact (pos_iff_pos_of_mul_pos (h1 ▸ one_pos)).2 (hu i)

theorem isOpen_pos (ι : Type) [Finite ι] : IsOpen {x : ι → ℝ | ∀ i, 0 < x i} := by
  have h1 : {x : ι → ℝ | ∀ i, 0 < x i} = ⋂ i, {x : ι → ℝ | 0 < x i} := by
    ext x
    simp
  rw [h1]
  exact isOpen_iInter_of_finite fun i => isOpen_lt continuous_const (continuous_apply i)

theorem isOpen_posU (ι : Type) [Fintype ι] : IsOpen (posU ι : Set (ι → ℝ)ˣ) :=
  (isOpen_pos ι).preimage Units.continuous_val

theorem isOpenEmbedding_sq (ι : Type) [Fintype ι] :
    IsOpenEmbedding (fun u : posU ι => ((u : (ι → ℝ)ˣ) ^ 2 : (ι → ℝ)ˣ)) := by
  have hv : IsOpenEmbedding (Units.val : (ι → ℝ)ˣ → (ι → ℝ)) := Units.isOpenEmbedding_val
  refine (IsOpenEmbedding.of_comp_iff _ hv).1 ?_
  set j : posU ι → (ι → ℝ) := fun u => ((u : (ι → ℝ)ˣ) : ι → ℝ) with hjdef
  have hj : IsOpenEmbedding j := hv.comp (isOpen_posU ι).isOpenEmbedding_subtypeVal
  set g : posU ι → (ι → ℝ) := Units.val ∘ (fun u : posU ι => ((u : (ι → ℝ)ˣ) ^ 2 : (ι → ℝ)ˣ)) with hgdef
  have hg : Continuous g :=
    Units.continuous_val.comp (continuous_subtype_val.pow 2)
  let r : (ι → ℝ) → (ι → ℝ) := fun x i => Real.sqrt (x i)
  have hr : Continuous r := continuous_pi fun i => (continuous_apply i).sqrt
  have hrg : r ∘ g = j := by
    funext u i
    have hu : 0 < ((u : (ι → ℝ)ˣ) : ι → ℝ) i := u.2 i
    simp [r, g, j, Real.sqrt_sq hu.le]
  have hind : IsInducing g := IsInducing.of_comp hg hr (by rw [hrg]; exact hj.isInducing)
  have hinj : Function.Injective g := Function.Injective.of_comp (f := r) (by rw [hrg]; exact hj.injective)
  have hrange : Set.range g = {x : ι → ℝ | ∀ i, 0 < x i} := by
    ext x
    constructor
    · rintro ⟨u, rfl⟩ i
      have hu : 0 < ((u : (ι → ℝ)ˣ) : ι → ℝ) i := u.2 i
      simpa [g] using pow_pos hu 2
    · intro hx
      have hs : ∀ i, 0 < Real.sqrt (x i) := fun i => Real.sqrt_pos.2 (hx i)
      let w : (ι → ℝ)ˣ :=
        ⟨fun i => Real.sqrt (x i), fun i => (Real.sqrt (x i))⁻¹,
          by funext i; simp [(hs i).ne'], by funext i; simp [(hs i).ne']⟩
      refine ⟨⟨w, fun i => hs i⟩, ?_⟩
      funext i
      simp [g, w, Real.sq_sqrt (hx i).le]
  exact ⟨⟨hind, hinj⟩, by rw [hrange]; exact isOpen_pos ι⟩

variable (F : Type) [Field F] [NumberField F]

def eInf (h : IsTotallyReal F) : Ainf F ≃+* (InfinitePlace F → ℝ) :=
  RingEquiv.piCongrRight fun w => InfinitePlace.Completion.ringEquivRealOfIsReal (h.isReal w)

omit [NumberField F] in
theorem continuous_eInf (h : IsTotallyReal F) : Continuous (eInf F h) := by
  show Continuous (fun (x : ∀ w : InfinitePlace F, w.Completion) (w : InfinitePlace F) =>
    InfinitePlace.Completion.ringEquivRealOfIsReal (h.isReal w) (x w))
  exact continuous_pi fun w =>
    (InfinitePlace.Completion.isometryEquivRealOfIsReal (h.isReal w)).continuous.comp (continuous_apply w)

omit [NumberField F] in
theorem continuous_eInf_symm (h : IsTotallyReal F) : Continuous (eInf F h).symm := by
  show Continuous (fun (x : InfinitePlace F → ℝ) (w : InfinitePlace F) =>
    (InfinitePlace.Completion.ringEquivRealOfIsReal (h.isReal w)).symm (x w))
  exact continuous_pi fun w =>
    (InfinitePlace.Completion.isometryEquivRealOfIsReal (h.isReal w)).symm.continuous.comp (continuous_apply w)

def hInf (h : IsTotallyReal F) : Ainf F ≃ₜ (InfinitePlace F → ℝ) where
  toEquiv := (eInf F h).toEquiv
  continuous_toFun := continuous_eInf F h
  continuous_invFun := continuous_eInf_symm F h

def uInf (h : IsTotallyReal F) : (Ainf F)ˣ ≃ₜ (InfinitePlace F → ℝ)ˣ where
  toEquiv := (Units.mapEquiv (eInf F h).toMulEquiv).toEquiv
  continuous_toFun := Continuous.units_map _ (continuous_eInf F h)
  continuous_invFun := Continuous.units_map _ (continuous_eInf_symm F h)

end GlobalTheory.CompanionTheory.SW.LocInf


open GlobalTheory.CompanionTheory.SW.LocInf in
theorem GlobalTheory.CompanionTheory.SW.isLocR_Ainf : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → IsLocR (Ainf F) := by
  intro F _ _ h
  have hT2 : T2Space (Ainf F) := inferInstanceAs (T2Space (∀ w : InfinitePlace F, w.Completion))
  have hSC : SecondCountableTopology (Ainf F) := (hInf F h).secondCountableTopology
  have hArt : IsArtinianRing (Ainf F) := inferInstanceAs (IsArtinianRing (∀ w : InfinitePlace F, w.Completion))
  have hRed : IsReduced (Ainf F) := inferInstanceAs (IsReduced (∀ w : InfinitePlace F, w.Completion))
  have hval : IsOpenEmbedding (Units.val : (Ainf F)ˣ → Ainf F) := by
    have h1 : IsOpenEmbedding (Units.val : (InfinitePlace F → ℝ)ˣ → (InfinitePlace F → ℝ)) :=
      Units.isOpenEmbedding_val
    have h2 := ((hInf F h).symm.isOpenEmbedding.comp h1).comp (uInf F h).isOpenEmbedding
    convert h2 using 1
    funext u
    exact ((eInf F h).symm_apply_apply _).symm
  refine ⟨inferInstance, inferInstance, hSC, hT2, hArt, hRed, hval,
    (posU (InfinitePlace F)).comap (Units.map (eInf F h).toMonoidHom), ?_, ?_⟩
  · exact (isOpen_posU (InfinitePlace F)).preimage (uInf F h).continuous
  · let S := (posU (InfinitePlace F)).comap (Units.map (eInf F h).toMonoidHom)
    let T : S ≃ₜ posU (InfinitePlace F) :=
      (uInf F h).subtype (fun x => Iff.rfl)
    have h2 := ((uInf F h).symm.isOpenEmbedding.comp (isOpenEmbedding_sq (InfinitePlace F))).comp
      T.isOpenEmbedding
    convert h2 using 1
    funext u
    apply (uInf F h).injective
    simp only [Function.comp_apply, Homeomorph.apply_symm_apply]
    exact map_pow (Units.map (eInf F h).toMonoidHom) (u : (Ainf F)ˣ) 2
