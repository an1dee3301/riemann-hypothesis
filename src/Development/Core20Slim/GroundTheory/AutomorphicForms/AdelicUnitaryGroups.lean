module

public import Mathlib
public import Development.Core20Slim.GroundTheory.AutomorphicForms.AdelicUnitaryGroups.Restricted
public import Development.Core20Slim.GroundTheory.AutomorphicForms.AdelicUnitaryGroups.LatticeCompact
public import Development.Core20Slim.GroundTheory.AutomorphicForms.AdelicUnitaryGroups.Anisotropic
public import Development.Core20Slim.GroundTheory.GlobalFields.Adele.Discrete
public import Development.Core20Slim.GroundTheory.GlobalFields.Adele.Topology
public import Development.Core20Slim.GroundTheory.AutomorphicForms.AdelicUnitaryGroups.Topology
public import Development.Core20Slim.GroundTheory.AutomorphicForms.HermitianSpaces
public import Development.Core20Slim.GroundTheory.AutomorphicForms.UnitaryGroupScheme
public import GroundTheory.GlobalFields.Adele.Approximation
public import Init.Core
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.NonUnitalHom
public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.Algebra.Algebra.Prod
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Basic
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Pi
public import Mathlib.Algebra.Ring.Prod
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.WithAbs
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.Normed.Ring.WithAbs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Finsupp.SMul
public import Mathlib.Data.Finsupp.SMulWithZero
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.LinearAlgebra.InvariantBasisNumber
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Free
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.UniformMulAction
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.Maps.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Order

@[expose] public section

namespace GroundTheory.Automorphic

open Module Matrix TensorProduct Topology Filter IsDedekindDomain NumberField
open scoped RestrictedProduct NumberField.AdeleRing

noncomputable section

variable {K E : Type*} [Field K] [CommRing E] [Algebra K E] [Algebra.IsQuadraticExtension K E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι E)

section Congr

variable {R S : Type*} [CommRing R] [Algebra K R] [TopologicalSpace R] [IsTopologicalRing R]
  [CommRing S] [Algebra K S] [TopologicalSpace S] [IsTopologicalRing S]

attribute [local instance] tensorTopology

def unitaryCongr (e : R ≃ₐ[K] S) (he : Continuous e) (he' : Continuous e.symm) :
    unitaryPoints K E H R ≃ₜ* unitaryPoints K E H S := by
  let b := Module.finBasis K E
  let f := unitaryMap K E H e.toAlgHom
  let f' := unitaryMap K E H e.symm.toAlgHom
  have hrepr :
      (∀ z : R ⊗[K] E, ∀ k,
        (Algebra.TensorProduct.basis S b).repr (tensorMap E e.toAlgHom z) k =
          e ((Algebra.TensorProduct.basis R b).repr z k)) ∧
      (∀ z : S ⊗[K] E, ∀ k,
        (Algebra.TensorProduct.basis R b).repr (tensorMap E e.symm.toAlgHom z) k =
          e.symm ((Algebra.TensorProduct.basis S b).repr z k)) := by
    constructor <;> intro z k <;> induction z using TensorProduct.inductionOn with
    | tmul r x => simp [Algebra.TensorProduct.basis_repr_tmul, Finsupp.mapRange_apply]
    | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]
  have hcoords :
      (∀ g p, unitaryCoords H S b (f g) p = e (unitaryCoords H R b g p)) ∧
      (∀ g p, unitaryCoords H R b (f' g) p = e.symm (unitaryCoords H S b g p)) := by
    exact ⟨fun g ⟨i, j, k⟩ => hrepr.1 (unitaryMat g i j) k,
      fun g ⟨i, j, k⟩ => hrepr.2 (unitaryMat g i j) k⟩
  have htensor :
      Continuous (tensorMap (E := E) e.toAlgHom) ∧
        Continuous (tensorMap (E := E) e.symm.toAlgHom) := by
    constructor
    · apply (tensorCoordsHomeomorph S b).isEmbedding.continuous_iff.mpr
      refine continuous_pi fun k => ?_
      have hk := he.comp ((continuous_apply k).comp (tensorCoordsHomeomorph R b).continuous)
      change Continuous (fun z => e (tensorCoordsHomeomorph R b z k)) at hk
      simpa only [Function.comp_apply, tensorCoordsHomeomorph_apply, hrepr.1] using hk
    · apply (tensorCoordsHomeomorph R b).isEmbedding.continuous_iff.mpr
      refine continuous_pi fun k => ?_
      have hk := he'.comp ((continuous_apply k).comp (tensorCoordsHomeomorph S b).continuous)
      change Continuous (fun z => e.symm (tensorCoordsHomeomorph S b z k)) at hk
      simpa only [Function.comp_apply, tensorCoordsHomeomorph_apply, hrepr.2] using hk
  refine
    { toFun := f
      invFun := f'
      left_inv := ?_
      right_inv := ?_
      map_mul' := map_mul f
      continuous_toFun := ?_
      continuous_invFun := ?_ }
  · intro g
    apply unitaryCoords_injective H R b
    funext p
    rw [hcoords.2, hcoords.1, e.symm_apply_apply]
  · intro g
    apply unitaryCoords_injective H S b
    funext p
    rw [hcoords.1, hcoords.2, e.apply_symm_apply]
  · have hm : Continuous fun M : Matrix ι ι (R ⊗[K] E) => M.map (tensorMap E e.toAlgHom) :=
      continuous_id.matrix_map htensor.1
    apply continuous_induced_rng.2
    rw [Units.continuous_iff]
    refine ⟨hm.comp (Units.continuous_val.comp continuous_subtype_val), ?_⟩
    change Continuous (fun g => ((f g : GL ι (S ⊗[K] E))⁻¹).val)
    simp only [← Subgroup.coe_inv, ← map_inv]
    exact hm.comp (Units.continuous_val.comp (continuous_subtype_val.comp continuous_inv))
  · have hm : Continuous fun M : Matrix ι ι (S ⊗[K] E) => M.map (tensorMap E e.symm.toAlgHom) :=
      continuous_id.matrix_map htensor.2
    apply continuous_induced_rng.2
    rw [Units.continuous_iff]
    refine ⟨hm.comp (Units.continuous_val.comp continuous_subtype_val), ?_⟩
    change Continuous (fun g => ((f' g : GL ι (R ⊗[K] E))⁻¹).val)
    simp only [← Subgroup.coe_inv, ← map_inv]
    exact hm.comp (Units.continuous_val.comp (continuous_subtype_val.comp continuous_inv))


end Congr

variable [NumberField K]

variable (K) in
def adeleRingEquivProd : 𝔸[K] ≃ₐ[K] InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K :=
  AlgEquiv.refl

variable (K) in
def infiniteAdeleRingEquivPi : InfiniteAdeleRing K ≃ₐ[K] ∀ w : InfinitePlace K, w.Completion :=
  AlgEquiv.refl

variable (K) in
def adeleInfiniteEval (w : InfinitePlace K) : 𝔸[K] →ₐ[K] w.Completion :=
  ((Pi.evalAlgHom K (fun w : InfinitePlace K => w.Completion) w).comp
    (infiniteAdeleRingEquivPi K).toAlgHom).comp
    ((AlgHom.fst K _ _).comp (adeleRingEquivProd K).toAlgHom)

variable (K) in
def adeleFiniteEval (v : HeightOneSpectrum (𝓞 K)) : 𝔸[K] →ₐ[K] v.adicCompletion K :=
  (finiteAdeleEval K v).comp ((AlgHom.snd K _ _).comp (adeleRingEquivProd K).toAlgHom)

variable {κ : Type*} [Fintype κ] (b : Basis κ K E)

theorem locallyCompactSpace_unitaryPoints_adele (hH : IsUnit H.det) :
    LocallyCompactSpace (unitaryPoints K E H 𝔸[K]) :=
  locallyCompactSpace_unitaryPoints H 𝔸[K] hH

variable (K) in
def unitaryDiagonal : unitaryPoints K E H K →* unitaryPoints K E H 𝔸[K] :=
  unitaryMap K E H (Algebra.ofId K 𝔸[K])

section Hermitian

variable {V : Type*} [AddCommGroup V] [Module E V] (h : HermitianForm K E V) (v : Basis ι E V)

def hermitianDiagonal : h.unitaryGroup →* unitaryPoints K E (gram h.toSesq v) 𝔸[K] :=
  (unitaryDiagonal K (gram h.toSesq v)).comp
    (unitaryPointsRationalEquivHermitian K E h v).symm.toMonoidHom

end Hermitian

end

end GroundTheory.Automorphic
