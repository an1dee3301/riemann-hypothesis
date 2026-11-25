module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzFixedBySchroedingerOpenFiniteSubgr
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Classical
public import Init.Core
public import Init.Data.Function
public import Init.Data.Zero
public import Init.Ext
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.IsApply
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Basic
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Prod
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Equiv
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Module.Submodule.Range
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Notation.Prod
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Equiv
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Sets
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Prod.Basic
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Prod
public import Mathlib.LinearAlgebra.Projection
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Logic.Function.CompTypeclasses
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.Order.CompleteLattice.Defs
public import Mathlib.Order.Disjoint
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic

@[expose] public section

open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift

namespace GlobalTheory.SliceExt

noncomputable def splitPts (F : Type) [Field F] [NumberField F] (κ : Type) :
    (κ → AF F) ≃ (κ → mixedEmbedding.mixedSpace F) × (κ → Af F) where
  toFun x := (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1, fun i => (x i).2)
  invFun p := fun i => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (p.1 i), p.2 i)
  left_inv x := by
    funext i
    show (((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm
      (InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1), (x i).2) : AF F) = x i
    rw [RingEquiv.symm_apply_apply]; rfl
  right_inv p := by
    refine Prod.ext ?_ rfl
    funext i
    exact RingEquiv.apply_symm_apply _ _


open scoped TensorProduct in
open NumberField MeasureTheory in
theorem _root_.GlobalTheory.SliceExt.exists_rep_pure (F : Type) [Field F] [NumberField F]
    (κ : Type) [Fintype κ]
    (G : Type) [Group G] (ρ : G →* (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F κ →L[ℂ] _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F κ)) :
    ∃ ω₀ : G →* Module.End ℂ ((κ → _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) → ℂ), ∀ (g : G) (f : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F κ)
      (h : (κ → _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) → ℂ),
      ω₀ g (_root_.GlobalTheory.WeilM.pureA F f h) = _root_.GlobalTheory.WeilM.pureA F (ρ g f) h := by
  classical
  let ι : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F κ →ₗ[ℂ] ((κ → mixedEmbedding.mixedSpace F) → ℂ) :=
    { toFun := fun f => ⇑f, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have hι : Function.Injective ι := DFunLike.coe_injective
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl (LinearMap.range ι)
  let j := LinearEquiv.ofInjective ι hι
  let e := Submodule.prodEquivOfIsCompl _ C hC
  let A : G → Module.End ℂ ((κ → mixedEmbedding.mixedSpace F) → ℂ) := fun g =>
    e.toLinearMap ∘ₗ ((j.toLinearMap ∘ₗ (ρ g).toLinearMap ∘ₗ j.symm.toLinearMap).prodMap
      LinearMap.id) ∘ₗ e.symm.toLinearMap
  have hA1 : A 1 = 1 := by
    ext v
    simp [A]
  have hAmul : ∀ g h, A (g * h) = A g * A h := by
    intro g h
    ext v
    simp [A]
  have hAι : ∀ g f, A g (ι f) = ι (ρ g f) := by
    intro g f
    have : e.symm (ι f) = (j f, 0) := by
      rw [show ι f = ((j f : LinearMap.range ι) : _) from rfl]
      exact Submodule.prodEquivOfIsCompl_symm_apply_left _ _ hC _
    simp only [A, LinearMap.comp_apply, LinearEquiv.coe_coe, this, LinearMap.prodMap_apply,
      LinearEquiv.symm_apply_apply, map_zero, LinearMap.id_apply]
    rw [Submodule.coe_prodEquivOfIsCompl']
    simp [j]
  let s := _root_.GlobalTheory.SliceExt.splitPts F κ
  let slice : ((κ → _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) → ℂ) → (κ → _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) → (κ → mixedEmbedding.mixedSpace F) → ℂ :=
    fun Φ y a => Φ (s.symm (a, y))
  let W : G → Module.End ℂ ((κ → _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) → ℂ) := fun g =>
    { toFun := fun Φ x => A g (slice Φ (s x).2) (s x).1
      map_add' := by
        intro Φ Ψ
        funext x
        have : slice (Φ + Ψ) (s x).2 = slice Φ (s x).2 + slice Ψ (s x).2 := rfl
        simp only [this, map_add (f := _), Pi.add_apply]
      map_smul' := by
        intro c Φ
        funext x
        have : slice (c • Φ) (s x).2 = c • slice Φ (s x).2 := rfl
        simp only [this, map_smul, Pi.smul_apply, RingHom.id_apply] }
  refine ⟨{ toFun := W, map_one' := ?_, map_mul' := ?_ }, ?_⟩
  · ext Φ x
    simp only [W, hA1, LinearMap.coe_mk, AddHom.coe_mk, Module.End.one_apply, slice,
      Prod.mk.eta, Equiv.symm_apply_apply]
  · intro g h
    ext Φ x
    simp only [W, hAmul, LinearMap.coe_mk, AddHom.coe_mk, Module.End.mul_apply]
    have hsl : slice (fun x => A h (slice Φ (s x).2) (s x).1) (s x).2 = A h (slice Φ (s x).2) := by
      funext a
      simp only [slice, Equiv.apply_symm_apply]
    rw [hsl]
  · intro g f h
    funext x
    have hsl : ∀ (f' : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F κ),
        slice (_root_.GlobalTheory.WeilM.pureA F f' h) (s x).2 = h (s x).2 • ι f' := by
      intro f'
      funext a
      have h1 := s.apply_symm_apply (a, (s x).2)
      simp only [slice, _root_.GlobalTheory.WeilM.pureA, Pi.smul_apply, smul_eq_mul]
      have ha : (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (s.symm (a, (s x).2) i).1) = a :=
        congrArg Prod.fst h1
      have hy : (fun i => (s.symm (a, (s x).2) i).2) = (s x).2 := congrArg Prod.snd h1
      rw [ha, hy, mul_comm]
      rfl
    show A g (slice (_root_.GlobalTheory.WeilM.pureA F f h) (s x).2) (s x).1 = _
    rw [hsl, map_smul, hAι]
    simp only [Pi.smul_apply, smul_eq_mul, _root_.GlobalTheory.WeilM.pureA]
    rw [mul_comm]
    rfl

end GlobalTheory.SliceExt
