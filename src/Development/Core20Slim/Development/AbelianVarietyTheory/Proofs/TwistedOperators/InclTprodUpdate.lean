module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteSupport
public import Development.Core20Slim.Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.KTypeExtension
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedSmooth
public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Classical
public import Init.Core
public import Init.Data.Function
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Ker
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Module.Submodule.LinearMap
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Mathlib.Analysis.CStarAlgebra.Module.Defs
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.FDeriv.Linear
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Logic.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Erase
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Set.Defs
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Complex.Module
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Multilinear.Basic
public import Mathlib.LinearAlgebra.PiTensorProduct.Basic
public import Mathlib.Logic.Function.Basic
public import Mathlib.Order.Notation
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.RestrictScalars
public import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.Algebra
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open Matrix MeasureTheory GlobalTheory.Chain GlobalTheory.Chain.RealIt
open GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension (kFin KVec KMap maxCpt rep_mem_kFin)
open scoped TensorProduct InnerProductSpace Classical
open GlobalTheory.Chain.IoLift
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Chain.IoLift.FinTensor

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel V S}

theorem inclK_injective (h : KSm M) : Function.Injective (inclK h) := by
  choose r hr using fun τ =>
    LinearMap.exists_leftInverse_of_injective (Submodule.inclusion (h τ))
      (LinearMap.ker_eq_bot.mpr (Submodule.inclusion_injective (h τ)))
  have key : PiTensorProduct.map r ∘ₗ inclK h = LinearMap.id := by
    unfold inclK
    rw [← PiTensorProduct.map_comp]
    simp only [hr, PiTensorProduct.map_id]
  intro x y hxy
  calc x = (PiTensorProduct.map r ∘ₗ inclK h) x := by rw [key, LinearMap.id_apply]
    _ = (PiTensorProduct.map r ∘ₗ inclK h) y := by rw [LinearMap.comp_apply, hxy, ← LinearMap.comp_apply]
    _ = y := by rw [key, LinearMap.id_apply]

theorem incl_tprod (h : KSm M) (v : ∀ ρ, kFin M ρ) :
    inclT M (inclK h (PiTensorProduct.tprod ℂ v)) = PiTensorProduct.tprod ℂ fun ρ => (v ρ : M.H ρ) := by
  simp [inclT, inclK]

theorem incl_tprod_update (h : KSm M) (v : ∀ ρ, kFin M ρ) (τ : D.what₂.Tau) (u : kFin M τ) :
    inclT M (inclK h (PiTensorProduct.tprod ℂ (Function.update v τ u))) =
      PiTensorProduct.tprod ℂ (Function.update (fun ρ => (v ρ : M.H ρ)) τ (u : M.H τ)) := by
  rw [incl_tprod]
  congr 1
  funext ρ
  rcases eq_or_ne ρ τ with rfl | hρ
  · simp
  · simp [Function.update_of_ne hρ]

theorem act_tprod (τ : D.what₂.Tau) (g : Matrix (Fin V.rank) (Fin V.rank) ℂ) (v : ∀ ρ, M.H ρ) :
    actT M τ g (PiTensorProduct.tprod ℂ v) = PiTensorProduct.tprod ℂ (Function.update v τ (M.rep τ g (v τ))) := by
  simp only [actT, PiTensorProduct.map_tprod]
  congr 1
  funext ρ
  rcases eq_or_ne ρ τ with rfl | hρ
  · simp
  · simp [Function.update_of_ne hρ]

theorem ell_update (w v : ∀ ρ, M.H ρ) (τ : D.what₂.Tau) (u : M.H τ) :
    ellT M w (PiTensorProduct.tprod ℂ (Function.update v τ u)) =
      ⟪w τ, u⟫_ℂ * ∏ ρ ∈ Finset.univ.erase τ, ⟪w ρ, v ρ⟫_ℂ := by
  have hs : ∀ ρ ∈ Finset.univ.erase τ, ⟪w ρ, Function.update v τ u ρ⟫_ℂ = ⟪w ρ, v ρ⟫_ℂ := fun ρ hρ => by
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hρ)]
  simp only [ellT, PiTensorProduct.lift.tprod, MultilinearMap.compLinearMap_apply,
    MultilinearMap.mkPiAlgebra_apply]
  show ∏ ρ, ⟪w ρ, Function.update v τ u ρ⟫_ℂ = _
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ τ), Function.update_self]
  congr 1
  exact Finset.prod_congr rfl hs

private theorem hasDerivAt_ellT_actT_exp_tprod (h : KSm M) (τ : D.what₂.Tau)
    (a : Matrix (Fin V.rank) (Fin V.rank) ℂ → Module.End ℂ (kFin M τ)) (ha : IsKAct M τ a)
    (X : Matrix (Fin V.rank) (Fin V.rank) ℂ) (hX : X ∈ lieAt V τ) (w : ∀ ρ, M.H ρ) (v : ∀ ρ, kFin M ρ) :
    HasDerivAt (fun t : ℝ => ellT M w (actT M τ (NormedSpace.exp (t • X)) (inclT M (inclK h (PiTensorProduct.tprod ℂ v)))))
      (ellT M w (inclT M (inclK h (intersection_update_fsHerm_neg_one τ (a X) (PiTensorProduct.tprod ℂ v))))) 0 := by
  have hd := ha.der X hX (v τ)
  have hi : HasDerivAt (fun t : ℝ => ⟪w τ, M.rep τ (NormedSpace.exp (t • X)) (v τ : M.H τ)⟫_ℂ)
      ⟪w τ, (a X (v τ) : M.H τ)⟫_ℂ 0 := by
    have hc := ((innerSL ℂ (w τ)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hd
    simpa [Function.comp_def] using hc
  have e2 : ellT M w (inclT M (inclK h (intersection_update_fsHerm_neg_one τ (a X) (PiTensorProduct.tprod ℂ v)))) =
      ⟪w τ, (a X (v τ) : M.H τ)⟫_ℂ * ∏ ρ ∈ Finset.univ.erase τ, ⟪w ρ, (v ρ : M.H ρ)⟫_ℂ := by
    rw [position_tprod, incl_tprod_update, ell_update]
  have e1 : (fun t : ℝ => ellT M w (actT M τ (NormedSpace.exp (t • X)) (inclT M (inclK h (PiTensorProduct.tprod ℂ v))))) =
      fun t : ℝ => ⟪w τ, M.rep τ (NormedSpace.exp (t • X)) (v τ : M.H τ)⟫_ℂ *
        ∏ ρ ∈ Finset.univ.erase τ, ⟪w ρ, (v ρ : M.H ρ)⟫_ℂ := by
    funext t
    rw [incl_tprod, act_tprod, ell_update]
  rw [e1, e2]
  exact hi.mul_const _

theorem derT_mapFactor (h : KSm M) (τ : D.what₂.Tau) (a : Matrix (Fin V.rank) (Fin V.rank) ℂ → Module.End ℂ (kFin M τ))
    (ha : IsKAct M τ a) (X : Matrix (Fin V.rank) (Fin V.rank) ℂ) (hX : X ∈ lieAt V τ) (x : KT M) :
    DerT M τ X (inclK h x) (inclK h (intersection_update_fsHerm_neg_one τ (a X) x)) := by
  delta DerT
  intro w
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r v =>
    simp only [map_smul, smul_eq_mul]
    exact (hasDerivAt_ellT_actT_exp_tprod h τ a ha X hX w v).const_mul r
  | add x y hx hy =>
    simp only [map_add (f := _)]
    exact hx.add hy

theorem incl_mapFactor_kOp (h : KSm M) (τ : D.what₂.Tau) (k : Matrix (Fin V.rank) (Fin V.rank) ℂ) (hk : k ∈ maxCpt M τ)
    (x : KT M) : inclT M (inclK h (intersection_update_fsHerm_neg_one τ (kOp M τ hk) x)) = actT M τ k (inclT M (inclK h x)) := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r v =>
    simp only [map_smul]
    congr 1
    rw [position_tprod, incl_tprod_update, incl_tprod, act_tprod] <;> rfl
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem kFinTensor : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (τ : D.what₂.Tau) (h : KSm M), Function.Injective (inclK h) ∧ (∀ a : Matrix (Fin V.rank) (Fin V.rank) ℂ → Module.End ℂ (kFin M τ), IsKAct M τ a → ∀ X ∈ lieAt V τ, ∀ x : KT M, DerT M τ X (inclK h x) (inclK h (intersection_update_fsHerm_neg_one τ (a X) x))) ∧ ∀ (k : Matrix (Fin V.rank) (Fin V.rank) ℂ) (hk : k ∈ maxCpt M τ) (x : KT M), inclT M (inclK h (intersection_update_fsHerm_neg_one τ (kOp M τ hk) x)) = actT M τ k (inclT M (inclK h x)) := by
  intro D V S M τ h
  refine ⟨inclK_injective h, ?_, ?_⟩
  · intro a ha X hX x
    exact derT_mapFactor h τ a ha X hX x
  · intro k hk x
    exact incl_mapFactor_kOp h τ k hk x

end GlobalTheory.Chain.IoLift.FinTensor

end
