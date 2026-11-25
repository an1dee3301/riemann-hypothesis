module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolMatchIff
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Classical
public import Init.Core
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
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
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Insert
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Sets
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Multilinear.Basic
public import Mathlib.LinearAlgebra.PiTensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Map
public import Mathlib.Logic.Function.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

open scoped TensorProduct Classical
open NumberField IsDedekindDomain MeasureTheory Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace GlobalTheory.ThK.PolynomialMatching

section Extend

variable {ι : Type} {M : ι → Type} [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)]

def padFam (T S : Finset ι) (c : ∀ i, M i) (x : ∀ u : T, M u) : ∀ u : S, M u :=
  fun u => if h : u.1 ∈ T then x ⟨u.1, h⟩ else c u.1

theorem padFam_update (T S : Finset ι) (hTS : T ⊆ S) (c : ∀ i, M i) [DecidableEq T] [DecidableEq S]
    (x : ∀ u : T, M u) (i : T) (y : M i) :
    padFam T S c (Function.update x i y) = Function.update (padFam T S c x) ⟨i.1, hTS i.2⟩ y := by
  funext u
  by_cases h : u.1 ∈ T
  · by_cases hu : u.1 = i.1
    · obtain ⟨u, hu'⟩ := u
      obtain ⟨i, hi⟩ := i
      simp only at hu
      subst hu
      simp [padFam, h]
    · have h1 : (⟨u.1, h⟩ : T) ≠ i := fun e => hu (by rw [← e])
      have h2 : u ≠ ⟨i.1, hTS i.2⟩ := fun e => hu (by rw [e])
      simp only [padFam, h, dif_pos, Function.update_of_ne h1, Function.update_of_ne h2]
  · have h2 : u ≠ ⟨i.1, hTS i.2⟩ := fun e => h (by rw [e]; exact i.2)
    simp only [padFam, h, dif_neg, not_false_eq_true, Function.update_of_ne h2]

def padMultilinear (T S : Finset ι) (hTS : T ⊆ S) (c : ∀ i, M i) :
    (∀ u : T, M u) →ₘₗ[ℂ] (⨂[ℂ] u : S, M u) where
  toFun x := PiTensorProduct.tprod ℂ (padFam T S c x)
  map_update_add' x i y z := by
    simp only [padFam_update T S hTS c]
    exact (PiTensorProduct.tprod ℂ).map_update_add _ _ _ _
  map_update_smul' x i r y := by
    simp only [padFam_update T S hTS c]
    exact (PiTensorProduct.tprod ℂ).map_update_smul _ _ _ _

def padTensor (T S : Finset ι) (hTS : T ⊆ S) (c : ∀ i, M i) :
    (⨂[ℂ] u : T, M u) →ₗ[ℂ] ⨂[ℂ] u : S, M u :=
  PiTensorProduct.lift (padMultilinear T S hTS c)

theorem padTensor_tprod (T S : Finset ι) (hTS : T ⊆ S) (c : ∀ i, M i) (x : ∀ u : T, M u) :
    padTensor T S hTS c (PiTensorProduct.tprod ℂ x) = PiTensorProduct.tprod ℂ (padFam T S c x) := by
  simp [padTensor, padMultilinear]

end Extend

theorem polMatchOn_insert : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (R : RealMaps F a a') (Rf : FinMaps F a a') (v : Pl (F := F)),
    Rf.p v (G.M.vac v) = Rf.p' v (G.M'.vac v) → ∀ (T : Finset (Pl (F := F))) (Φ : (Fin a × Fin (a + a') → AF F) → ℂ)
    (Φ' : (Fin a' × Fin (a + a') → AF F) → ℂ), GlobalTheory.ThK.PolynomialMatching.PolMatchOn B G X R Rf T Φ Φ' →
    GlobalTheory.ThK.PolynomialMatching.PolMatchOn B G X R Rf (insert v T) Φ Φ' := by
  intro F E _ _ _ _ _ σ B a a' G X R Rf v hv T Φ Φ' hM
  obtain ⟨m, m', f, φ, f', φ', hφ, hφ', hΦ, hΦ', hsum⟩ := hM
  refine ⟨m, m', f, φ, f', φ',
    fun i => ⟨(hφ i).1, (hφ i).2.1, fun w hw => (hφ i).2.2 w fun h => hw (Finset.mem_insert_of_mem h)⟩,
    fun j => ⟨(hφ' j).1, (hφ' j).2.1, fun w hw => (hφ' j).2.2 w fun h => hw (Finset.mem_insert_of_mem h)⟩,
    hΦ, hΦ', ?_⟩
  let c : ∀ u, Rf.Pi u := fun u => Rf.p u (G.M.vac u)
  have key := congrArg (LinearMap.lTensor R.Pi (padTensor T (insert v T) (Finset.subset_insert _ _) c)) hsum
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, LinearMap.lTensor_tmul, padTensor_tprod] at key
  have e1 : ∀ i, padFam T (insert v T) c (fun u : T => Rf.p u (φ i u)) =
      fun u : (insert v T : Finset (Pl (F := F))) => Rf.p u (φ i u) := by
    intro i
    funext u
    by_cases h : u.1 ∈ T
    · simp [padFam, h]
    · simp [padFam, h, c, (hφ i).2.2 u.1 h]
  have e2 : ∀ j, padFam T (insert v T) c (fun u : T => Rf.p' u (φ' j u)) =
      fun u : (insert v T : Finset (Pl (F := F))) => Rf.p' u (φ' j u) := by
    intro j
    funext u
    by_cases h : u.1 ∈ T
    · simp [padFam, h]
    · obtain ⟨u, hu⟩ := u
      have huv : u = v := by
        rcases Finset.mem_insert.1 hu with h' | h'
        · exact h'
        · exact absurd h' h
      subst huv
      simp [padFam, h, c, (hφ' j).2.2 u h, hv]
  simp only [e1, e2] at key
  exact key

end GlobalTheory.ThK.PolynomialMatching
