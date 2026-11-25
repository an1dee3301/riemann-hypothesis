module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ColMapEqColMapV
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.OmEqSumLattice
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsThetaAtOfVac
public import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
public import Development.AbelianVarietyTheory.Definitions.Divisors.InvVolConjLevelOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowShiftTheta
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.BinderNameHint
public import Init.Classical
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Int.Lemmas
public import Init.Data.Int.Order
public import Init.Data.Nat.Basic
public import Init.Data.Sum.Basic
public import Init.Data.Zero
public import Init.Omega.Coeffs
public import Init.Omega.Constraint
public import Init.Omega.Int
public import Init.Omega.LinearCombo
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Notation.Prod
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.IsEmpty.Basic
public import Mathlib.Basic.IsEmpty.Defs
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.BooleanAlgebra
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Empty
public import Mathlib.Data.Finset.Erase
public import Mathlib.Data.Finset.Insert
public import Mathlib.Data.Finset.Sum
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.Logic.Function.Basic
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.BooleanAlgebra.Defs
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.ExpansionInvariance

section Tensor

variable {ι : Type} [Fintype ι] [DecidableEq ι] {X Y : ι → Type} (T : ∀ i, (X i → ℂ) →ₗ[ℂ] (Y i → ℂ)) {δ : Type}

theorem sum_prod_partial_eq_zero (s : Finset δ) (a : δ → ℂ) (F : δ → ∀ i, X i → ℂ)
    (h : ∀ x : ∀ i, X i, ∑ d ∈ s, a d * ∏ i, F d i (x i) = 0) (A : Finset ι) (x : ∀ i, X i) (y : ∀ i, Y i) :
    ∑ d ∈ s, a d * ((∏ i ∈ A, T i (F d i) (y i)) * ∏ i ∈ Aᶜ, F d i (x i)) = 0 := by
  induction A using Finset.induction_on generalizing x with
  | empty => simpa using h x
  | @insert b A hb ih =>
    set c : δ → ℂ := fun d => a d * ((∏ i ∈ A, T i (F d i) (y i)) * ∏ i ∈ (insert b A)ᶜ, F d i (x i)) with hc
    have hbA : b ∈ Aᶜ := Finset.mem_compl.2 hb
    have hcompl : (insert b A)ᶜ = (Aᶜ).erase b := by
      ext i; simp [Finset.mem_erase, and_comm]
    have hφ : (∑ d ∈ s, c d • F d b) = 0 := by
      funext z
      have := ih (Function.update x b z)
      rw [Finset.sum_apply, Pi.zero_apply, ← this]
      refine Finset.sum_congr rfl fun d _ => ?_
      rw [Pi.smul_apply, smul_eq_mul, hc, ← Finset.mul_prod_erase _ _ hbA, Function.update_self, hcompl]
      have : ∏ i ∈ (Aᶜ).erase b, F d i (Function.update x b z i) = ∏ i ∈ (Aᶜ).erase b, F d i (x i) :=
        Finset.prod_congr rfl fun i hi => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
      rw [this]; ring
    have h2 := congrArg (fun f => T b f (y b)) hφ
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, map_zero, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h2
    rw [← h2]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [Finset.prod_insert hb, hc]; ring

theorem sum_prod_map_eq_zero (s : Finset δ) (a : δ → ℂ) (F : δ → ∀ i, X i → ℂ)
    (h : ∀ x : ∀ i, X i, ∑ d ∈ s, a d * ∏ i, F d i (x i) = 0) (y : ∀ i, Y i) :
    ∑ d ∈ s, a d * ∏ i, T i (F d i) (y i) = 0 := by
  by_cases hX : Nonempty (∀ i, X i)
  · obtain ⟨x⟩ := hX
    simpa using sum_prod_partial_eq_zero T s a F h Finset.univ x y
  · have hi : ∃ i, IsEmpty (X i) := by
      by_contra hn
      push_neg at hn
      exact hX ⟨fun i => Classical.choice (hn i)⟩
    obtain ⟨i, hi⟩ := hi
    have h0 : ∀ f : X i → ℂ, f = 0 := fun f => funext fun z => hi.elim z
    refine Finset.sum_eq_zero fun d _ => ?_
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (by rw [h0 (F d i), map_zero]; rfl), mul_zero]

theorem sum_prod_map_congr {δ' : Type} (s : Finset δ) (s' : Finset δ') (a : δ → ℂ) (a' : δ' → ℂ) (F : δ → ∀ i, X i → ℂ)
    (F' : δ' → ∀ i, X i → ℂ)
    (h : ∀ x : ∀ i, X i, ∑ d ∈ s', a' d * ∏ i, F' d i (x i) = ∑ d ∈ s, a d * ∏ i, F d i (x i)) (y : ∀ i, Y i) :
    ∑ d ∈ s', a' d * ∏ i, T i (F' d i) (y i) = ∑ d ∈ s, a d * ∏ i, T i (F d i) (y i) := by
  have key := sum_prod_map_eq_zero T (s'.disjSum s) (Sum.elim a' fun d => -a d) (Sum.elim F' F) (fun x => by
    rw [Finset.sum_disjSum]
    simp only [Sum.elim_inl, Sum.elim_inr, neg_mul, Finset.sum_neg_distrib, h x, add_neg_cancel]) y
  rw [Finset.sum_disjSum] at key
  simp only [Sum.elim_inl, Sum.elim_inr, neg_mul, Finset.sum_neg_distrib] at key
  exact sub_eq_zero.1 (by rw [sub_eq_add_neg]; exact key)

end Tensor

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

def stdLatO (S : GridChoice W U) (p : Pair T) : AddSubgroup (WO (G.pS p) (G.pT p)) :=
  latO (G.pS p) (G.pT p) (S.N.latS p : Set (Fin (G.pS p).rank → D.host.E)) (S.N.latT p : Set (Fin (G.pT p).rank → D.host.E))
    fun _ => True

def movedFn (_S : GridChoice W U) {t : T} (d : PureDat G t) (j : ℕ) (hj : j + 1 < D.R.m) (g : FinPt G (.top (j + 1))) :
    ∀ j' : Fin D.R.m, WO (G.pS (.top t j' : Pair T)) (G.pT (.top t j' : Pair T)) → ℂ :=
  Function.update (Function.update (fun j' => (d.1 j').fn) ⟨j, by omega⟩
      fun x => (d.1 ⟨j, by omega⟩).fn (actO _ _ 1⁻¹ (g : GA D (G.V (.top (j + 1))))⁻¹ x))
    ⟨j + 1, hj⟩ fun x => (d.1 ⟨j + 1, hj⟩).fn (actO _ _ (g : GA D (G.V (.top (j + 1))))⁻¹ 1⁻¹ x)

theorem vec_eq_model (S : GridChoice W U) {t : T} {p : Pair T} (d : FinDatum G t p) (hz : d.z = 1) (hv : S.Z.HasVec d)
    (Tm : (WO (G.pS p) (G.pT p) → ℂ) →ₗ[ℂ] (WO (G.pS p) (G.pT p) → ℂ))
    (hTm : IsPlaceModel W.ψ (symplO _ _) (heisO W.ψ _ _) d.e (stdLatO S p) 1 (S.Z.vac p) Tm) : S.Z.vec d = Tm d.fn := by
  obtain ⟨f, hf⟩ := hv
  rw [Normal.vec, FinDatum.vec_eq W hf, hz, ← hf.2 Tm hTm]
  rw [show ((1 : GA D (G.pS p)), (1 : GA D (G.pT p))) = 1 from rfl, map_one]
  rfl

end GlobalTheory.ExpansionInvariance

end
