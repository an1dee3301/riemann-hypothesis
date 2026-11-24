module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
public import Batteries.Logic
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.BinderNameHint
public import Init.Classical
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Ext
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.GroupWithZero.Action
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Prod
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Notation.Pi.Basic
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Notation.Prod
public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Equiv
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Pi
public import Mathlib.Algebra.Ring.Prod
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.WithAbs
public import Mathlib.Analysis.Normed.Ring.WithAbs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Prod
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
public import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Tactic.FieldSimp.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

open scoped TensorProduct Matrix Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift

noncomputable section

namespace GlobalTheory.PolRangeInf

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def adAt (w : InfinitePlace F) (c : w.Completion) : AF F :=
  LinearMap.inl F (Ainf F) (Af F) (Pi.single w c)

theorem piInf_adAt_same (v : InfinitePlace F) (τ : EmbOver E v) (c : v.Completion) (x : E) :
    piInf τ (adAt v c ⊗ₜ[F] x) = InfinitePlace.Completion.extensionEmbedding v c * τ.1 x := by
  change infEmb τ (evInf F v (adAt v c) ⊗ₜ[F] x) = _
  have : evInf F v (adAt v c) = c := by
    change (Pi.single v c : Ainf F) v = c
    exact Pi.single_eq_same v c
  rw [this, infEmb_tmul]

theorem piInf_adAt_ne {v w : InfinitePlace F} (h : v ≠ w) (τ : EmbOver E v) (c : w.Completion) (x : E) :
    piInf τ (adAt w c ⊗ₜ[F] x) = 0 := by
  change infEmb τ (evInf F v (adAt w c) ⊗ₜ[F] x) = _
  have : evInf F v (adAt w c) = 0 := by
    change (Pi.single w c : Ainf F) v = 0
    exact Pi.single_eq_of_ne h c
  rw [this, TensorProduct.zero_tmul, map_zero]

theorem ext_symm_real {w : InfinitePlace F} (hw : w.IsReal) (t : ℝ) :
    InfinitePlace.Completion.extensionEmbedding w ((InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm t) =
      (t : ℂ) := by
  rw [← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hw,
    ← InfinitePlace.Completion.ringEquivRealOfIsReal_apply, RingEquiv.apply_symm_apply]

theorem smul_adAt_tmul (u : AF F) (hu : evI F u = 0) (w : InfinitePlace F) (c : w.Completion) (x : E) :
    u • (adAt w c ⊗ₜ[F] x : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) = 0 := by
  have hu1 : u.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (hu.trans (map_zero _).symm)
  rw [TensorProduct.smul_tmul', smul_eq_mul]
  have : u * adAt w c = 0 := by
    refine Prod.ext ?_ ?_
    · change u.1 * (adAt w c).1 = 0
      rw [hu1, zero_mul]
    · change u.2 * (adAt w c).2 = 0
      exact mul_eq_zero_of_right _ rfl
  rw [this, TensorProduct.zero_tmul]

theorem exists_at_inf_values : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E}, IsCMExt F E σ → ∀ (τ : ∀ w : InfinitePlace F, EmbOver E w) (z : InfinitePlace F → ℂ),
    ∃ a : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), At (evI F) a ∧ ∀ w, piInf (τ w) a = z w := by
  intro F E _ _ _ _ _ σ h τ z
  haveI : IsTotallyReal F := h.1
  haveI : IsTotallyComplex E := h.2.1
  have hξ : ∀ w, ∃ ξ : E, ((τ w).1 ξ).im ≠ 0 := fun w => by
    by_contra hc
    push_neg at hc
    exact IsTotallyComplex.complexEmbedding_not_isReal (τ w).1
      (ComplexEmbedding.isReal_iff.2 (RingHom.ext fun x => Complex.conj_eq_iff_im.2 (hc x)))
  choose ξ hξ using hξ
  let s : InfinitePlace F → ℝ := fun w => (z w).im / ((τ w).1 (ξ w)).im
  let r : InfinitePlace F → ℝ := fun w => (z w).re - s w * ((τ w).1 (ξ w)).re
  let cR : ∀ w : InfinitePlace F, ℝ → w.Completion := fun w t =>
    (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w)).symm t
  refine ⟨∑ w, (adAt w (cR w (r w)) ⊗ₜ[F] (1 : E) + adAt w (cR w (s w)) ⊗ₜ[F] ξ w), ?_, fun v => ?_⟩
  · intro u hu
    rw [Finset.smul_sum]
    refine Finset.sum_eq_zero fun w _ => ?_
    rw [smul_add, smul_adAt_tmul u hu, smul_adAt_tmul u hu, add_zero]
  set_option synthInstance.maxHeartbeats 100000 in
    · rw [map_sum, Finset.sum_eq_single v]
      · rw [map_add (f := _), piInf_adAt_same, piInf_adAt_same]
        simp only [cR, ext_symm_real, map_one, mul_one]
        have h0 := hξ v
        apply Complex.ext
        · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, zero_mul, sub_zero, r]
          ring
        · simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, zero_add, zero_mul,
            add_zero, s]
          field_simp
      · intro w _ hw
        rw [map_add (f := _), piInf_adAt_ne (Ne.symm hw), piInf_adAt_ne (Ne.symm hw), add_zero]
      · intro hv; exact absurd (Finset.mem_univ v) hv

end GlobalTheory.PolRangeInf
