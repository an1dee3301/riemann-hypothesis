module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.HermitianHassePrincipleHolds
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsZeroCoordNeZero
public import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.PosIndexMapEqCardOfCongrDiagonal
public import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.ExistsOrthogonalBasisDotProductApplyEq
public import Formalism.LocalToGlobal.ProjectiveLattices.RdOrbIntOfLatZ
public import Init.BinderNameHint
public import Init.Classical
public import Init.Core
public import Init.Data.Fin.Basic
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.NeZero
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.NonUnitalHom
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Units.Lemmas
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fin.SuccPred
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.NNRat.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Rat.Defs
public import Mathlib.Data.Rat.Init
public import Mathlib.FieldTheory.Separable
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.CMField
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Lattice
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Tactic.Linarith.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature

@[expose] public section

open Matrix NumberField
open scoped ComplexConjugate

namespace PositivityTheory.Rg.Sw.Glob.WLt

open ReciprocityTheory.ChartRestriction.G

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem cc_cc (t : E) : FD.cc (FD.cc t) = t := IsCMField.complexConj_apply_apply E t

theorem emb_cc (τ : E →+* ℂ) (t : E) : τ (FD.cc t) = conj (τ t) := IsCMField.complexEmbedding_complexConj E τ t

theorem exists_skew : ∃ θ : E, θ ≠ 0 ∧ FD.cc θ = -θ := by
  by_contra hne
  push Not at hne
  apply IsCMField.complexConj_ne_one E
  ext t
  by_contra ht
  have h1 : t - FD.cc t ≠ 0 := sub_ne_zero.mpr (Ne.symm ht)
  apply hne _ h1
  show IsCMField.complexConj E (t - FD.cc t) = -(t - FD.cc t)
  rw [map_sub]
  change FD.cc t - FD.cc (FD.cc t) = _
  rw [cc_cc]
  ring

theorem emb_real (τ : E →+* ℂ) {t : E} (ht : FD.cc t = t) : τ t = ((τ t).re : ℂ) := by
  have h := emb_cc τ t
  rw [ht] at h
  apply Complex.ext
  · simp
  · have := congrArg Complex.im h
    simp only [Complex.conj_im] at this
    simp only [Complex.ofReal_im]
    linarith

theorem iso_diag {r : ℕ} (g : Fin (r + 1) → E) (hr : 2 ≤ r) (hg : ∀ i, FD.cc (g i) = g i) (hg0 : ∀ i, g i ≠ 0)
    (hs : ∀ τ : E →+* ℂ, (∃ i, 0 < (τ (g i)).re) ∧ (∃ j, (τ (g j)).re < 0)) :
    ∃ z : Fin (r + 1) → E, z ≠ 0 ∧ z ⬝ᵥ diagonal g *ᵥ (FD.cc ∘ z) = 0 := by
  obtain ⟨θ, hθ0, hθ⟩ := exists_skew (E := E)
  have hF : ∀ t : E, IsCMField.complexConj E t = t ↔ ∃ s : maximalRealSubfield E, algebraMap (maximalRealSubfield E) E s = t :=
    fun t => (IsCMField.complexConj_eq_self_iff E t).trans ⟨fun h => ⟨⟨t, h⟩, rfl⟩, by rintro ⟨s, rfl⟩; exact s.2⟩
  have hne : ∀ (τ : E →+* ℂ) (i : Fin (r + 1)), (τ (g i)).re ≠ 0 := by
    intro τ i h
    have h1 := emb_real τ (hg i)
    rw [h, Complex.ofReal_zero] at h1
    exact hg0 i ((map_eq_zero τ).1 h1)
  obtain ⟨z, hz⟩ := GlobalTheory.HermGlobal.exists_represent (σ := IsCMField.complexConj E) (IsCMField.complexConj_apply_apply E) hF
    hθ0 hθ hr (g := fun i => g i.succ) (fun i => hg _) (fun i => hg0 _) (b := -g 0)
    (by show IsCMField.complexConj E (-g 0) = -g 0; rw [map_neg]; exact congrArg Neg.neg (hg 0))
    (neg_ne_zero.mpr (hg0 0)) (by
      intro τ _
      obtain ⟨⟨i, hi⟩, ⟨j, hj⟩⟩ := hs τ
      have hb : (τ (-g 0)).re = -(τ (g 0)).re := by simp
      rcases lt_or_gt_of_ne (hne τ 0) with h0 | h0
      ·
        have hi0 : i ≠ 0 := by rintro rfl; linarith
        obtain ⟨i', rfl⟩ := Fin.exists_succ_eq.mpr hi0
        exact ⟨i', by simp only [hb]; constructor <;> intro _ <;> linarith⟩
      · have hj0 : j ≠ 0 := by rintro rfl; linarith
        obtain ⟨j', rfl⟩ := Fin.exists_succ_eq.mpr hj0
        exact ⟨j', by simp only [hb]; constructor <;> intro h <;> linarith⟩)
  refine ⟨Fin.cons 1 z, fun h => one_ne_zero (congrFun h 0), ?_⟩
  have key : (Fin.cons 1 z : Fin (r + 1) → E) ⬝ᵥ diagonal g *ᵥ (FD.cc ∘ Fin.cons 1 z) =
      g 0 + z ⬝ᵥ diagonal (fun i => g i.succ) *ᵥ (FD.cc ∘ z) := by
    simp only [dotProduct, mulVec_diagonal, Fin.sum_univ_succ, Function.comp_apply, Fin.cons_zero, Fin.cons_succ]
    have : FD.cc (1 : E) = 1 := map_one (IsCMField.complexConj E)
    rw [this]
    ring
  rw [key]
  have hz' : z ⬝ᵥ diagonal (fun i => g i.succ) *ᵥ (FD.cc ∘ z) = -g 0 := hz
  rw [hz']
  ring

end PositivityTheory.Rg.Sw.Glob.WLt
