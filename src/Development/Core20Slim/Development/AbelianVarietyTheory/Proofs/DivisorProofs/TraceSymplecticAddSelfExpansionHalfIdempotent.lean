module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsNotRelZero
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareTriple
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareStanding
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.NonUnitalHom
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Trace.Basic
public import Mathlib.RingTheory.Trace.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.VacExpand

theorem symp_add_self_expand : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) {n d : ℕ} (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n)
    (Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d) (r s r' s' : ℕ),
    B.IsGood σ → X.IsHerm σ B r s → Y.IsSkew σ B r' s' → ∀ θ : E, θ + σ θ = 1 →
    ∀ γ γ' : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)),
      GlobalTheory.WeilM.symp (R := AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (inclR (F := F) (AF F) θ) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J)
                   (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J) (γ + γ') (γ + γ') =
        GlobalTheory.WeilM.symp (R := AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (inclR (F := F) (AF F) θ) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J)
                     (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J) γ γ +
          GlobalTheory.WeilM.symp (R := AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (inclR (F := F) (AF F) θ) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J)
            (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J) γ' γ' +
          2 * GlobalTheory.WeilM.symp (R := AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (inclR (F := F) (AF F) θ) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J)
            (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J) γ γ' +
          GlobalTheory.WeilM.symp (R := AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (-1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J)
            (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J) γ γ' := by
  intro F E _ _ _ _ _ σ B n d X Y r s r' s' hB hX hY θ hθ γ γ'
  have hinv : ∀ x : E, σ (σ x) = x := by
    intro x
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply τ.injective
    rw [hB.cm.2.2.2, hB.cm.2.2.2, star_star]
  have hcc : ∀ z : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ z) = z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA, hinv]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  have hcI : ∀ x : E, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ (inclR (F := F) (AF F) x) = inclR (F := F) (AF F) (σ x) := by
    intro x; simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA, inclR]
  let e : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E) ≃ₐ[AF F] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E) :=
    AlgEquiv.ofAlgHom (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (AlgHom.ext hcc) (AlgHom.ext hcc)
  have htr : ∀ z, Algebra.trace (AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ z) =
      Algebra.trace (AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) z := fun z => Algebra.trace_eq_of_algEquiv e z
  set A := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J with hA
  set Bm := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J with hBm
  set c := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ with hc
  have key : ∀ f : Fin n → Fin d → Fin n → Fin d → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E),
      ∑ i, ∑ j, ∑ k, ∑ l, f i j k l = ∑ k, ∑ l, ∑ i, ∑ j, f i j k l := by
    intro f
    calc _ = ∑ i, ∑ k, ∑ j, ∑ l, f i j k l := Finset.sum_congr rfl fun i _ => Finset.sum_comm
      _ = ∑ k, ∑ i, ∑ j, ∑ l, f i j k l := Finset.sum_comm
      _ = ∑ k, ∑ i, ∑ l, ∑ j, f i j k l :=
          Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => Finset.sum_comm
      _ = ∑ k, ∑ l, ∑ i, ∑ j, f i j k l := Finset.sum_congr rfl fun k _ => Finset.sum_comm
  have hconj : ∀ x y : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)),
      c (GlobalTheory.WeilM.hTens c A Bm x y) = -GlobalTheory.WeilM.hTens c A Bm y x := by
    intro x y
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [GlobalTheory.WeilM.hTens, map_sum, map_mul, hcc, hA, hBm, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM, Matrix.map_apply, hcI,
      hX.herm, hY.skew, map_neg]
    rw [key, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hexp : ∀ x y : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)),
      GlobalTheory.WeilM.hTens c A Bm (x + y) (x + y) = GlobalTheory.WeilM.hTens c A Bm x x + GlobalTheory.WeilM.hTens c A Bm y y +
        GlobalTheory.WeilM.hTens c A Bm x y + GlobalTheory.WeilM.hTens c A Bm y x := by
    intro x y
    simp only [GlobalTheory.WeilM.hTens, Matrix.add_apply, map_add (f := _), add_mul, mul_add, Finset.sum_add_distrib]
    ring
  have hθ' : σ θ = 1 - θ := eq_sub_of_add_eq' hθ
  have hcΘ : c (inclR (F := F) (AF F) θ) = 1 - inclR (F := F) (AF F) θ := by
    rw [hc, hcI, hθ', map_sub, map_one]
  have hswap : Algebra.trace (AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (inclR (F := F) (AF F) θ * GlobalTheory.WeilM.hTens c A Bm γ' γ) =
      Algebra.trace (AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (inclR (F := F) (AF F) θ * GlobalTheory.WeilM.hTens c A Bm γ γ') +
      Algebra.trace (AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) ((-1) * GlobalTheory.WeilM.hTens c A Bm γ γ') := by
    have h1 : GlobalTheory.WeilM.hTens c A Bm γ' γ = -c (GlobalTheory.WeilM.hTens c A Bm γ γ') := by rw [hconj]; ring
    have h2 : inclR (F := F) (AF F) θ * GlobalTheory.WeilM.hTens c A Bm γ' γ =
        -c ((1 - inclR (F := F) (AF F) θ) * GlobalTheory.WeilM.hTens c A Bm γ γ') := by
      rw [h1, map_mul, ← hcΘ, hcc]; ring
    rw [h2, map_neg, htr]
    simp only [sub_mul, one_mul, neg_mul, map_sub, map_neg]
    ring
  simp only [GlobalTheory.WeilM.symp]
  rw [hexp, mul_add, mul_add, mul_add, map_add (f := _), map_add (f := _), map_add (f := _), hswap]
  ring

end GlobalTheory.VacExpand
