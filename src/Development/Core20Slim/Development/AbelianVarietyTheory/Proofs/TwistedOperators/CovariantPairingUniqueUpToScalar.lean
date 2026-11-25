module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqMulProdOfPartial
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLinearMapTensorOfPairing
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdjointIntertwinerDiscreteSeriesDescends
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.DerivedAdjoint
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFiniteDimensionalForallMapMemStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockPolynomialsLocallyFiniteRationalWeightsStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockOperatorsLieRepresentationCommuteStatement
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Init.Classical
public import Init.Core
public import Init.Data.Function
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Rat.Basic
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
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Module.Submodule.LinearMap
public import Mathlib.Algebra.Module.Submodule.Map
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Mathlib.Analysis.CStarAlgebra.Module.Defs
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Subspace
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Submodule
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Map
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Order.SetNotation
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.Tactic.LinearCombination.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Matrix GlobalTheory.Chain GlobalTheory.Chain.RealIt GlobalTheory.Chain.RealLine
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PairingLine

open GlobalTheory.PairingTensor

theorem exists_tensor {V A B H₁ H₂ : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup A] [Module ℂ A]
    [AddCommGroup B] [Module ℂ B] [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [NormedAddCommGroup H₂]
    [InnerProductSpace ℂ H₂] (i₁ : A →ₗ[ℂ] H₁) (i₂ : B →ₗ[ℂ] H₂) (h₁ : Function.Injective i₁)
    (h₂ : Function.Injective i₂) (φ : B → V →ₗ[ℂ] A)
    (hadj : ∀ P x, ∃ b, ∀ y, ⟪i₁ x, i₁ (φ y P)⟫_ℂ = ⟪i₂ y, i₂ b⟫_ℂ)
    (hE : ∀ P, ∃ E : Submodule ℂ A, FiniteDimensional ℂ E ∧ ∀ y, φ y P ∈ E) :
    ∃ f : V →ₗ[ℂ] A ⊗[ℂ] B, (∀ P y, contrR (innerₛₗ ℂ (i₂ y) ∘ₗ i₂) (f P) = φ y P) ∧
      ∀ z w : A ⊗[ℂ] B,
        (∀ y, contrR (innerₛₗ ℂ (i₂ y) ∘ₗ i₂) z = contrR (innerₛₗ ℂ (i₂ y) ∘ₗ i₂) w) → z = w := by
  let m : B → B →ₗ[ℂ] ℂ := fun y => (innerₛₗ ℂ (i₂ y)) ∘ₗ i₂
  have hm : ∀ y b, m y b = inner ℂ (i₂ y) (i₂ b) := fun _ _ => rfl
  have sepm : ∀ b, (∀ y, m y b = 0) → b = 0 := fun b h => by
    apply h₂
    rw [map_zero]
    exact inner_self_eq_zero.mp (h b)
  have sepR : ∀ z w : A ⊗[ℂ] B, (∀ y, contrR (m y) z = contrR (m y) w) → z = w := by
    intro z w h
    rw [← sub_eq_zero]
    exact eq_zero_of_contrR m sepm _ (fun y => by rw [map_sub, h, sub_self])
  choose ψ hψ using hadj
  have ex : ∀ P, ∃ z : A ⊗[ℂ] B, ∀ y, contrR (m y) z = φ y P := by
    intro P
    obtain ⟨E, hfin, hmem⟩ := hE P
    let e := stdOrthonormalBasis ℂ (E.map i₁)
    have ha : ∀ j, ∃ a : A, i₁ a = (e j : H₁) := fun j => by
      obtain ⟨a, -, ha⟩ := (e j).2
      exact ⟨a, ha⟩
    choose a ha using ha
    refine ⟨∑ j, a j ⊗ₜ[ℂ] ψ P (a j), fun y => ?_⟩
    apply h₁
    have := congrArg (fun v : E.map i₁ => (v : H₁))
      (e.sum_repr' ⟨i₁ (φ y P), Submodule.mem_map_of_mem (hmem y)⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_inner] at this
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← this, map_sum, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [contrR_tmul, map_smul, hm, ← hψ, ha]
  choose g hg using ex
  exact ⟨{ toFun := g
           map_add' := fun P Q => sepR _ _ fun y => by rw [map_add (f := _), hg, hg, hg, map_add (f := _)]
           map_smul' := fun s P => sepR _ _ fun y => by
             rw [map_smul, hg, hg, map_smul, RingHom.id_apply] }, hg, sepR⟩

theorem contrR_map_right {A B : Type} [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
    (m : B →ₗ[ℂ] ℂ) (b : Module.End ℂ B) (z : A ⊗[ℂ] B) :
    contrR m (TensorProduct.map LinearMap.id b z) = contrR (m ∘ₗ b) z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem contrR_neg {A B : Type} [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
    (m : B →ₗ[ℂ] ℂ) (z : A ⊗[ℂ] B) : contrR (-m) z = -contrR m z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy, neg_add]

theorem linear_eq_of_upq {p q : ℕ} {N : Type} [AddCommGroup N] [Module ℂ N] (F G : Mat p q →ₗ[ℂ] N)
    (h : ∀ Z ∈ upq p q, F Z = G Z) (Z : Mat p q) : F Z = G Z := by
  have e1 := h _ (GlobalTheory.AdjDescent.re_mem_upq Z)
  have e2 := h _ (GlobalTheory.AdjDescent.im_mem_upq Z)
  have hd := GlobalTheory.AdjDescent.decomp Z
  generalize Z + conjR Z = X at e1 hd
  generalize Complex.I • (Z - conjR Z) = Y at e2 hd
  subst hd
  simp only [map_add (f := _), map_smul, e1, e2]

theorem skew {p q : ℕ} {T : GrpData p q} (R : DSRep T) {Y : Mat p q} (hY : Y ∈ upq p q) (x y : R.HK.V) :
    ⟪R.ι (R.HK.act Y x), R.ι y⟫_ℂ = -⟪R.ι x, R.ι (R.HK.act Y y)⟫_ℂ := by
  have h1 := (R.der Y hY x).inner ℂ (R.der Y hY y)
  simp only [GlobalTheory.RealPar.DerivedAdjoint.inner_map, zero_smul, T.expt_zero, map_one,
    ContinuousLinearMap.one_apply] at h1
  have h2 := h1.unique (hasDerivAt_const (0 : ℝ) (inner ℂ (R.ι x) (R.ι y)))
  linear_combination h2

theorem exists_intw {p q r s : ℕ} {T₁ : GrpData p q} {T₂ : GrpData r s} (R₁ : DSRep T₁) (R₂ : DSRep T₂)
    (hA : Formalism.MainNotions.SchurIrreducible.AdmGK R₁.HK) (B : Pol p q r s →ₗ[ℂ] R₂.HK.V →ₛₗ[starRingEnd ℂ] R₁.HK.V)
    (hB : CoverW R₁ R₂ B) :
    ∃ f : Pol p q r s →ₗ[ℂ] R₁.HK.V ⊗[ℂ] R₂.HK.V,
      (∀ Z, f ∘ₗ fockAct1 p q r s Z = TensorProduct.map (R₁.HK.act Z) LinearMap.id ∘ₗ f) ∧
      (∀ Z, f ∘ₗ fockAct2 p q r s Z = TensorProduct.map LinearMap.id (R₂.HK.act Z) ∘ₗ f) ∧
      ∀ P y, contrR (innerₛₗ ℂ (R₂.ι y) ∘ₗ R₂.ι) (f P) = B P y := by
  have hsrc : ∀ Z P y, B (fockAct1 p q r s Z P) y = R₁.HK.act Z (B P y) := fun Z P y =>
    linear_eq_of_upq (B.flip y ∘ₗ (fockAct1 p q r s).flip P) (R₁.HK.act.flip (B P y))
      (fun Z hZ => hB.src Z hZ P y) Z
  have hlie := (GlobalTheory.T.fockOperators_lie_representation_commute p q r s).2.1
  obtain ⟨f, hf, sep⟩ := exists_tensor R₁.ι R₂.ι R₁.ι_inj R₂.ι_inj (fun y => B.flip y) hB.adj (fun P => by
    obtain ⟨W, hW, hP, hst⟩ := ((GlobalTheory.T.fock_polynomials_locallyFinite_rationalWeights p q r s).1 P).1
    obtain ⟨E, hE, hE'⟩ := GlobalTheory.T.exists_finiteDimensional_forall_map_mem' p q R₁.HK hA _ (fockAct1 p q r s) (fun Y Z _ _ => hlie Y Z) W hW hst
      (fun v _ => ((GlobalTheory.T.fock_polynomials_locallyFinite_rationalWeights p q r s).1 v).2)
    exact ⟨E, hE, fun y => hE' (B.flip y) (fun Z _ v => hsrc Z v y) P hP⟩)
  simp only [LinearMap.flip_apply] at hf
  refine ⟨f, fun Z => ?_, fun Z => ?_, hf⟩
  · refine LinearMap.ext fun P => sep _ _ fun y => ?_
    rw [LinearMap.comp_apply, LinearMap.comp_apply, contrR_map, hf, hf, hsrc]
  · refine LinearMap.ext fun P => ?_
    refine linear_eq_of_upq (f ∘ₗ (fockAct2 p q r s).flip P)
      (((LinearMap.lTensorHom R₁.HK.V).comp R₂.HK.act).flip (f P)) (fun Z hZ => ?_) Z
    refine sep _ _ fun y => ?_
    change contrR _ (f (fockAct2 p q r s Z P)) = contrR _ (TensorProduct.map LinearMap.id (R₂.HK.act Z) (f P))
    have e : (innerₛₗ ℂ (R₂.ι y) ∘ₗ R₂.ι) ∘ₗ R₂.HK.act Z = -(innerₛₗ ℂ (R₂.ι (R₂.HK.act Z y)) ∘ₗ R₂.ι) := by
      refine LinearMap.ext fun b => ?_
      change ⟪R₂.ι y, R₂.ι (R₂.HK.act Z b)⟫_ℂ = -⟪R₂.ι (R₂.HK.act Z y), R₂.ι b⟫_ℂ
      rw [skew R₂ hZ, neg_neg]
    rw [contrR_map_right, e, contrR_neg, hf, hf]
    exact eq_neg_of_add_eq_zero_left (hB.tgt Z hZ P y)

theorem pairing_line : ∀ (X : ProvA) (p q r s : ℕ) (lam : Ix p q → ℚ) (lam' : Ix r s → ℚ), Formalism.MainNotions.SchurIrreducible.AdmGK (X.ds p q lam).HK → Formalism.MainNotions.SchurIrreducible.ARiiiLine X lam lam' → ∃ B₀ : Pol p q r s → (X.ds r s lam').HK.V → (X.ds p q lam).HK.V, ∀ B : Pol p q r s →ₗ[ℂ] (X.ds r s lam').HK.V →ₛₗ[starRingEnd ℂ] (X.ds p q lam).HK.V, CoverW (X.ds p q lam) (X.ds r s lam') B → ∃ c : ℂ, ∀ P y, B P y = c • B₀ P y := by
  intro X p q r s lam lam' hA hL
  obtain ⟨f₀, -, -, hf₀⟩ := hL
  refine ⟨fun P y => contrR (innerₛₗ ℂ ((X.ds r s lam').ι y) ∘ₗ (X.ds r s lam').ι) (f₀ P), fun B hB => ?_⟩
  obtain ⟨f, h1, h2, hf⟩ := exists_intw _ _ hA B hB
  obtain ⟨c, hc⟩ := hf₀ f ⟨h1, h2⟩
  refine ⟨c, fun P y => ?_⟩
  rw [← hf, hc, LinearMap.smul_apply, map_smul]

end GlobalTheory.PairingLine
