module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.WeylDualWeylLatticesAgreeOfLowestAlcove
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SubstitutionAdjoint
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ThDistC
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.JetOpIdentityOfEntire
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.StandardRankOneLatticeOfLocal
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RhoDetPrimeEqMuTildeMulChiPow
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.Foundations.ExistsUnitaryMulTriangular
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.GaloisGeometry.TrueWtAddSSNonneg
public import Formalism.GradedWeylDivisibility.StatementD
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalToGlobal.Columns.AbelianHostFieldConditions
public import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
public import Formalism.LocalToGlobal.Divisibility.CoefMod
public import Formalism.LocalToGlobal.Divisibility.Tuples
public import Formalism.LocalToGlobal.KernelLattices.ThDistC
public import Formalism.LocalToGlobal.ProjectiveLattices.SubConstMemOrig
public import Init.Core
public import Init.Data.Sum.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.PropLemmas
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.NonUnitalHom
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MonoidAlgebra.Module
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.MvPolynomial.Monad
public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finsupp.Basic
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Function
public import Mathlib.Data.Set.Operations
public import Mathlib.Data.Sum.Basic
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker 

namespace GlobalTheory.KerT.RatLaw

section Alg

open MvPolynomial

variable {K : Type} [Field K] {ι : Type} {a b : ℕ}

abbrev tabFn (J : (DVar ι a b →₀ ℕ) → K) : MvPolynomial (DVar ι a b) K →ₗ[K] K := (basisMonomials (DVar ι a b) K).constr K J

abbrev subst (g : ι → Matrix (Fin a) (Fin a) K) (h : ι → Matrix (Fin b) (Fin b) K) (k : DVar ι a b) : MvPolynomial (DVar ι a b) K :=
  ∑ i : Fin b, ∑ j : Fin a, C (h k.1 i k.2.1 * g k.1 k.2.2 j) * X (k.1, i, j)

theorem jetLin_monomial (J : (DVar ι a b →₀ ℕ) → K) (m : (ι × Fin b × Fin b) ⊕ DVar ι a b →₀ ℕ) :
    jetLin J (monomial m 1) = monomial (m.comapDomain Sum.inl Sum.inl_injective.injOn)
      (J (m.comapDomain Sum.inr Sum.inr_injective.injOn)) := by
  have := (basisMonomials ((ι × Fin b × Fin b) ⊕ DVar ι a b) K).constr_basis K (fun m =>
    (monomial (m.comapDomain Sum.inl Sum.inl_injective.injOn) (J (m.comapDomain Sum.inr Sum.inr_injective.injOn)) : Pol K ι b)) m
  rw [coe_basisMonomials] at this
  exact this

theorem tabFn_monomial (J : (DVar ι a b →₀ ℕ) → K) (m : DVar ι a b →₀ ℕ) : tabFn J (monomial m 1) = J m := by
  have := (basisMonomials (DVar ι a b) K).constr_basis K J m
  rwa [coe_basisMonomials] at this

theorem monomial_split {α β : Type} (m : α ⊕ β →₀ ℕ) :
    (monomial m 1 : MvPolynomial (α ⊕ β) K) = rename Sum.inl (monomial (m.comapDomain Sum.inl Sum.inl_injective.injOn) 1) *
      rename Sum.inr (monomial (m.comapDomain Sum.inr Sum.inr_injective.injOn) 1) := by
  rw [rename_monomial, rename_monomial, monomial_mul, one_mul]
  congr 2
  ext (x | x)
  · rw [Finsupp.add_apply, Finsupp.mapDomain_apply_of_injective Sum.inl_injective, Finsupp.mapDomain_notin_range _ _ (by simp)]
    simp
  · rw [Finsupp.add_apply, Finsupp.mapDomain_apply_of_injective Sum.inr_injective, Finsupp.mapDomain_notin_range _ _ (by simp)]
    simp

theorem jetLin_mul (J : (DVar ι a b →₀ ℕ) → K) (p : Pol K ι b) (q : MvPolynomial (DVar ι a b) K) :
    jetLin J (rename Sum.inl p * rename Sum.inr q) = tabFn J q • p := by
  induction p using MvPolynomial.induction_on' with
  | add p p' h h' => rw [map_add (f := _), add_mul, map_add (f := _), h, h', smul_add]
  | monomial m c =>
    induction q using MvPolynomial.induction_on' with
    | add q q' h h' => rw [map_add (f := _), mul_add, map_add (f := _), h, h', map_add (f := _), add_smul]
    | monomial m' c' =>
      have e : ∀ {σ : Type} (m : σ →₀ ℕ) (c : K), (monomial m c : MvPolynomial σ K) = c • monomial m 1 := fun m c => by
        rw [smul_monomial, smul_eq_mul, mul_one]
      have e1 : (m.mapDomain Sum.inl + m'.mapDomain Sum.inr).comapDomain Sum.inl Sum.inl_injective.injOn = m := by
        ext x
        rw [Finsupp.comapDomain_apply, Finsupp.add_apply, Finsupp.mapDomain_apply_of_injective Sum.inl_injective,
          Finsupp.mapDomain_notin_range _ _ (by simp), add_zero]
      have e2 : (m.mapDomain Sum.inl + m'.mapDomain Sum.inr).comapDomain Sum.inr Sum.inr_injective.injOn = m' := by
        ext x
        rw [Finsupp.comapDomain_apply, Finsupp.add_apply, Finsupp.mapDomain_apply_of_injective Sum.inr_injective,
          Finsupp.mapDomain_notin_range _ _ (by simp), zero_add]
      rw [rename_monomial, rename_monomial, monomial_mul, e _ (c * c'), map_smul, jetLin_monomial, e1, e2, e m' c', map_smul,
        tabFn_monomial, smul_monomial, smul_monomial]
      congr 1
      simp only [smul_eq_mul]
      ring

theorem jetLin_right {J J' : (DVar ι a b →₀ ℕ) → K} (φ : DVar ι a b → MvPolynomial (DVar ι a b) K)
    (hJ : ∀ m, J' m = tabFn J (aeval φ (monomial m (1 : K)))) (Q : MvPolynomial ((ι × Fin b × Fin b) ⊕ DVar ι a b) K) :
    jetLin J' Q = jetLin J (aeval (Sum.elim (fun v => X (Sum.inl v)) fun k => rename Sum.inr (φ k)) Q) := by
  refine LinearMap.congr_fun (g := jetLin J ∘ₗ (aeval (Sum.elim (fun v => X (Sum.inl v)) fun k => rename Sum.inr (φ k))).toLinearMap)
    ((basisMonomials _ K).ext fun m => ?_) Q
  rw [coe_basisMonomials]
  simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply]
  rw [monomial_split, jetLin_mul, tabFn_monomial, hJ, map_mul, aeval_rename, aeval_rename, ← jetLin_mul]
  congr 2
  · refine AlgHom.congr_fun (φ₁ := rename Sum.inl) (MvPolynomial.algHom_ext fun v => ?_) _
    simp
  · refine AlgHom.congr_fun (φ₁ := (rename Sum.inr).comp (aeval φ)) (MvPolynomial.algHom_ext fun v => ?_) _
    simp

theorem jetLin_left (J : (DVar ι a b →₀ ℕ) → K) (ψ : Pol K ι b →ₐ[K] Pol K ι b)
    (Q : MvPolynomial ((ι × Fin b × Fin b) ⊕ DVar ι a b) K) :
    jetLin J (aeval (Sum.elim (fun v => rename Sum.inl (ψ (X v))) fun k => X (Sum.inr k)) Q) = ψ (jetLin J Q) := by
  refine LinearMap.congr_fun (f := jetLin J ∘ₗ (aeval (Sum.elim (fun v => rename Sum.inl (ψ (X v))) fun k => X (Sum.inr k))).toLinearMap)
    (g := ψ.toLinearMap ∘ₗ jetLin J) ((basisMonomials _ K).ext fun m => ?_) Q
  rw [coe_basisMonomials]
  simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply]
  rw [monomial_split, jetLin_mul, map_smul, map_mul, aeval_rename, aeval_rename, ← jetLin_mul]
  congr 2
  · refine AlgHom.congr_fun (φ₂ := (rename Sum.inl).comp ψ) (MvPolynomial.algHom_ext fun v => ?_) _
    simp
  · refine AlgHom.congr_fun (φ₂ := rename Sum.inr) (MvPolynomial.algHom_ext fun v => ?_) _
    simp

theorem subD_subst (g : ι → Matrix (Fin a) (Fin a) K) (h : ι → Matrix (Fin b) (Fin b) K) (P : Pol K ι a) :
    aeval (Sum.elim (fun v => X (Sum.inl v)) fun k => rename Sum.inr (subst g h k)) (subD K ι a b P) =
      (aeval (Sum.elim (fun v => rename Sum.inl (Formalism.GradedWeylDivisibility.blockAct K h (X v : Pol K ι b))) fun k => X (Sum.inr k))
        (subD K ι a b (Formalism.GradedWeylDivisibility.blockAct K g P)) : MvPolynomial ((ι × Fin b × Fin b) ⊕ DVar ι a b) K) := by
  refine AlgHom.congr_fun (φ₁ := (aeval _).comp (subD K ι a b))
    (φ₂ := (aeval _).comp ((subD K ι a b).comp (Formalism.GradedWeylDivisibility.blockAct K g))) (MvPolynomial.algHom_ext fun v => ?_) P
  obtain ⟨τ, α, s⟩ := v
  by_cases hs : s.1 < b
  · set_option synthInstance.maxHeartbeats 100000 in
    simp only [AlgHom.comp_apply, Formalism.GradedWeylDivisibility.blockAct, subD, aeval_X, map_sum, map_mul, algHom_C, dif_pos hs, Sum.elim_inl,
      Sum.elim_inr, rename_X, algebraMap_eq, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm, Finset.sum_congr rfl fun _ _ => Finset.sum_comm, Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun β _ => ?_
    ring
  · simp [Formalism.GradedWeylDivisibility.blockAct, subD, dif_neg hs]

theorem blockAct_frDet (g : ι → Matrix (Fin a) (Fin a) K) (τ : ι) :
    Formalism.GradedWeylDivisibility.blockAct K g (frDet K a τ) = C (g τ).det * frDet K a τ := by
  rw [frDet, AlgHom.map_det, RingHom.map_det, ← Matrix.det_mul]
  congr 1
  ext1 α s
  simp [Formalism.GradedWeylDivisibility.blockAct, Matrix.mul_apply]

variable [Fintype ι]

theorem jetMap_subst {J J' : (DVar ι a b →₀ ℕ) → K} (g : ι → Matrix (Fin a) (Fin a) K) (h : ι → Matrix (Fin b) (Fin b) K)
    (hJ : ∀ m, J' m = tabFn J (aeval (subst g h) (monomial m (1 : K)))) (n : ι → ℕ)
    (P : Pol K ι a) :
    jetMap J' n P = (∏ τ, (g τ).det ^ n τ) • Formalism.GradedWeylDivisibility.blockAct K h (jetMap J n (Formalism.GradedWeylDivisibility.blockAct K g P)) := by
  simp only [jetMap, LinearMap.comp_apply, AlgHom.toLinearMap_apply, LinearMap.mulRight_apply]
  rw [jetLin_right _ hJ, subD_subst, jetLin_left, ← map_smul, ← map_smul, ← map_smul, map_mul, map_prod]
  congr 3
  simp only [map_pow, blockAct_frDet, mul_pow, Finset.prod_mul_distrib, smul_eq_C_mul, map_prod]
  ring



end Alg

section Jet

open MvPolynomial


variable {X : Fields} {a b : ℕ}







end Jet

section Mu

open Formalism.L2.Host (HChar ordF)



variable {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S}
  {cst : LocCst X (rowSG Pr sel mu)} {σ₀ : X.K →+* ℂ} {e : Fin R.m → X.Tau → ℚ} {m0 : Fin R.m → HChar X.E} {eta ξ : HChar X.E}







end Mu




end GlobalTheory.KerT.RatLaw
