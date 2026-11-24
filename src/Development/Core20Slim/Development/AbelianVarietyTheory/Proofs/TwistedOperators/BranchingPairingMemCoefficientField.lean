module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueIsFunForm
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TensorMapDescent
public import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
public import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.InvVolConjLevelOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.MemHalfCosetSelf
public import Formalism.LocalRingCardinality.DataCoeff
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataParams₂
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.Columns.CoefModB
public import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
public import Formalism.LocalToGlobal.Divisibility.CoefMod
public import Formalism.LocalToGlobal.Divisibility.CoefModLemmas
public import Formalism.LocalToGlobal.Divisibility.LiftLat
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.InterlaceDifferenceShiftInvariant
public import Formalism.LocalToGlobal.KernelLattices.ThDistC
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Classical
public import Init.Core
public import Init.Data.Fin.Basic
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.GroupWithZero.Units.Lemmas
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.LinearMap
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MonoidAlgebra.Module
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.MvPolynomial.Monad
public import Mathlib.Algebra.Ring.CharZero
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.RingTheory.SimpleRing.Basic

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest Formalism.IndefR.WeilFull GlobalTheory.RowClaim

noncomputable section

namespace GlobalTheory.BrRat

open MvPolynomial Formalism.L2.Col Formalism.L2.Ker

section General

variable {ι : Type} [Fintype ι] {n : ℕ}

theorem projVV_of_mem {K : Type} [Field K] [CharZero K] (sg : ι → DomWeight n) (x : VV K sg) :
    Br.projVV sg x.1 = x := by
  have h := GlobalTheory.Proof.TensorMapDescent.eq_zero_of_fockB sg (Br.projVV sg x.1 - x) fun i => by
    rw [← fockBL_apply, Submodule.coe_sub, map_sub, fockBL_apply, fockBL_apply,
      GlobalTheory.Proof.TensorMapDescent.fockB_projVV_basis, sub_self]
  exact sub_eq_zero.mp h

theorem exists_map_eq {K : Type} [Field K] (φ : K →+* ℂ) {σ : Type} (P : MvPolynomial σ ℂ)
    (h : ∀ m, AddMonoidAlgebra.coeff P m ∈ Set.range φ) : ∃ P₀ : MvPolynomial σ K, map φ P₀ = P := by
  classical
  choose c hc using h
  refine ⟨∑ m ∈ P.support, monomial m (c m), ?_⟩
  conv_rhs => rw [P.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    simp [map_sum, map_monomial, hc]

theorem descend {K : Type} [Field K] [CharZero K] (φ : K →+* ℂ) (sg : ι → DomWeight n) (x : VV ℂ sg)
    (h : ∀ m, AddMonoidAlgebra.coeff x.1 m ∈ Set.range φ) : ∃ y : VV K sg, map φ y.1 = x.1 := by
  obtain ⟨P₀, hP⟩ := exists_map_eq φ x.1 h
  refine ⟨Br.projVV sg P₀, ?_⟩
  rw [← GlobalTheory.Proof.TensorMapDescent.projVV_map φ sg P₀, hP, projVV_of_mem]

theorem map_frDet {K : Type} [Field K] (φ : K →+* ℂ) (τ : ι) : map φ (frDet K n τ) = frDet ℂ n τ := by
  unfold frDet
  rw [RingHom.map_det]
  congr 1
  ext a s
  simp

theorem map_dualSubst {K : Type} [Field K] (φ : K →+* ℂ) (P : Pol K ι n) :
    map φ (dualSubst K ι n P) = dualSubst ℂ ι n (map φ P) := by
  have e : (map φ : Pol K ι n →+* Pol ℂ ι n).comp (dualSubst K ι n).toRingHom =
      (dualSubst ℂ ι n).toRingHom.comp (map φ) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [dualSubst]
    · intro v
      have hm : (Matrix.of fun a s : Fin n => (X (v.1, a, s) : Pol ℂ ι n)) =
          (map φ : Pol K ι n →+* Pol ℂ ι n).mapMatrix (Matrix.of fun a s : Fin n => (X (v.1, a, s) : Pol K ι n)) := by
        ext a s
        simp
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, dualSubst, aeval_X, map_X]
      rw [hm, ← RingHom.map_adjugate]
      rfl
  exact DFunLike.congr_fun e P

theorem isFunForm_map {K : Type} [Field K] (φ : K →+* ℂ) (σ : ι → DomWeight n) {F : VV K σ}
    {f : VV K fun τ => (σ τ).dual} (h : IsFunForm σ F f) :
    IsFunForm σ ⟨map φ F.1, GlobalTheory.Proof.TensorMapDescent.map_mem_VV φ σ _ F.2⟩
      ⟨map φ f.1, GlobalTheory.Proof.TensorMapDescent.map_mem_VV φ _ _ f.2⟩ := by
  unfold IsFunForm at h ⊢
  have h1 := congrArg (map φ) h
  simp only [map_mul, map_prod, map_pow, map_frDet, map_dualSubst] at h1
  exact h1

theorem covOf_eq (σ : ι → DomWeight n) (f : VV ℂ fun τ => (σ τ).dual) : covOf σ f = (funEquiv σ).symm f := by
  have hex : ∃ φ : (VV ℂ fun τ => (σ τ).dual) →ₗ[ℂ] VV ℂ σ, ∀ f, IsFunForm σ (φ f) f :=
    ⟨(funEquiv σ).symm.toLinearMap, fun f => (isFunForm_iff_eq σ _ f).2 (by simp)⟩
  have e : covOf σ f = hex.choose f := by rw [covOf, dite_eq_left hex]
  rw [e]
  apply (funEquiv σ).injective
  rw [LinearEquiv.apply_symm_apply]
  exact ((isFunForm_iff_eq σ _ f).1 (hex.choose_spec f)).symm

theorem covOf_desc {K : Type} [Field K] [CharZero K] (φ : K →+* ℂ) (σ : ι → DomWeight n)
    (f : VV ℂ fun τ => (σ τ).dual) (hf : ∀ m, AddMonoidAlgebra.coeff f.1 m ∈ Set.range φ) :
    ∃ F₀ : VV K σ, map φ F₀.1 = (covOf σ f).1 := by
  obtain ⟨f₀, hf₀⟩ := descend φ _ f hf
  refine ⟨(funEquiv σ).symm f₀, ?_⟩
  have h1 : IsFunForm σ ((funEquiv σ).symm f₀) f₀ := by
    have := isFunForm_funEquiv σ ((funEquiv σ).symm f₀)
    rwa [LinearEquiv.apply_symm_apply] at this
  have h2 := isFunForm_map φ σ h1
  have h4 : f = funEquiv σ ⟨map φ ((funEquiv σ).symm f₀).1, GlobalTheory.Proof.TensorMapDescent.map_mem_VV φ σ _ ((funEquiv σ).symm f₀).2⟩ := by
    rw [← (isFunForm_iff_eq σ _ _).1 h2]
    exact Subtype.ext hf₀.symm
  rw [covOf_eq, h4, LinearEquiv.symm_apply_apply]

theorem brPair_mem_range {K : Type} [Field K] [CharZero K] (φ : K →+* ℂ) (σ : ι → DomWeight n) {N : ℕ}
    (hN : N = n + 1) (Λ : ι → DomWeight N) (U : VV ℂ Λ) (V : VV ℂ fun τ => (σ τ).dual)
    (hU : ∀ m, AddMonoidAlgebra.coeff U.1 m ∈ Set.range φ) (hV : ∀ m, AddMonoidAlgebra.coeff V.1 m ∈ Set.range φ) :
    brPair σ hN Λ U V ∈ Set.range φ := by
  obtain ⟨U₀, hU₀⟩ := exists_map_eq φ U.1 hU
  obtain ⟨F₀, hF₀⟩ := covOf_desc φ σ V hV
  refine ⟨(extNormB K σ)⁻¹ * fockB (Br.brStdP hN Λ σ U₀ : Pol K ι n) F₀.1, ?_⟩
  rw [brPair, LinearMap.compl₁₂_apply, pairBK_apply, pairB_apply, ← hF₀, Br.brStd, LinearMap.comp_apply,
    Submodule.subtype_apply, ← hU₀, GlobalTheory.Proof.TensorMapDescent.branchingProjection_map, GlobalTheory.Proof.TensorMapDescent.fockB_map, map_mul, map_inv₀]
  congr 2
  unfold extNormB
  rw [map_prod]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [← GlobalTheory.Proof.TensorMapDescent.fockB_map, Formalism.L2.DIV.map_extremal]

end General

end GlobalTheory.BrRat

namespace GlobalTheory.RowClaim

theorem brPair_mem_coefField : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R) (large₂ : SizeData₂ D) (F : Face D A), HidaSetting large₂ R F → ch.Is → ch.FieldOK → ∀ (t : T) (Φ : ch.G.Datum), ch.S.SumOK t Φ → ∀ (U : VV ℂ (wt ch.G (.top D.R.m))) (V : VV ℂ (wt ch.G (.grid D.R.m D.R.m))), (∀ m, AddMonoidAlgebra.coeff U.1 m ∈ Set.range D.what₂.embLL) → (∀ m, AddMonoidAlgebra.coeff V.1 m ∈ Set.range D.what₂.embLL) → brPair (listedWt ch.G (.grid D.R.m D.R.m)) ch.G.sp.topDec.rank.symm (wt ch.G (.top D.R.m)) U V ∈ Set.range D.what₂.embLL := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R ch large₂ F _ _ _ t Φ _ U V hU hV
  haveI : CharZero D.what₂.LL := (RingHom.charZero_iff D.what₂.embLL.injective).mpr inferInstance
  exact GlobalTheory.BrRat.brPair_mem_range D.what₂.embLL _ _ _ U V hU hV

end GlobalTheory.RowClaim
