module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatIffOfSelfDual
public import Development.AbelianVarietyTheory.Definitions.Foundations.ClassMassEqSumOfBijective
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FlatSpaceComponents
public import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.EmbRelExistsUnique
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Formalism.LocalToGlobal.HermitianColumns.InLocalDiscriminantKernel
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.SatakeDualWeyl.Statement
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.ByCases
public import Init.Core
public import Init.Data.Function
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Notation.Pi.Basic
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Equiv
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Finsupp.SMul
public import Mathlib.Data.Finsupp.Single
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.Logic.Function.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Maps

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Matrix
open Formalism.L2.DIV (Pl UA)
open Formalism.L2.Theta (GA GfC finHom frameMat)
open Formalism.IndefR.Lev (EAf finE)
open Formalism.IndefR.Datum (IsSelfDualC)
open Formalism.UG (cT hform)
open GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents GlobalTheory.AdIsom
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdIsomCorrection

section Algebra

variable {A : Type} [CommRing A] (σ : A →+* A)

theorem cT_mul_rect {l m n : ℕ} (M : Matrix (Fin l) (Fin m) A) (N : Matrix (Fin m) (Fin n) A) :
    cT σ (M * N) = cT σ N * cT σ M := by
  rw [cT, Matrix.map_mul, transpose_mul]
  rfl

theorem gram_of_form {m n : ℕ} (J' : Matrix (Fin m) (Fin m) A) (J : Matrix (Fin n) (Fin n) A)
    (x : Matrix (Fin m) (Fin n) A)
    (h : ∀ i j, hform σ J' (x *ᵥ Pi.single i 1) (x *ᵥ Pi.single j 1) = J i j) :
    cT σ x * J' * x = J := by
  ext i j
  rw [← h i j]
  simp only [hform, mulVec_single_one, Matrix.mul_apply, cT, transpose_apply, map_apply, col_apply, Finset.sum_mul]
  exact Finset.sum_comm

theorem hform_single {n : ℕ} (J : Matrix (Fin n) (Fin n) A) (i j : Fin n) :
    hform σ J (Pi.single i 1) (Pi.single j 1) = J i j := by
  simp [hform, Pi.single_apply, apply_ite σ]

theorem exists_unitary {m n : ℕ} (J' : Matrix (Fin m) (Fin m) A) (J : Matrix (Fin n) (Fin n) A)
    (x y : Matrix (Fin m) (Fin n) A) (y' : Matrix (Fin n) (Fin m) A) (h1 : y * y' = 1) (h2 : y' * y = 1)
    (hb : Function.Surjective x.mulVec) (hx : cT σ x * J' * x = J) (hy : cT σ y * J' * y = J) :
    ∃ g : GL (Fin m) A, cT σ g.1 * J' * g.1 = J' ∧ g.1 * y = x := by
  have hu : IsUnit (x * y') := by
    rw [← Matrix.mulVec_surjective_iff_isUnit]
    intro v
    obtain ⟨w, rfl⟩ := hb v
    exact ⟨y *ᵥ w, by rw [mulVec_mulVec, Matrix.mul_assoc, h2, Matrix.mul_one]⟩
  refine ⟨hu.unit, ?_, ?_⟩
  · rw [hu.unit_spec, cT_mul_rect]
    have e : cT σ y' * cT σ y = 1 := by
      rw [← cT_mul_rect, h1, cT, Matrix.map_one _ (map_zero σ) (map_one σ), transpose_one]
    calc cT σ y' * cT σ x * J' * (x * y') = cT σ y' * (cT σ x * J' * x) * y' := by simp only [Matrix.mul_assoc]
      _ = (cT σ y' * cT σ y) * J' * (y * y') := by rw [hx, ← hy]; simp only [Matrix.mul_assoc]
      _ = J' := by rw [e, h1, Matrix.one_mul, Matrix.mul_one]
  · rw [hu.unit_spec, Matrix.mul_assoc, h2, Matrix.mul_one]

end Algebra

variable {D : D7}

theorem exists_finE (V : HSp D) (g : GL (Fin V.rank) (EAf D)) (hg : g ∈ UA D.sp.cm V.gram) :
    ∃ k ∈ GfC V, finE V k = g := by
  obtain ⟨b, hb⟩ := (GlobalTheory.Mass.swapPts (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram).surjective ⟨g, hg⟩
  obtain ⟨h1, h2⟩ := GlobalTheory.Mass.parts_spec D.sp.cm.sig V.gram
  obtain ⟨k, k1, k2⟩ := h2 1 b.1
  refine ⟨⟨k, (h1 k).2 ⟨k1 ▸ one_mem _, k2 ▸ b.2⟩⟩, k1, ?_⟩
  have e := congrArg Subtype.val hb
  have e2 := GlobalTheory.Mass.coe_swapPts (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram b
  refine Eq.trans ?_ (e2.symm.trans e)
  exact congrArg (Formalism.UG.bc (Formalism.IndefR.Lev.swapAE D)) k2

theorem mA_mul (X Y Z : HSp D) (f : X.V →ₗ[D.host.E] Y.V) (g : Y.V →ₗ[D.host.E] Z.V) :
    mA Z Y g * mA Y X f = mA Z X (g.comp f) := by
  rw [mA, mA, mA, ← Matrix.map_mul, frameMat, frameMat, frameMat, LinearMap.toMatrix_comp X.frame Y.frame Z.frame]

theorem mA_id (X : HSp D) : mA X X LinearMap.id = 1 := by
  rw [mA, frameMat, LinearMap.toMatrix_id, Matrix.map_one _ (RingHom.map_zero _) (RingHom.map_one _)]

theorem vA_frame (X : HSp D) (i : Fin X.rank) : vA X (X.frame i) = Pi.single i 1 := by
  funext j
  have : Formalism.L2.Herm.crd X (X.frame i) j = X.frame.repr (X.frame i) j := rfl
  rw [vA, this, Module.Basis.repr_self, Finsupp.single_apply, Pi.single_apply]
  by_cases h : i = j
  · rw [if_pos h, if_pos h.symm, RingHom.map_one]
  · rw [if_neg h, if_neg (Ne.symm h), RingHom.map_zero]

theorem gram_mA (Y Y' : HSp D) (f : Y.V →ₗ[D.host.E] Y'.V) (hf : HSpace.IsIsomEmb Y Y' f) :
    HMul.hMul (HMul.hMul (cT (cjA D) (mA Y' Y f)) (Y'.gram.map (inc D))) (mA Y' Y f) = Y.gram.map (inc D) := by
  refine gram_of_form _ _ _ _ fun i j => ?_
  rw [← vA_frame, ← vA_frame, mA_mulVec_vA, mA_mulVec_vA, ← hA_eq, hA_vA, HSpace.hD, hf]
  rfl

theorem correction_of_transport : ∀ D : D7, TransportSt D → CorrectionSt D := by
  intro D hT Y Y' io hio Λ Λ' hΛ hΛ' S hS n be be' hbe hbe'
  have hr : Y.rank = Y'.rank := by rw [← Y.rank_eq, ← Y'.rank_eq, io.finrank_eq]
  obtain ⟨⟨x, hx⟩, -⟩ := hT Y Y' hr Λ Λ' hΛ hΛ' S hS n be be' hbe hbe'
  obtain ⟨g, hg, hgx⟩ := exists_unitary (cjA D) (Y'.gram.map (inc D)) (Y.gram.map (inc D)) x
    (mA Y' Y io.toLinearMap) (mA Y Y' io.symm.toLinearMap)
    (by rw [mA_mul, LinearEquiv.comp_symm, mA_id]) (by rw [mA_mul, LinearEquiv.symm_comp, mA_id]) hx.1.1.2
    (gram_of_form _ _ _ _ fun i j => (hx.1.2 _ _).trans (hform_single _ _ i j)) (gram_mA Y Y' _ hio)
  obtain ⟨k, hk, e⟩ := exists_finE Y' g hg
  refine ⟨k, hk, ?_⟩
  rw [e, hgx]
  exact hx

end GlobalTheory.AdIsomCorrection
