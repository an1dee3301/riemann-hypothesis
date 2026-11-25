module

public import Mathlib
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RatVInjective
public import Development.Core20Slim.CompanionTheory.AutomorphicTheory.SiegelWeilFiniteness.Bridge
public import Development.Core20Slim.GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Assembly
public import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
public import Formalism.SatakeDualWeyl.Statement
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.Core20Slim.GroundTheory.AutomorphicForms.HermitianExistenceLocal
public import Development.Core20Slim.GroundTheory.AutomorphicForms.HermitianSpaces
public import Development.Core20Slim.GroundTheory.AutomorphicForms.QuadraticConj
public import Development.Core20Slim.GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Objects
public import Development.Core20Slim.GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.SecondCountableTopologyArchUnitary
public import Development.Core20Slim.GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsComplementForm
public import Development.Core20Slim.GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsHyperbolicPairs
public import Init.Core
public import Init.Data.Fin.Basic
public import Init.Data.Nat.Basic
public import Init.Data.NeZero
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Subgroup.Actions
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Basic
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.FieldTheory.Perfect
public import Mathlib.FieldTheory.Separable
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.StdBasis
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.Bialgebra.Basic
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.RedCov


open GroundTheory.Automorphic GroundTheory.Heights₂.Heights.FiniteCovolume Module in
theorem exists_ratPts_sends_isotropic : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E), IsWittFrame σ J X Y → ∀ v : Fin n → E, v ≠ 0 → hE σ J v v = 0 → ∃ γ ∈ ratPts σ J, Sends σ J γ (Xᵀ 0) v := by
  intro F E _ _ _ _ _ σ hσ n J hJ r X Y hW v hv hvv
  obtain ⟨hF, hEc, h2, hc⟩ := hσ
  have : Algebra.IsQuadraticExtension F E := ⟨h2⟩
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  obtain rfl : σ = (conj F E).toAlgHom := AlgHom.ext fun x =>
    τ.injective ((hc τ x).trans (embedding_conj τ x).symm)
  have hu : IsUnit J.det := isUnit_iff_ne_zero.2 hJ.2
  have hH : IsHermitianFor (conjHom F E) J := Matrix.ext fun i j => hJ.1 i j
  obtain ⟨h, hg, hform⟩ : ∃ h : HermitianForm F E (Fin n → E), gram h.toSesq (Pi.basisFun E (Fin n)) = J ∧
      ∀ x y, h.toSesq x y = hE (conj F E).toAlgHom J x y :=
    ⟨HermitianForm.ofGram J hH hu, gram_ofGram J hH hu, fun x y => rfl⟩
  have key : ∀ A B : Matrix (Fin n) (Fin (r + 1)) E, h.toSesq (Aᵀ 0) (Bᵀ 0) =
      (cT (((conj F E).toAlgHom : E →ₐ[F] E) : E →+* E) A * J * B) 0 0 := by
    intro A B
    rw [hform]
    simp only [hE, Formalism.UG.hform, Matrix.mul_apply, Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]
    exact Finset.sum_comm
  have hxx : h.toSesq (Xᵀ 0) (Xᵀ 0) = 0 := by rw [key, hW.xx]; rfl
  have hyy : h.toSesq (Yᵀ 0) (Yᵀ 0) = 0 := by rw [key, hW.yy]; rfl
  have hxy : h.toSesq (Xᵀ 0) (Yᵀ 0) = 1 := by rw [key, hW.xy]; simp
  obtain ⟨w, hvw, hww⟩ := WittPartner.full h v hv (by rw [hform]; exact hvv)
  obtain ⟨g, hgv, -⟩ := HyperbolicPairTransitive.full h (Xᵀ 0) (Yᵀ 0) v w ⟨hxx, hyy, hxy⟩
    ⟨by rw [hform]; exact hvv, hww, hvw⟩
  obtain ⟨M, hM, hact⟩ : ∃ M : GL (Fin n) E, M ∈ Formalism.UG.UJ (((conj F E).toAlgHom : E →ₐ[F] E) : E →+* E) J ∧
      (M : Matrix (Fin n) (Fin n) E) *ᵥ (Xᵀ 0) = v := by
    have h3 : ∀ N : GL (Fin n) E, N ∈ unitaryGroupMatrix (conjHom F E) (gram h.toSesq (Pi.basisFun E (Fin n))) →
        N ∈ Formalism.UG.UJ (((conj F E).toAlgHom : E →ₐ[F] E) : E →+* E) J := by
      rw [hg]
      exact fun N hN => hN
    refine ⟨_, h3 _ (unitaryGroupEquivMatrix h (Pi.basisFun E (Fin n)) g).2, ?_⟩
    rw [unitaryGroupEquivMatrix_apply, LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_mulVec]
    exact hgv
  refine ⟨ratEmb _ J ⟨M, hM⟩, by rw [← range_ratEmb]; exact ⟨_, rfl⟩, ?_⟩
  unfold Sends
  funext i
  rw [← hact]
  have e : (matHom _ _ J (ratEmb _ J ⟨M, hM⟩)).1 = (M : Matrix (Fin n) (Fin n) E).map (inclR (F := F) (AF F)) := rfl
  rw [e]
  exact (RingHom.map_mulVec (inclR (F := F) (AF F)) _ _ i).symm

end GlobalTheory.CompanionTheory.RedCov

end
