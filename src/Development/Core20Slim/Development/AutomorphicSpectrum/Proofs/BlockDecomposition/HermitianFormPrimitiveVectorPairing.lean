module

public import Mathlib
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HypOneZeroZero
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HermitianMatricesLocallyCompactBorel
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.WittExtensionArtinianRingStatement
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LinearlyIndependentFramesOpen
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsReducedAlgebraOfSmoothOfIsNoetherianRing
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.TensAll
public import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import Init.Core
public import Init.Data.Fin.Basic
public import Init.Data.Fin.Lemmas
public import Init.Data.Nat.Basic
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Rat
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Basic.Unique
public import Mathlib.Data.Finset.BooleanAlgebra
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Insert
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.FieldTheory.Perfect
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Artinian.Defs
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.EssentialFiniteness
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.RingTheory.Smooth.Field
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Finite
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Separation.Hausdorff

@[expose] public section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.FreePartner

theorem isReduced_tens (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (R : Type) [CommRing R] [Algebra F R] [IsReduced R] : IsReduced (R ⊗[F] E) := by
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : Algebra.FormallyEtale F E := Algebra.FormallyEtale.of_isSeparable F E
  haveI : Algebra.FormallySmooth F E := inferInstance
  haveI : Algebra.FinitePresentation F E := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  haveI : Algebra.Smooth F E := ⟨inferInstance, inferInstance⟩
  haveI : Algebra.Smooth R (R ⊗[F] E) := inferInstance
  exact GlobalTheory.isReduced_algebra_of_smooth_of_isReduced R (R ⊗[F] E)

theorem isUnit_det_JR {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R]
    [Algebra F R] {M : ℕ} {J : Matrix (Fin M) (Fin M) E} (h : J.det ≠ 0) :
    IsUnit (JR (F := F) R J).det := by
  have e : (JR (F := F) R J).det = inclR (F := F) R J.det := by
    rw [RingHom.map_det]
    rfl
  rw [e]
  exact (IsUnit.mk0 _ h).map _

theorem exists_partner : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ x : Fin M → R ⊗[F] E, LinearIndependent (R ⊗[F] E) (fun _ : Fin 1 => x) → ∃ y : Fin M → R ⊗[F] E, hR R σ J x y = 1 := by
  intro F E _ _ _ _ _ σ hσ M J hJ R _ _ _ _ _ hloc x hx
  obtain ⟨-, -, -, -, hA, hRed, -, -⟩ := hloc
  haveI := hA
  haveI := hRed
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsArtinianRing (R ⊗[F] E) := IsArtinianRing.of_finite R _
  haveI : IsReduced (R ⊗[F] E) := isReduced_tens F E R
  have hinv : ∀ z : R ⊗[F] E, sigR R σ (sigR R σ z) = z :=
    HermTop.sigR_sigR R (HermTop.sigma_sigma hσ)
  have hlip := FreeOpen.lip_of_artinian_reduced (R ⊗[F] E)
  obtain ⟨P, hP⟩ := hlip (Fin M) (Fin 1)
    (Matrix.of fun i (_ : Fin 1) => sigR R σ (x i)) (by
      intro c hc
      have h1 : ∀ i, sigR R σ (x i) * c 0 = 0 := by
        intro i
        have := congrFun hc i
        simpa [Matrix.mulVec, dotProduct] using this
      have h2 : sigR R σ (c 0) • x = 0 := by
        funext i
        have := congrArg (sigR R σ) (h1 i)
        rw [map_mul, hinv, map_zero] at this
        simpa [mul_comm] using this
      have h3 := Fintype.linearIndependent_iff.mp hx (fun _ => sigR R σ (c 0)) (by simpa using h2) 0
      have h4 : c 0 = 0 := by
        have := congrArg (sigR R σ) h3
        simpa [hinv] using this
      funext j
      rw [Subsingleton.elim j 0]
      simpa using h4)
  have hu := isUnit_det_JR (F := F) R hJ.2
  refine ⟨(JR R J)⁻¹ *ᵥ (fun j => P 0 j), ?_⟩
  have hv : JR R J *ᵥ ((JR R J)⁻¹ *ᵥ (fun j => P 0 j)) = fun j => P 0 j := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hu, Matrix.one_mulVec]
  have h00 := congrFun (congrFun hP 0) 0
  simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply_eq] at h00
  have hform' : hR R σ J x ((JR R J)⁻¹ *ᵥ (fun j => P 0 j)) =
      ∑ i, sigR R σ (x i) * (JR R J *ᵥ ((JR R J)⁻¹ *ᵥ (fun j => P 0 j))) i := by
    simp only [hR, hform, Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
  rw [hform', hv, ← h00]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

end GlobalTheory.CompanionTheory.WeilSiegel.FreePartner
