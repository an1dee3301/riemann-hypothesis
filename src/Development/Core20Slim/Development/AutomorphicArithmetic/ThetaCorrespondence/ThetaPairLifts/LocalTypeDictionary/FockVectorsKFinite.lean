module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolActs
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergLineDerivativeFiniteSpanStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVacuaSpanFiniteDimensionalStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompactUnitaryMovesHeisenbergDerivativeStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.GaussianCompactActionEigen
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFiniteDimensionalOrbitOfBoundedRankGeneratStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
public import Development.Core20Slim.Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.MemPolarizationStabilizerOfDualPair
public import Development.Core20Slim.Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.IsGaussianOfFockVacuumStabilizerActs
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Classical
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Notation.Prod
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Sets
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Logic.Function.Basic
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.Order.Bounds.Defs
public import Mathlib.Order.CompleteLattice.Defs
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
namespace GlobalTheory.FockKFin
theorem fock_space_kFinite : FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (n d : ℕ) (X : IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n)
    (W : IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d) (M : IndefiniteRowSideFullHecke.WeilTensorModels.Model σ X W) (χX χW : IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E)
    (om : IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ X W) (r s r' s' : ℕ), ThK.IsPair B M χX χW om r s r' s' →
    ∀ f ∈ M.Pol B.ψ B.emb, ∃ S : Submodule ℂ (IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)), FiniteDimensional ℂ S ∧
      ∀ k ∈ IndefiniteRowSideFullHecke.WeilTensorModels.KInf σ X B.emb, ∀ f₁ : IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d),
        IndefiniteRowSideFullHecke.WeilTensorModels.Acts (IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (om (k, 1)) f f₁ → f₁ ∈ S := by
  intro hPr F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP f hf
  have hPA := T.dualPair_preserves_polarization hPr F E σ B n d X W M χX χW om r s r' s' hP
  obtain ⟨m, L, hD⟩ := T.heisenbergLine_derivative_finite_span F E σ n d X W M B.ψ hP.base.std
  choose! Dfun hDiff hDspan using hD
  have hK := hPA.2.1
  simp only [RealActs.OpOn] at hK
  choose! Tk hTpres hTacts using hK
  have hGP : ∀ f₀, M.IsGauss B.ψ B.emb f₀ → f₀ ∈ M.Pol B.ψ B.emb := fun f₀ h =>
    Submodule.mem_sInf.2 fun N hN => hN.1 f₀ h
  have hclos : ∀ u, At (evI F) u → ∀ g ∈ M.Pol B.ψ B.emb, Dfun u g ∈ M.Pol B.ψ B.emb := fun u hu g hg =>
    Submodule.mem_sInf.2 fun N hN => hN.2 u hu g (Submodule.mem_sInf.1 hg N hN) _ ((hDiff u hu g _).2 rfl)
  have hmin : ∀ N : Submodule ℂ (SInf F (Fin n × Fin d)), {f₀ | M.IsGauss B.ψ B.emb f₀} ⊆ N →
      (∀ u ∈ {u : Matrix (Fin n) (Fin d) (AE F E) | At (evI F) u}, ∀ g ∈ N, Dfun u g ∈ N) → M.Pol B.ψ B.emb ≤ N := by
    intro N hG hN
    refine sInf_le ⟨fun f₀ h => hG h, fun u hu g hg g₁ hg₁ => ?_⟩
    rw [(hDiff u hu g g₁).1 hg₁]
    exact hN u hu g hg
  have hAt : ∀ k : UA σ X.J, ∀ u : Matrix (Fin n) (Fin d) (AE F E), At (evI F) u → At (evI F) (mat k * u) :=
    fun k u hu c hc => by rw [← Matrix.mul_smul, hu c hc, Matrix.mul_zero]
  obtain ⟨S, hS, hSk⟩ := T.exists_finiteDimensional_orbit_of_boundedRank_generated (SInf F (Fin n × Fin d)) (Matrix (Fin n) (Fin d) (AE F E))
    {k // k ∈ KInf σ X B.emb} {u | At (evI F) u} {f₀ | M.IsGauss B.ψ B.emb f₀} (M.Pol B.ψ B.emb) Dfun m L
    (fun k => Tk k.1) (fun k u => mat k.1 * u) (T.fockVacua_span_finiteDimensional F E σ B n d X W M χX χW om r s r' s' hP)
    (fun u hu g => hDspan u hu g) (fun f₀ h => hGP f₀ h) (fun u hu g hg => hclos u hu g hg) hmin
    (fun k g hg => Submodule.subset_span
      (T.fock_vacuum_stabilized_is_gaussian hPr F E σ B n d X W M χX χW om r s r' s' hP k.1 k.2 g hg _
        ((hTacts k.1 k.2 g (hGP g hg) _).2 rfl)))
    (fun k u hu => hAt k.1 u hu)
    (fun k u hu g hg => (hDiff _ (hAt k.1 u hu) _ _).1
      (T.compactUnitary_moves_heisenbergDerivative F E σ B n d X W M χX χW om r s r' s' hP k.1 k.2 u hu g (Dfun u g) (Tk k.1 g)
        (Tk k.1 (Dfun u g)) ((hDiff u hu g _).2 rfl) ((hTacts k.1 k.2 g hg _).2 rfl)
        ((hTacts k.1 k.2 _ (hclos u hu g hg) _).2 rfl)))
    f hf
  exact ⟨S, hS, fun k hk f₁ hact => by rw [(hTacts k hk f hf f₁).1 hact]; exact hSk ⟨k, hk⟩⟩
end GlobalTheory.FockKFin
end

section
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fock_vectors_kFinite : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (n d : ℕ) (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n)
    (W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d) (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ X W) (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ X W) (r s r' s' : ℕ), GlobalTheory.ThK.IsPair B M χX χW om r s r' s' →
    ∀ f ∈ M.Pol B.ψ B.emb, ∃ S : Submodule ℂ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)), FiniteDimensional ℂ S ∧
      ∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf σ X B.emb, ∀ f₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d),
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (om (k, 1)) f f₁ → f₁ ∈ S := by
  first | exact @_root_.GlobalTheory.FockKFin.fock_space_kFinite | exact _root_.GlobalTheory.FockKFin.fock_space_kFinite | (intros; apply _root_.GlobalTheory.FockKFin.fock_space_kFinite <;> assumption)
end
