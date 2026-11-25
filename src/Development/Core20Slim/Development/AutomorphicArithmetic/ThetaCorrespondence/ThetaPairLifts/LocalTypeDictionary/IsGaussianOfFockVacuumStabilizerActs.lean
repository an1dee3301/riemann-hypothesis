module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.GaussianCompactActionEigen
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
public import Development.Core20Slim.Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.MemPolarizationStabilizerOfDualPair
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolActs
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompactUnitaryMovesHeisenbergDerivativeStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergLineDerivativeFiniteSpanStatement
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Classical
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
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
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Sets
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.GroupTheory.GroupAction.Hom
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
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix
namespace GlobalTheory.FockVacStab
theorem isGaussian_of_fock_vacuum_stabilizer_acts : FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W)
    (r s r' s' : ℕ), ThK.IsPair B M χX χW om r s r' s' → ∀ k ∈ KInf σ X B.emb, ∀ f₀ : SInf F (Fin n × Fin d),
    M.IsGauss B.ψ B.emb f₀ → ∀ f₁ : SInf F (Fin n × Fin d), Acts (evI F) (om (k, 1)) f₀ f₁ → M.IsGauss B.ψ B.emb f₁ := by
  intro hPr F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP k hk f₀ hG f₁ hact
  have hPA := T.dualPair_preserves_polarization hPr F E σ B n d X W M χX χW om r s r' s' hP
  obtain ⟨m, L, hD⟩ := T.heisenbergLine_derivative_finite_span F E σ n d X W M B.ψ hP.base.std
  choose! Dfun hDiff _ using hD
  obtain ⟨Dk, _, hDk⟩ := hPA.2.1 k hk
  have hGP : ∀ g, M.IsGauss B.ψ B.emb g → g ∈ M.Pol B.ψ B.emb := fun g h =>
    Submodule.mem_sInf.2 fun N hN => hN.1 g h
  have hclos : ∀ u, At (evI F) u → ∀ g ∈ M.Pol B.ψ B.emb, Dfun u g ∈ M.Pol B.ψ B.emb := fun u hu g hg =>
    Submodule.mem_sInf.2 fun N hN => hN.2 u hu g (Submodule.mem_sInf.1 hg N hN) _ ((hDiff u hu g _).2 rfl)
  have hAt : ∀ (a : Matrix (Fin n) (Fin n) (AE F E)) (u : Matrix (Fin n) (Fin d) (AE F E)), At (evI F) u →
      At (evI F) (a * u) := fun a u hu c hc => by rw [← Matrix.mul_smul, hu c hc, Matrix.mul_zero]
  obtain ⟨hkk, hkk'⟩ := mat_mul_mat_inv k
  have hcomm : ∀ w, (mat k⁻¹).map (piInf (B.emb w)) * X.θ w = X.θ w * (mat k⁻¹).map (piInf (B.emb w)) := by
    intro w
    set A := (mat k).map (piInf (B.emb w))
    set A' := (mat k⁻¹).map (piInf (B.emb w))
    have h1 : A * A' = 1 := by
      rw [← Matrix.map_mul, hkk]; exact Matrix.map_one _ (map_zero _) (map_one _)
    have h2 : A' * A = 1 := by
      rw [← Matrix.map_mul, hkk']; exact Matrix.map_one _ (map_zero _) (map_one _)
    have hc : A * X.θ w = X.θ w * A := hk.2 w
    calc A' * X.θ w = A' * X.θ w * (A * A') := by rw [h1, Matrix.mul_one]
      _ = A' * (X.θ w * A) * A' := by simp only [Matrix.mul_assoc]
      _ = A' * (A * X.θ w) * A' := by rw [hc]
      _ = (A' * A) * X.θ w * A' := by simp only [Matrix.mul_assoc]
      _ = X.θ w * A' := by rw [h2, Matrix.one_mul]
  obtain ⟨ε, hε⟩ := hG
  refine ⟨ε, fun u u' hu hu' huu' f f' hf hf' => ?_⟩
  set v := mat k⁻¹ * u
  set v' := mat k⁻¹ * u'
  have hv : At (evI F) v := hAt _ u hu
  have hv' : At (evI F) v' := hAt _ u' hu'
  have hvv' : ∀ w, v'.map (piInf (B.emb w)) =
      (((ε w : ℤ) : ℂ) * Complex.I) • (X.θ w * v.map (piInf (B.emb w)) * (W.θ w)ᵀ) := by
    intro w
    simp only [v, v', Matrix.map_mul, huu' w, Matrix.mul_smul, ← Matrix.mul_assoc, hcomm w]
  have hkv : mat k * v = u := by simp only [v, ← Matrix.mul_assoc, hkk, Matrix.one_mul]
  have hkv' : mat k * v' = u' := by simp only [v', ← Matrix.mul_assoc, hkk, Matrix.one_mul]
  have hgg : Dfun v' f₀ = Complex.I • Dfun v f₀ :=
    hε v v' hv hv' hvv' _ _ ((hDiff v hv f₀ _).2 rfl) ((hDiff v' hv' f₀ _).2 rfl)
  have hf0 : f₀ ∈ M.Pol B.ψ B.emb := hGP f₀ ⟨ε, hε⟩
  have hmove : ∀ x, At (evI F) x → ActsD (evI F) (M.heisLine B.ψ (mat k * x)) f₁ (Dk (Dfun x f₀)) := by
    intro x hx
    exact T.compactUnitary_moves_heisenbergDerivative F E σ B n d X W M χX χW om r s r' s' hP k hk x hx f₀ (Dfun x f₀) f₁ (Dk (Dfun x f₀))
      ((hDiff x hx f₀ _).2 rfl) hact ((hDk _ (hclos x hx f₀ hf0) _).2 rfl)
  have e1 : f = Dk (Dfun v f₀) := by
    have a := (hDiff u hu f₁ f).1 hf
    have b := (hDiff u hu f₁ _).1 (hkv ▸ hmove v hv)
    rw [a, b]
  have e2 : f' = Dk (Dfun v' f₀) := by
    have a := (hDiff u' hu' f₁ f').1 hf'
    have b := (hDiff u' hu' f₁ _).1 (hkv' ▸ hmove v' hv')
    rw [a, b]
  rw [e2, e1, hgg, map_smul]
end GlobalTheory.FockVacStab
end

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fock_vacuum_stabilized_is_gaussian : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W)
    (r s r' s' : ℕ), GlobalTheory.ThK.IsPair B M χX χW om r s r' s' → ∀ k ∈ KInf σ X B.emb, ∀ f₀ : SInf F (Fin n × Fin d),
    M.IsGauss B.ψ B.emb f₀ → ∀ f₁ : SInf F (Fin n × Fin d), Acts (evI F) (om (k, 1)) f₀ f₁ → M.IsGauss B.ψ B.emb f₁ := by
  first | exact @_root_.GlobalTheory.FockVacStab.isGaussian_of_fock_vacuum_stabilizer_acts | exact _root_.GlobalTheory.FockVacStab.isGaussian_of_fock_vacuum_stabilizer_acts | (intros; apply _root_.GlobalTheory.FockVacStab.isGaussian_of_fock_vacuum_stabilizer_acts <;> assumption)
end
