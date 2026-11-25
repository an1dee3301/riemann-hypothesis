module

public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Upqcpt
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Sum.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Notation.Pi.Basic
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.Archimedean.Real.Hom
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.Analysis.Normed.Lp.WithLp
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.Finite.Sum
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Block
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.SymplecticGroup
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.Algebra
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.UniformSpace.Defs
public import Mathlib.Topology.UniformSpace.Real

@[expose] public section

open scoped TensorProduct Matrix
open MeasureTheory Formalism.BasicNotions.TH GlobalTheory.RealLift GlobalTheory.RealWeil

noncomputable section

namespace GlobalTheory.ColAction

theorem sympl_eq_neg_dotProduct {l : Type} [Fintype l] [DecidableEq l] (u v : l ⊕ l → ℝ) :
    sympl u v = -(u ⬝ᵥ (Matrix.J l ℝ *ᵥ v)) := by
  simp [sympl, pPart, qPart, PiLp.inner_apply, Matrix.J, Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
    Matrix.one_apply, Finset.sum_neg_distrib, mul_comm]
  ring

theorem mem_symplecticGroup_of_sympl {l : Type} [Fintype l] [DecidableEq l] (M : Matrix (l ⊕ l) (l ⊕ l) ℝ)
    (h : ∀ u v, sympl (M *ᵥ u) (M *ᵥ v) = sympl u v) : M ∈ Matrix.symplecticGroup l ℝ := by
  rw [SymplecticGroup.mem_iff']
  ext a b
  have key : ∀ u v, (M *ᵥ u) ⬝ᵥ (Matrix.J l ℝ *ᵥ (M *ᵥ v)) = u ⬝ᵥ ((Mᵀ * Matrix.J l ℝ * M) *ᵥ v) := by
    intro u v
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec u Mᵀ, Matrix.vecMul_transpose]
  have := h (Pi.single a 1) (Pi.single b 1)
  rw [sympl_eq_neg_dotProduct, sympl_eq_neg_dotProduct, neg_inj, key] at this
  simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using this

theorem signed_sum_eq_trace {P Q R S : ℕ} (X Y : Matrix (Ix P Q) (Ix R S) ℂ) :
    ∑ a, ∑ b, lineSign a b * X a b * star (Y a b) = Matrix.trace (Jm P Q * X * Jm R S * Yᴴ) := by
  have e : Jm P Q * X * Jm R S =
      Matrix.of fun a b => ((fun _ => (1 : ℂ)) ⊕ᵥ fun _ => -1) a * X a b * ((fun _ => (1 : ℂ)) ⊕ᵥ fun _ => -1) b := by
    ext a b
    simp [Jm, Formalism.UG.P.Jpq_eq_diagonal, Matrix.diagonal_mul, Matrix.mul_diagonal]
  rw [e]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.of_apply, Matrix.conjTranspose_apply]
  simp [Fintype.sum_sum_type, lineSign]

theorem signed_sum_mul_transpose {P Q R S : ℕ} (X Y : Matrix (Ix P Q) (Ix R S) ℂ) (k : Mat R S)
    (hk : kᴴ * Jm R S * k = Jm R S) :
    ∑ a, ∑ b, lineSign a b * (X * kᵀ) a b * star ((Y * kᵀ) a b) = ∑ a, ∑ b, lineSign a b * X a b * star (Y a b) := by
  have hJ : (Jm R S)ᵀ = Jm R S := by
    simp [Jm, Formalism.UG.P.Jpq_eq_diagonal]
  have e : (kᵀ)ᴴ = k.map star := by ext i j; simp
  have hk' : kᵀ * Jm R S * (kᵀ)ᴴ = Jm R S := by
    have := congrArg Matrix.transpose hk
    rw [Matrix.transpose_mul, Matrix.transpose_mul, hJ, Matrix.conjTranspose_transpose] at this
    rw [e, Matrix.mul_assoc, this]
  rw [signed_sum_eq_trace, signed_sum_eq_trace, Matrix.conjTranspose_mul]
  congr 1
  calc Jm P Q * (X * kᵀ) * Jm R S * ((kᵀ)ᴴ * Yᴴ) = Jm P Q * X * (kᵀ * Jm R S * (kᵀ)ᴴ) * Yᴴ := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [hk']

theorem exists_symplectic_hom_of_unitary : ∀ (ι l : Type) [Fintype ι] [DecidableEq ι] [Fintype l] [DecidableEq l] (P Q R S : ℕ)
    (φ : (ι → Matrix (Ix P Q) (Ix R S) ℂ) ≃ₗ[ℝ] (l ⊕ l → ℝ)),
    (∀ c c', sympl (φ c) (φ c') = 2 * (∑ w, ∑ a, ∑ b, lineSign a b * c w a b * star (c' w a b)).im) →
    ∀ (G : Type) [Group G] [TopologicalSpace G] (k : G →* (ι → Mat R S)), Continuous k →
    (∀ g w, (k g w)ᴴ * Jm R S * k g w = Jm R S) →
    ∃ s : G →* Matrix.symplecticGroup l ℝ, Continuous s ∧
      ∀ g c, (s g : Matrix (l ⊕ l) (l ⊕ l) ℝ) *ᵥ φ c = φ fun w => c w * (k g w)ᵀ := by
  intro ι l _ _ _ _ P Q R S φ hφ G _ _ k hk hkJ
  let A : G → (ι → Matrix (Ix P Q) (Ix R S) ℂ) →ₗ[ℝ] (ι → Matrix (Ix P Q) (Ix R S) ℂ) := fun g =>
    { toFun := fun c w => c w * (k g w)ᵀ
      map_add' := fun c c' => by ext w : 1; simp [Matrix.add_mul]
      map_smul' := fun r c => by ext w : 1; simp [Matrix.smul_mul] }
  let T : G → (l ⊕ l → ℝ) →ₗ[ℝ] (l ⊕ l → ℝ) := fun g => φ.toLinearMap ∘ₗ A g ∘ₗ φ.symm.toLinearMap
  have hT : ∀ g c, T g (φ c) = φ (fun w => c w * (k g w)ᵀ) := fun g c => by simp [T, A]
  have hsy : ∀ g u v, sympl (T g u) (T g v) = sympl u v := by
    intro g u v
    obtain ⟨c, rfl⟩ := φ.surjective u
    obtain ⟨c', rfl⟩ := φ.surjective v
    rw [hT, hT, hφ, hφ]
    simp only [signed_sum_mul_transpose _ _ _ (hkJ g _)]
  have hmem : ∀ g, LinearMap.toMatrix' (T g) ∈ Matrix.symplecticGroup l ℝ := fun g =>
    mem_symplecticGroup_of_sympl _ (fun u v => by simpa only [LinearMap.toMatrix'_mulVec] using hsy g u v)
  have hTmul : ∀ g h, T (g * h) = T g ∘ₗ T h := by
    intro g h
    apply LinearMap.ext
    intro u
    obtain ⟨c, rfl⟩ := φ.surjective u
    show T (g * h) (φ c) = T g (T h (φ c))
    rw [hT, hT, hT]
    congr 1
    ext w : 1
    simp [map_mul, Pi.mul_apply, Matrix.transpose_mul, Matrix.mul_assoc]
  have hT1 : T 1 = LinearMap.id := by
    apply LinearMap.ext
    intro u
    obtain ⟨c, rfl⟩ := φ.surjective u
    rw [hT]
    simp
  let s : G →* Matrix.symplecticGroup l ℝ :=
    { toFun := fun g => ⟨LinearMap.toMatrix' (T g), hmem g⟩
      map_one' := by
        apply Subtype.ext
        simp only [hT1, LinearMap.toMatrix'_id]
        rfl
      map_mul' := fun g h => by
        apply Subtype.ext
        simp only [hTmul, LinearMap.toMatrix'_comp]
        rfl }
  refine ⟨s, ?_, fun g c => ?_⟩
  · apply Continuous.subtype_mk
    refine continuous_pi fun a => continuous_pi fun b => ?_
    have e : ∀ g, LinearMap.toMatrix' (T g) a b = φ (fun w => φ.symm (Pi.single b 1) w * (k g w)ᵀ) a := by
      intro g
      rw [LinearMap.toMatrix'_apply, ← hT, φ.apply_symm_apply]
    simp only [e]
    exact (continuous_apply a).comp ((LinearMap.continuous_of_finiteDimensional φ.toLinearMap).comp
      (continuous_pi fun w => continuous_const.matrix_mul ((continuous_apply w).comp hk).matrix_transpose))
  · show LinearMap.toMatrix' (T g) *ᵥ φ c = _
    rw [LinearMap.toMatrix'_mulVec, hT]

end GlobalTheory.ColAction
