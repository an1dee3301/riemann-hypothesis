module

public import Development.Core20Slim.Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RealGaussianTraces.PsiNegTrPairGen
public import Development.Core20Slim.Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RealGaussianTraces.SecondCountableTens
public import Development.Core20Slim.Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhitGenOf
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.IsSingTest
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.ClsBoundAlt
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.NullSec
public import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Ring.CharZero
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

noncomputable section

namespace PositivityTheory.SiegelWeilFormula.GReal

open HeckeCharacterZeroLocus.SiegelWeilU NumberField MeasureTheory PositivityTheory.PfSWUS.Loc PositivityTheory.Rg.Sw PositivityTheory.SiegelWeilFormula.Gen
open scoped TensorProduct Matrix NNReal

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem map_gramR (σ : E →ₐ[F] E) (θ : Ainf F ⊗[F] E →+* ℂ)
    (hc : ∀ z, θ (sigR (Ainf F) σ z) = star (θ z)) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (Y : Fin n → Fin M → Ainf F ⊗[F] E) :
    (gramR (Ainf F) σ J Y).map θ =
      (Matrix.of fun a j => θ (Y j a))ᴴ * (JR (Ainf F) J).map θ * Matrix.of fun a j => θ (Y j a) := by
  ext a b
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.map_apply, gramR, hR, hform, map_sum, map_mul, hc, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.of_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem of_eq_crd {M n : ℕ} (θ : Ainf F ⊗[F] E →+* ℂ) (fr : GL (Fin M) ℂ) (g : GL (Fin n) ℂ)
    (Y : Fin n → Fin M → Ainf F ⊗[F] E) :
    (Matrix.of fun a j => θ (Y j a)) = fr.1 * crd θ fr g Y * (g⁻¹).1 := by
  simp only [crd, ← Matrix.mul_assoc]
  rw [← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul, Matrix.mul_assoc, ← Units.val_mul,
    mul_inv_cancel, Units.val_one, Matrix.mul_one]

theorem map_gramR_crd (σ : E →ₐ[F] E) (ψ : AddChar (AF F) ℂ) {ι : Type} [Fintype ι]
    (θ : ι → (Ainf F ⊗[F] E →+* ℂ)) (l : ι → ℝ) (hP : IsPlaces σ ψ θ l) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (ε : ι → Fin M → Bool) (fr : ι → GL (Fin M) ℂ) (hfr : IsFrames J θ ε fr) (g : ι → GL (Fin n) ℂ)
    (Y : Fin n → Fin M → Ainf F ⊗[F] E) (i : ι) :
    (gramR (Ainf F) σ J Y).map (θ i) = (((g i)⁻¹).1)ᴴ * gramX (ε i) (crdAll θ fr g Y i) * ((g i)⁻¹).1 := by
  rw [map_gramR σ (θ i) (hP.conj i), of_eq_crd (θ i) (fr i) (g i)]
  have hg : gramX (ε i) (crdAll θ fr g Y i) =
      (crd (θ i) (fr i) (g i) Y)ᴴ * Matrix.diagonal (sgn (ε i)) * crd (θ i) (fr i) (g i) Y := gramX_eq _ _
  rw [hg, ← hfr i]
  simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]

theorem trace_herm_mul {n : ℕ} (β y : WR.E n) :
    (herm β * herm y).trace = ∑ a, ∑ b, ((β a b : ℝ) : ℂ) * ((y a b : ℝ) : ℂ) := by
  have key : ∀ i j, herm β i j * herm y j i + herm β j i * herm y i j =
      ((β i j : ℝ) : ℂ) * ((y i j : ℝ) : ℂ) + ((β j i : ℝ) : ℂ) * ((y j i : ℝ) : ℂ) := by
    intro i j
    apply Complex.ext <;> simp [herm] <;> ring
  have h2 : (2 : ℂ) * (herm β * herm y).trace = 2 * ∑ a, ∑ b, ((β a b : ℝ) : ℂ) * ((y a b : ℝ) : ℂ) := by
    have e1 : (herm β * herm y).trace = ∑ i, ∑ j, herm β i j * herm y j i := by
      simp [Matrix.trace, Matrix.mul_apply]
    have e2 : (2 : ℂ) * ∑ i, ∑ j, herm β i j * herm y j i =
        ∑ i, ∑ j, (herm β i j * herm y j i + herm β j i * herm y i j) := by
      rw [two_mul]
      conv_lhs => arg 2; rw [Finset.sum_comm]
      simp only [Finset.sum_add_distrib]
    have e3 : (2 : ℂ) * ∑ a, ∑ b, ((β a b : ℝ) : ℂ) * ((y a b : ℝ) : ℂ) =
        ∑ i, ∑ j, (((β i j : ℝ) : ℂ) * ((y i j : ℝ) : ℂ) + ((β j i : ℝ) : ℂ) * ((y j i : ℝ) : ℂ)) := by
      rw [two_mul]
      conv_lhs => arg 2; rw [Finset.sum_comm]
      simp only [Finset.sum_add_distrib]
    rw [e1, e2, e3]
    simp only [key]
  exact mul_left_cancel₀ two_ne_zero h2

theorem trace_re_of_herm {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian) :
    ((((A * B).trace).re : ℝ) : ℂ) = (A * B).trace := by
  apply Complex.conj_eq_iff_re.mp
  change star (Matrix.trace _) = _
  rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, hA.eq, hB.eq, Matrix.trace_mul_comm]

theorem herm_ybAll (σ : E →ₐ[F] E) (ψ : AddChar (AF F) ℂ) {ι : Type} [Fintype ι]
    (θ : ι → (Ainf F ⊗[F] E →+* ℂ)) (l : ι → ℝ) (hP : IsPlaces σ ψ θ l) {n : ℕ} (g : ι → GL (Fin n) ℂ)
    (b : HermR (Ainf F) σ n) (i : ι) :
    herm (ybAll σ θ g b i) =
      ((g i)⁻¹).1 * (b : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)).map (θ i) * (((g i)⁻¹).1)ᴴ :=
  herm_hinv _ (Matrix.isHermitian_mul_mul_conjTranspose _ (map_isHerm σ (θ i) (hP.conj i) b))

theorem herm_ygAll (σ : E →ₐ[F] E) (ψ : AddChar (AF F) ℂ) {ι : Type} [Fintype ι]
    (θ : ι → (Ainf F ⊗[F] E →+* ℂ)) (l : ι → ℝ) (hP : IsPlaces σ ψ θ l) {n : ℕ} (g : ι → GL (Fin n) ℂ)
    (b : HermR (Ainf F) σ n) (i : ι) :
    herm (ygAll σ θ g b i) =
      ((g i).1)ᴴ * (b : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)).map (θ i) * (g i).1 :=
  herm_hinv _ (Matrix.isHermitian_conjTranspose_mul_mul _ (map_isHerm σ (θ i) (hP.conj i) b))

end PositivityTheory.SiegelWeilFormula.GReal
