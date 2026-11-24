module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Spectrum.Basic
public import Mathlib.Algebra.Algebra.StrictPositivity
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Algebra.Star.SelfAdjoint
public import Mathlib.Algebra.Star.Unitary
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unique
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unital
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.CStarAlgebra.Spectrum
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Eigenspace.Minpoly
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.LinearAlgebra.Matrix.InvariantBasisNumber
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.RingTheory.FiniteType
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.ContinuousOn
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.GDelta.MetrizableSpace
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.MetricSpace.Defs
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Metrizable.Uniformity
public import Mathlib.Topology.Separation.Basic
public import Mathlib.Topology.Separation.GDelta
public import Mathlib.Topology.Separation.Regular
public import Mathlib.Topology.UniformSpace.Defs
public import Mathlib.Topology.UniformSpace.Matrix

@[expose] public section

open Matrix

namespace GlobalTheory.ExpCartan

open scoped Matrix.Norms.L2Operator ComplexOrder


open scoped MatrixOrder in
theorem exists_posDef_mul_self {n : ℕ} {P : Matrix (Fin n) (Fin n) ℂ} (hP : P.PosDef) :
    ∃ S : Matrix (Fin n) (Fin n) ℂ, S.PosDef ∧ S * S = P := by
  refine ⟨CFC.sqrt P, ?_, CFC.sqrt_mul_sqrt_self _ hP.posSemidef.nonneg⟩
  have hP' := hP
  rw [← isStrictlyPositive_iff_posDef] at hP' ⊢
  exact IsStrictlyPositive.sqrt _ hP'

theorem im_star_dotProduct_mulVec {n : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (hM : Mᴴ = M)
    (x : Fin n → ℂ) : (star x ⬝ᵥ M *ᵥ x).im = 0 := by
  have h : star (star x ⬝ᵥ M *ᵥ x) = star x ⬝ᵥ M *ᵥ x := by
    rw [← Matrix.star_dotProduct, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, hM]
  exact Complex.conj_eq_iff_im.1 h

theorem exists_exp_eq_of_commute_cartan : ∀ {n : ℕ} {G C g : Matrix (Fin n) (Fin n) ℂ}, Gᴴ = G →
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsCartan Gᵀ C → gᴴ * G * g = G → Commute g C →
    ∃ Z : Matrix (Fin n) (Fin n) ℂ, Zᴴ * G + G * Z = 0 ∧ Commute Z C ∧ NormedSpace.exp Z = g := by
  intro n G C g hG hC hg hgC
  obtain ⟨hCC, hCG, hpos⟩ := hC
  have hCG' : Cᴴ * G * C = G := by
    have h := congrArg Matrix.transpose hCG
    simpa [Matrix.transpose_mul, Matrix.conjTranspose, Matrix.transpose_map, Matrix.mul_assoc] using h
  have hCG2 : Cᴴ * G = G * C := by
    calc Cᴴ * G = Cᴴ * G * (C * C) := by rw [hCC, Matrix.mul_one]
      _ = G * C := by rw [← Matrix.mul_assoc, hCG']
  set P := G * C with hPdef
  have hPh : Pᴴ = P := by rw [hPdef, Matrix.conjTranspose_mul, hG, hCG2]
  have hPpd : P.PosDef := by
    refine Matrix.posDef_iff_dotProduct_mulVec.2 ⟨hPh, fun x hx => ?_⟩
    have h1 := hpos x hx
    have he : (C *ᵥ x) ⬝ᵥ Gᵀ *ᵥ star x = star x ⬝ᵥ P *ᵥ x := by
      rw [dotProduct_comm, Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec,
        hPdef, ← Matrix.mulVec_mulVec]
    rw [he] at h1
    exact Complex.lt_def.2 ⟨by simpa using h1, by simpa using (im_star_dotProduct_mulVec hPh x).symm⟩
  obtain ⟨S, hSpd, hSS⟩ := exists_posDef_mul_self hPpd
  have hSh : Sᴴ = S := hSpd.isHermitian
  have hSu : IsUnit S.det := (Matrix.isUnit_iff_isUnit_det S).1 hSpd.isUnit
  set Si := S⁻¹ with hSidef
  have h1 : S * Si = 1 := Matrix.mul_nonsing_inv _ hSu
  have h2 : Si * S = 1 := Matrix.nonsing_inv_mul _ hSu
  have hSih : Siᴴ = Si := by rw [hSidef, Matrix.conjTranspose_nonsing_inv, hSh]
  have hgP : gᴴ * P * g = P := by
    calc gᴴ * P * g = gᴴ * G * (C * g) := by rw [hPdef]; simp only [Matrix.mul_assoc]
      _ = gᴴ * G * g * C := by rw [← hgC.eq]; simp only [Matrix.mul_assoc]
      _ = P := by rw [hg]
  set u := S * g * Si with hudef
  have hsu : star u = Si * gᴴ * S := by
    rw [hudef, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hSh, hSih,
      Matrix.mul_assoc]
  have huu : star u * u = 1 := by
    rw [hsu, hudef]
    calc Si * gᴴ * S * (S * g * Si) = Si * (gᴴ * (S * S) * g) * Si := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hSS, hgP, ← hSS, ← Matrix.mul_assoc, h2, Matrix.one_mul, h1]
  have hu : u ∈ unitary (Matrix (Fin n) (Fin n) ℂ) := ⟨huu, mul_eq_one_comm.1 huu⟩
  set C' := S * C * Si with hC'def
  have hSC : S * C = C' * S := by rw [hC'def, Matrix.mul_assoc _ Si, h2, Matrix.mul_one]
  have hSiC' : Si * C' = C * Si := by
    rw [hC'def, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h2, Matrix.one_mul]
  have huC : Commute u C' := by
    show u * C' = C' * u
    rw [hudef, hC'def]
    calc S * g * Si * (S * C * Si) = S * g * (Si * S) * C * Si := by simp only [Matrix.mul_assoc]
      _ = S * (C * g) * Si := by rw [h2, Matrix.mul_one, Matrix.mul_assoc S g C, hgC.eq]
      _ = S * C * (Si * S) * g * Si := by rw [h2, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = S * C * Si * (S * g * Si) := by simp only [Matrix.mul_assoc]
  have huC' : Commute (star u) C' := by
    have hus : u * star u = 1 := mul_eq_one_comm.1 huu
    show star u * C' = C' * star u
    calc star u * C' = star u * (C' * (u * star u)) := by rw [hus, Matrix.mul_one]
      _ = star u * (u * C' * star u) := by rw [huC.eq]; simp only [Matrix.mul_assoc]
      _ = (star u * u) * C' * star u := by simp only [Matrix.mul_assoc]
      _ = C' * star u := by rw [huu, Matrix.one_mul]
  have hN : IsStarNormal u := ⟨by
    show star u * u = u * star u
    rw [huu, mul_eq_one_comm.1 huu]⟩
  have hfin : (spectrum ℂ u).Finite := Matrix.finite_spectrum u
  have hsph : ∀ z ∈ spectrum ℂ u, ‖z‖ = 1 := fun z hz => by
    simpa using spectrum.subset_circle_of_unitary hu hz
  set Y := cfc Complex.log u with hYdef
  have hlog : ContinuousOn Complex.log (spectrum ℂ u) := hfin.continuousOn _
  have hexp : NormedSpace.exp Y = u := by
    rw [hYdef, ← CFC.exp_eq_normedSpace_exp (𝕜 := ℂ), ← Complex.exp_eq_exp_ℂ,
      ← cfc_comp Complex.exp Complex.log u (hf := hlog) (ha := hN)]
    conv_rhs => rw [← cfc_id' ℂ u hN]
    refine cfc_congr fun z hz => ?_
    have hz0 : z ≠ 0 := by intro h; have := hsph z hz; rw [h] at this; simp at this
    simp [Complex.exp_log hz0]
  have hstar : star Y = -Y := by
    rw [hYdef, ← cfc_star, ← cfc_neg]
    refine cfc_congr fun z hz => ?_
    apply Complex.ext
    · simp [Complex.log_re, hsph z hz]
    · simp
  have hYC : Commute Y C' := huC.cfc huC' Complex.log
  have hYh : Yᴴ = -Y := by rw [← Matrix.star_eq_conjTranspose, hstar]
  refine ⟨Si * Y * S, ?_, ?_, ?_⟩
  · have hGP : G = S * S * C := by
      rw [hSS, hPdef, Matrix.mul_assoc, hCC, Matrix.mul_one]
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hSh, hSih, hYh, hGP]
    calc S * (-Y * Si) * (S * S * C) + S * S * C * (Si * Y * S)
        = -(S * Y * (Si * S) * (S * C)) + S * ((S * C) * Si) * Y * S := by
          simp only [Matrix.mul_assoc, Matrix.mul_neg, Matrix.neg_mul]
      _ = -(S * (Y * C') * S) + S * (C' * Y) * S := by
          rw [h2, Matrix.mul_one, hSC, Matrix.mul_assoc C' S Si, h1, Matrix.mul_one]
          simp only [Matrix.mul_assoc]
      _ = 0 := by rw [hYC.eq, neg_add_cancel]
  · show Si * Y * S * C = C * (Si * Y * S)
    calc Si * Y * S * C = Si * (Y * C') * S := by rw [Matrix.mul_assoc _ S C, hSC]; simp only [Matrix.mul_assoc]
      _ = (Si * C') * Y * S := by rw [hYC.eq]; simp only [Matrix.mul_assoc]
      _ = C * (Si * Y * S) := by rw [hSiC']; simp only [Matrix.mul_assoc]
  · have hSun : IsUnit S := hSpd.isUnit
    rw [hSidef, Matrix.exp_conj' S Y hSun, hexp, hudef, ← hSidef]
    calc Si * (S * g * Si) * S = (Si * S) * g * (Si * S) := by simp only [Matrix.mul_assoc]
      _ = g := by rw [h2, Matrix.one_mul, Matrix.mul_one]

end GlobalTheory.ExpCartan
