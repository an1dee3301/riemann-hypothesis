module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnitaryOnTheta
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramHspOf
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStdCharNegOneOfStandardTraceAdelicAddCharStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictsToQuadraticSignPowIdelicRestrictionStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianSelfDualLatticeSpaceFormHermitianNondegStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewHermitianNegTraceZeroInvHermitianUnimodularStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilRepHermitianPairRationalSchrodingerStatement
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
public import Formalism.HermitianLattices.StatementLat
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Lattice.Basic
public import Mathlib.Algebra.Module.Lattice.Full
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Ring.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.SesquilinearForm.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.WeilSchrodinger

theorem exists_isWeil : ∀ (D : D7) (B : Base D.host.F D.host.E), B.IsGood D.sp.cm.sig →
    ∀ (n d : ℕ) (X : Spc D.host.F D.host.E n) (Y : Spc D.host.F D.host.E d) (r s r' s' : ℕ),
      X.IsHerm D.sp.cm.sig B r s → Y.IsSkew D.sp.cm.sig B r' s' →
      ∀ Mo : Model D.sp.cm.sig X Y, Mo.IsGood B.ψ →
      ∀ χX χW : Chr D.host.F D.host.E, GlobalTheory.LFun.IsHecke D.host.F D.host.E χX → GlobalTheory.LFun.IsHecke D.host.F D.host.E χW →
        GlobalTheory.WeilM.ResEtaPow (Units.map (algebraMap D.host.F (AF D.host.F)).toMonoidHom).range χX n →
        GlobalTheory.WeilM.ResEtaPow (Units.map (algebraMap D.host.F (AF D.host.F)).toMonoidHom).range χW d →
        ∃ om, Mo.IsWeil B.ψ χX χW om := by
  intro D B hB n d X Y r s r' s' hX hY Mo hMo χX χW hcX hcW rX rW
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.T.hermitianSelfDualLatticeSpace_form_hermitian_nondeg_unimodular D B hB n X r s hX
  obtain ⟨hJ, L, hL, h4, h5, h6⟩ := GlobalTheory.T.skewHermitian_neg_traceZero_inv_hermitian_unimodular D B hB d Y r' s' hY
  have hξ : D.host.xi0 ≠ 0 := GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D
  let T := hspOf D X.Jᵀ h1 h2 X.L (by letI := hX.lat; infer_instance) h3 (fun _ => (r, s))
  let S := hspOf D (-D.host.xi0 • Y.J⁻¹) h4 h5 L hL h6 (fun _ => (s', r'))
  have eA : X.J = T.gramᵀ := by rw [gram_hspOf]; rfl
  have eB : (-1 : AF D.host.F ⊗[D.host.F] D.host.E) • incM D.host.F Y.J = incM D.host.F (D.host.xi0 • S.gram⁻¹) := by
    rw [gram_hspOf]
    have e1 : (-D.host.xi0 • Y.J⁻¹)⁻¹ = (-D.host.xi0)⁻¹ • Y.J := Matrix.inv_eq_left_inv (by
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_nonsing_inv _ hJ,
        inv_mul_cancel₀ (neg_ne_zero.2 hξ), one_smul])
    have e2 : D.host.xi0 • (-D.host.xi0)⁻¹ • Y.J = -Y.J := by
      rw [smul_smul, inv_neg, mul_neg, mul_inv_cancel₀ hξ, neg_one_smul]
    show (-1 : AF D.host.F ⊗[D.host.F] D.host.E) • incM D.host.F Y.J = incM D.host.F (D.host.xi0 • (-D.host.xi0 • Y.J⁻¹)⁻¹)
    rw [e1, e2]
    funext i j
    simp [incM]
  exact GlobalTheory.T.exists_weilRep_hermitianPair_rationalSchrodinger D B.ψ (GlobalTheory.T.isStdChar_neg_one_of_standardTraceAdelicAddChar D B.ψ hB.std) S T χW χX hcW hcX (GlobalTheory.T.restrictsToQuadraticSignPow_idelic_restriction D χW d rW) (GlobalTheory.T.restrictsToQuadraticSignPow_idelic_restriction D χX n rX) X.J Y.J (-1) eA eB
    (Fin n × Fin d) Mo.co hMo.rat

end GlobalTheory.WeilSchrodinger

end
