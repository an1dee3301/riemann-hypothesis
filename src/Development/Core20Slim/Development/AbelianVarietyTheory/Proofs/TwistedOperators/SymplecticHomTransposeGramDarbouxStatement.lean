module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.SymplecticHomTransposeGramDarboux
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsReading
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symplectic_hom_transpose_gram_darboux : ∀ (D : D7) (S T S' T' : HSp D) (e₁ : Fin T'.rank ≃ Fin S.rank) (e₂ : Fin S'.rank ≃ Fin T.rank),
    T'.gramᵀ = -(S.gram.submatrix e₁ e₁) → S'.gram⁻¹ = -(T.gramᵀ.submatrix e₂ e₂) → ∀ x y : WO S' T',
      symplO S T (HMul.hMul (xᵀ.submatrix e₂.symm e₁.symm) (S.gram.map (incA D)) : Matrix (Fin T.rank) (Fin S.rank) (AE D))
        (HMul.hMul (yᵀ.submatrix e₂.symm e₁.symm) (S.gram.map (incA D)) : Matrix (Fin T.rank) (Fin S.rank) (AE D)) =
      symplO S' T' x y := by
  first | exact @GlobalTheory.DarbouxSymp.symplO_darboux | exact GlobalTheory.DarbouxSymp.symplO_darboux | (intros; apply GlobalTheory.DarbouxSymp.symplO_darboux <;> assumption)
