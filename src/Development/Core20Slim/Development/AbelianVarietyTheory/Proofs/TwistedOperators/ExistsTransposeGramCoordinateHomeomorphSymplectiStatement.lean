module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsTransposeGramCoordinateHomeomorphSymplecti
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsReading
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Instances.Matrix

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_transposeGram_coordinate_homeomorph_symplectic : ∀ (D : D7) (S T S' T' : HSp D) (e₁ : Fin T'.rank ≃ Fin S.rank) (e₂ : Fin S'.rank ≃ Fin T.rank),
    ∃ L : WO S' T' ≃ₗ[AE D] WO S T,
      (∀ u, L u = (HMul.hMul (uᵀ.submatrix e₂.symm e₁.symm) (S.gram.map (incA D)) : Matrix (Fin T.rank) (Fin S.rank) (AE D))) ∧
      (∀ x : Matrix (Fin T.rank) (Fin S.rank) (AE D),
        L.symm x = ((HMul.hMul x ((S.gram⁻¹).map (incA D)) : Matrix (Fin T.rank) (Fin S.rank) (AE D))ᵀ).submatrix e₁ e₂) ∧
      Continuous L ∧ Continuous L.symm ∧ (∀ x, L x ∈ ratL T S ↔ x ∈ ratL T' S') ∧
      (∀ x, (L x).map (infPart D) = 0 ↔ x.map (infPart D) = 0) ∧ ∀ x, (L x).map (finPart D) = 0 ↔ x.map (finPart D) = 0 := by
  first | exact @GlobalTheory.Twist.exists_transposeGram_coordinate_homeomorph_symplectic.coordsLin_spec | exact GlobalTheory.Twist.exists_transposeGram_coordinate_homeomorph_symplectic.coordsLin_spec | (intros; apply GlobalTheory.Twist.exists_transposeGram_coordinate_homeomorph_symplectic.coordsLin_spec <;> assumption)
