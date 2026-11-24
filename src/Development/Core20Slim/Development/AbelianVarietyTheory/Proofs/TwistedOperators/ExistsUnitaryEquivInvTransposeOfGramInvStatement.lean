module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnitaryEquivInvTransposeOfGramInv
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsReading
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Prelude
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Topology.Defs.Basic

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unitary_equiv_inv_transpose_of_gram_inv : ∀ (D : D7) (T S' : HSp D) (e₂ : Fin S'.rank ≃ Fin T.rank), S'.gram⁻¹ = -(T.gramᵀ.submatrix e₂ e₂) →
    ∃ φ : GA D S' ≃* GA D T, Continuous φ ∧ (∀ γ ∈ GQ S', φ γ ∈ GQ T) ∧
      (∀ g, (Formalism.L2.Theta.mt T (φ g)).submatrix e₂ e₂ = (Formalism.L2.Theta.mt S' g⁻¹)ᵀ) ∧
      (∀ e g, SuppAt e S' g → SuppAt e T (φ g)) ∧ ∀ g, (Formalism.L2.Theta.mt T (φ g)).det = (Formalism.L2.Theta.mt S' g⁻¹).det := by
  first | exact @GlobalTheory.InvTransposeIso.grp_contra | exact GlobalTheory.InvTransposeIso.grp_contra | (intros; apply GlobalTheory.InvTransposeIso.grp_contra <;> assumption)
