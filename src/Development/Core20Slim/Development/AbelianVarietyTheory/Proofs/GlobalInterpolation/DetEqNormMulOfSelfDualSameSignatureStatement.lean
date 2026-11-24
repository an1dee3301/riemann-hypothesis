module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DetEqNormMulOfSelfDualSameSignature
public import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
public import Formalism.HermitianLattices.StatementMass
public import Formalism.LocalRingCardinality.DataSpaces
public import Init.Core
public import Init.Data.Rat.Basic
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Rat.Defs
public import Mathlib.FieldTheory.Separable
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.CMField
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal

@[expose] public section

open NumberField Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.L2.GlobalTheoryTheory.GenusMassVolumes
attribute [local instance] IsCMField.starRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.det_eq_norm_mul_of_selfDual_same_signature : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Formalism.HermitianLatticesTheory.IsCMUnram E → ∀ W₁ W₂ : HSpace E, W₁.SigOK → W₂.SigOK → W₁.rank = W₂.rank → (∀ τ, W₁.sig τ = W₂.sig τ) → ∃ z : E, W₂.gram.det = z * star z * W₁.gram.det := by
  first | exact @GlobalTheory.SelfDualDet.det_eq_norm_mul | exact GlobalTheory.SelfDualDet.det_eq_norm_mul | (intros; apply GlobalTheory.SelfDualDet.det_eq_norm_mul <;> assumption)
