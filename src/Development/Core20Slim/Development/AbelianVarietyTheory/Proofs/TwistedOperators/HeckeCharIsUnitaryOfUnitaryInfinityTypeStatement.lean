module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeCharIsUnitaryOfUnitaryInfinityType
public import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
public import Init.Data.Int.Basic
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.NumberTheory.NumberField.Basic

@[expose] public section

open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeChar_isUnitary_of_unitary_infinityType : ∀ (L : Type) [Field L] [NumberField L] (χ : Formalism.L2.Host.HChar L) {I : Type} [Fintype I] (φ : I → L →+* ℂ) (n : I → ℤ), χ.HasInf φ n → χ.IsUnitary := by
  first | exact @GlobalTheory.HeckeUnitaryInf.isUnitary_of_hasInf | exact GlobalTheory.HeckeUnitaryInf.isUnitary_of_hasInf | (intros; apply GlobalTheory.HeckeUnitaryInf.isUnitary_of_hasInf <;> assumption)
