module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeCharLocPowEqOneOnLocalUnits
public import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterUnramifiedAeAndExistsLevel
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas

@[expose] public section

open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeChar_loc_pow_eq_one_on_localUnits : ∀ (L : Type) [Field L] [NumberField L] (χ : Formalism.L2.Host.HChar L) (v : HeightOneSpectrum (𝓞 L)) (x : (v.adicCompletion L)ˣ), Formalism.L2.Host.IsUnitAt v x → ∃ m : ℕ, 0 < m ∧ χ.loc v x ^ m = 1 := by
  first | exact @GlobalTheory.LocUnitPow.loc_pow_eq_one | exact GlobalTheory.LocUnitPow.loc_pow_eq_one | (intros; apply GlobalTheory.LocUnitPow.loc_pow_eq_one <;> assumption)
