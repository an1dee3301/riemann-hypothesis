module

public import Mathlib
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DenominatorNormQuadraticExtension
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsLatIntVec
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Order.Kleene
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm

@[expose] public section

open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.CompanionTheory.SiegelND.Integ.Hua GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
open scoped Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.denominator_norm_quadratic_extension : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], Module.finrank F E = 2 → ∀ x : F, Ideal.absNorm (den E (algebraMap F E x)) = Ideal.absNorm (den F x) ^ 2 := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.DenMap.absNorm_den_algebraMap | exact GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.DenMap.absNorm_den_algebraMap | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.DenMap.absNorm_den_algebraMap <;> assumption)
