module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFixedDenominatorFiniteCoordsIntegral
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.DerAlong
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuotientHeightLowerBoundShortIsotropicVector
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.WordDerivatives
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Lie.Basic
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition GlobalTheory.MixedTerm
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_fixed_denominator_finiteCoords_integral : ∀ (D : D7), ∃ d : ℕ, 0 < d ∧ ∀ x : D.host.E, IsIntegral ℤ x → ∀ k, (d : Af D.host.F) * GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.finCoord D ((1 : Af D.host.F) ⊗ₜ[D.host.F] x) k ∈ GlobalTheory.HolDict.ShortVec.intRing D.host.F := by
  first | exact @GlobalTheory.DenInt.exists_den | exact GlobalTheory.DenInt.exists_den | (intros; apply GlobalTheory.DenInt.exists_den <;> assumption)
