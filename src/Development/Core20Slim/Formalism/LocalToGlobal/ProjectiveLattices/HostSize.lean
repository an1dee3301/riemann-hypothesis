module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GCauchyStatement
public import Formalism.SharpRestriction.ElevenLe
public import Formalism.SharpRestriction.Divisibility.WeightAlgebra
public import Formalism.LocalRingCardinality.DataParams
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Formalism.FrobeniusOrbits.RealSubfieldLeCompositum
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.ConjugateConjugate
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.TraceIntegralBasis
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MajorantNormalForms
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.RealPlaceEmbeddings
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.QuadraticLatticeForms
public import Development.Core20Slim.Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.LogQdLeRd
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.HostCls
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ZsmulGeneratorEqZeroOfProjection
public import Init.Core
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

noncomputable section

namespace Formalism.L2.Pj

open NumberField Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.ChartRestriction.G.I2

variable {D : D7}

theorem hostSize_finrank (D : D7) : Module.finrank ℚ D.host.E = 2 * D.R.f := by
  rw [D.host.der.finrank_E, Formalism.BasicNotions.Ranks.f_eq_ord (R := D.R)]
  first
  | ring
  | rfl
  | omega
  | (simp only [Formalism.BasicNotions.Ranks.ord]; ring)








end Formalism.L2.Pj
