module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.NormComparisonConstants
public import Formalism.LocalToGlobal.ProjectiveLattices.DepthTie
public import Development.AbelianVarietyTheory.Definitions.Jets.EmbShortThLeThetaPlain
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsNormOneRootCongruentOddHostField
public import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Maximal
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

@[expose] public section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.RunJoin GlobalTheory.FinalJoin GlobalTheory.FinalJoin2 GlobalTheory.CompRat GlobalTheory.Member
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IdeleNinety


theorem conj_ne_one (D : D7) : cF D ≠ 1 := by
  intro h
  obtain ⟨P, hM⟩ := Ideal.exists_maximal (𝓞 D.host.E)
  obtain ⟨t, s, hs, hts⟩ := D.sp.cm.cmUnram.2.2 P hM
  have hs' : (s : D.host.E) = cF D (t : D.host.E) := hs
  rw [h] at hs'
  have : s = t := Subtype.ext hs'
  rw [this, sub_self] at hts
  exact hts P.zero_mem




end GlobalTheory.IdeleNinety
