module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
public import Formalism.LocalToGlobal.ProjectiveLattices.HasDataCondition
public import Formalism.LocalToGlobal.ProjectiveLattices.FamilyUniformisationBasePointOrthogonalBis
public import Formalism.LocalToGlobal.ProjectiveLattices.RecCond
public import Formalism.LocalToGlobal.ProjectiveLattices.ParCanon
public import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLevelMulSplit
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsDeltaDatumHigherLevel
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsEquivariantFunOnSpanningFamilies
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIdempotentSectionFamily
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsComponentWeight
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicCompletionFractionalIdealProperties
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianCodeWordStagesRingOfIntegersFull
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianCodeWordStagesHasRootOfUnity
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.FractionalIdeal.Basic
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FinalJoin.CondTest

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem integral_of_mem_intAE {x : D.host.E} (hx : (1 : Af D.host.F) ⊗ₜ[D.host.F] x ∈ intAE D) :
    ∃ y : 𝓞 D.host.E, (y : D.host.E) = x := by
  have h : intAE D ≤ GlobalTheory.AdLat.hat1 D.host.F
      ((1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) : Set D.host.E) := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨a, ha, y, rfl⟩
    exact GlobalTheory.AdLat.tmul_mem_adelicCompletion_of_integral D.host.F ha ((FractionalIdeal.mem_one_iff _).2 ⟨y, rfl⟩)
  exact (FractionalIdeal.mem_one_iff _).1 ((GlobalTheory.AdLat.one_tmul_mem_adelicCompletion_fractionalIdeal_iff D.host.F 1 x).1 (h hx))

end GlobalTheory.FinalJoin.CondTest
