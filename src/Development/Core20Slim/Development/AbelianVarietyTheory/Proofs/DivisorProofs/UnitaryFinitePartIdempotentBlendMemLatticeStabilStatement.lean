module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryFinitePartIdempotentBlendMemLatticeStabil
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.MemHalfCosetSelf
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStdLatEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOrEqOfPlaceIdem
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIdempotentPlaceChartFiniteAdeles
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalisationEqStdAtOfCongruentOneAtPrime
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteAdeleCMMemIntegralOfIdempotent
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Formalism.LocalToGlobal.HermitianColumns.InLocalDiscriminantKernel
public import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryFinitePart_idempotentBlend_mem_latticeStabilizer : ∀ {D : D7} (V : HSp D) (g : GA D V) (β₀ β₁ : GL (Fin V.rank) (Lev.EAf D)),
    (∀ i j, β₀.val i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ∧ (β₀⁻¹).val i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) →
    (∀ i j, β₁.val i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ∧ (β₁⁻¹).val i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) →
    ∀ ε φ : Lev.EAf D, ε ∈ Formalism.L2.Herm.intAf D.host.F D.host.E → φ ∈ Formalism.L2.Herm.intAf D.host.F D.host.E →
    (Formalism.L2.Theta.mt V g).map (toEAf D) = (1 - ε - φ) • (1 : Matrix (Fin V.rank) (Fin V.rank) (Lev.EAf D)) +
      ε • (β₁ * β₀⁻¹).val + φ • ((β₀ * β₁⁻¹).val.map (GlobalTheory.AdelicLatMove.cF D)).transpose →
    (Formalism.L2.Theta.mt V g⁻¹).map (toEAf D) = (1 - ε - φ) • (1 : Matrix (Fin V.rank) (Fin V.rank) (Lev.EAf D)) +
      ε • (β₀ * β₁⁻¹).val + φ • ((β₁ * β₀⁻¹).val.map (GlobalTheory.AdelicLatMove.cF D)).transpose →
    Formalism.IndefR.Lev.finE V g ∈ Formalism.L2.DIV.St β₁ := by
  first | exact @GlobalTheory.StabMove.finE_mem_St | exact GlobalTheory.StabMove.finE_mem_St | (intros; apply GlobalTheory.StabMove.finE_mem_St <;> assumption)
