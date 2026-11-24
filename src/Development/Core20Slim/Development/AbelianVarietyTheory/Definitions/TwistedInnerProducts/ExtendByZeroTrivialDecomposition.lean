module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TowerEx
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CmHostImaginaryGeneratorNeZero
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittDecompositionMixedCoordsRankZero
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaHeisenbergConjugationNegHermitianSpace
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EqZeroOfLintegralEqZero
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MapFinNeg
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfPartOneSubEInfSmul
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilLatticeVacuumStabilizerSplittingCharacters
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsCompactParahoricLevelAndContainsLifts
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowBesZeroE
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilDatumPowersUnramifiedEtaTilde
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.SatakeParameters.AbsNormCoprimeOfSup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaIntegrandIntegrable
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AdelicUnitaryTopCong
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
public import Formalism.LocalToGlobal.HermitianColumns.InLocalDiscriminantKernel
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
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
public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Empty
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Filter.Defs
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.OpenSubgroup
public import Mathlib.Topology.Basic
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Defs.Induced

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AscInh

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ}


theorem stab_compact_open (W : HSp D) (β : GL (Fin W.rank) (Lev.EAf D)) :
    IsCompact (Lev.levA W (Formalism.L2.DIV.St β) : Set (GA D W)) ∧
      IsOpen (((Lev.levA W (Formalism.L2.DIV.St β)).subgroupOf (GfC W) : Subgroup (GfC W)) : Set (GfC W)) := by
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig W.gram
  have ho : IsOpen (((Formalism.L2.DIV.St β).comap (Lev.finE W) : Subgroup (GA D W)) : Set (GA D W)) := by
    refine Subgroup.isOpen_of_mem_nhds _ (g := 1) ?_
    filter_upwards [GlobalTheory.ThetaIntegrand.eventually_princ W β ∅] with κ hh
    exact hh.2.1
  obtain ⟨C, hC, hCm⟩ := GlobalTheory.ParahoricCompact.exists_compact W β
  refine ⟨hC.of_isClosed_subset ((GlobalTheory.Ker.CongTop.isClosed_GfC W).inter (Subgroup.isClosed_of_isOpen _ ho))
    fun k hk => hCm k hk.1 hk.2, ?_⟩
  convert ho.preimage (continuous_subtype_val (p := fun x => x ∈ GfC W)) using 1
  ext k
  exact ⟨fun hk => hk.2, fun hk => ⟨k.2, hk⟩⟩







variable {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc)




end GlobalTheory.AscInh

end
