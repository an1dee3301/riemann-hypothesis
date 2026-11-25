module

public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaEV0EqICPqRows
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Realised
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.Divisors.MulVecEqOfBasis
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.Divisors.TieTest
public import Development.AbelianVarietyTheory.Definitions.Divisors.TupleReadBaseTupleEqFamily
public import Development.AbelianVarietyTheory.Definitions.Divisors.TwistedPlaceChoiceLiesOverPair
public import Formalism.LocalRingCardinality.DataDIV
public import Formalism.LocalRingCardinality.DataExtra
public import Formalism.LocalRingCardinality.DataGatTies
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataParams₂
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.Divisibility.ClassSum
public import Formalism.LocalToGlobal.Divisibility.HeckeRI
public import Formalism.LocalToGlobal.Divisibility.InertRationalAdjoint
public import Formalism.LocalToGlobal.Divisibility.LiftLat
public import Formalism.LocalToGlobal.Divisibility.RowLat
public import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
public import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
public import Formalism.LocalToGlobal.IndefiniteReal.FaceOf3
public import Formalism.LocalToGlobal.IndefiniteReal.NormalDecomposition.LiftHeckeOperators
public import Formalism.LocalToGlobal.IndefiniteReal.PackageFromPrimitiveStatements
public import Formalism.LocalToGlobal.IndefiniteReal.PartsOrth
public import Formalism.LocalToGlobal.IndefiniteReal.PrimitiveStatementsWithPassage
public import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
public import Formalism.LocalToGlobal.ProjectiveLattices.CuspidalL2Subspace
public import Formalism.LocalToGlobal.ProjectiveLattices.EmbKCoe
public import Formalism.LocalToGlobal.ProjectiveLattices.FamilyUniformisationBasePointOrthogonalBis
public import Formalism.LocalToGlobal.ProjectiveLattices.PartitionExtendByZeroAntitone
public import Formalism.SharpRestriction.GrowthBounds.IsResidueClassZero
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Classical
public import Init.Core
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Map
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.RepresentationTheory.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PushInvertible

@[expose] public section

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain Formalism.L2 Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Indef Formalism.IndefR.Cx GlobalTheory.BigTop GlobalTheory.BigTop.Fun
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.BigTop.Fun
open Formalism.L2.DIV Formalism.IndefR.Cx Formalism.IndefR.Cx.CxData
open scoped InnerProductSpace Matrix
set_option maxHeartbeats 1000000 in
theorem theta_eV0_eq_iC_Pq_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz), p.PointConditions' → ∀ (t : Tup p) (y : Fin ((Df p).nV t) → D.what₂.LL), (p.R.toCx3 p.F).Θ t ((p.R.toCx3 p.F).jR t (eV0 p t y)) = (p.R.toCx3 p.F).iC p.F.cr false t (cpt p.P.A3.fam3.base3.v0.embedding (((Df p).Pq t).mulVec y)) := by
  intro D L hT Gi Gl Kc Y cX ex Csz p hp t y
  have hCx := Formalism.IndefR.Links.complex_data_conditions_base_level_of_primitive_links hp.ok hp.sep p.charW hp.prim
  rw [iC_cpt_eq_theta_toR, TieModel.toR_eq]
  let y' : Fin ((p.P.A3.A.fam.R t).nV (p.P.A3.A.fam.lvl p.P.P0 p.P.ψ0)) → D.what₂.LL := y
  have hu := sub_zE_Pq_mem_U (p.P.A3.A.fam.R t) (p.P.A3.A.fam.lvl p.P.P0 p.P.ψ0) ((p.R.toCx3 p.F).zs.Z t)
    ((hCx.wf false).Pq_surj t) y'
  have h := theta_jR_eq_zero_of_perp _ p.F.cv hCx.jIsoR hCx.ratZ t (eV0 p t (y' - ((p.P.A3.A.fam.R t).zE (p.P.A3.A.fam.lvl p.P.P0 p.P.ψ0)
      ((p.R.toCx3 p.F).zs.Z t)).mulVec (((Df p).Pq t).mulVec y))) (fun w hw =>
    csum_goodPart_perp_eq_zero (p.P.A3.A.fam.R t) 1 (hp.ok.ok2.what₂ t) _ hp.ok.ok2.conj _ hp.ok.ok2.irr _
      (fun g => Submodule.map_le_iff_le_comap.mp (hCx.stable.1 t (Sum.inr g))) _ hu w hw)
  erw [(eV0 p t).map_sub] at h
  have h2 := ((p.R.toCx3 p.F).jR t).map_sub (eV0 p t y') (eV0 p t (((p.P.A3.A.fam.R t).zE (p.P.A3.A.fam.lvl p.P.P0 p.P.ψ0)
      ((p.R.toCx3 p.F).zs.Z t)).mulVec (((Df p).Pq t).mulVec y)))
  erw [h2, map_sub] at h
  exact sub_eq_zero.mp h
end GlobalTheory.BigTop.Fun
end
end
