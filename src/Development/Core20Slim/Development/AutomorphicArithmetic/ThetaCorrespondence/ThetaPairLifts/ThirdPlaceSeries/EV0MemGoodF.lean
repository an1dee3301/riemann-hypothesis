module

public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.Divisors.TieTest
public import Formalism.LocalToGlobal.IndefiniteReal.CxLemmas
public import Formalism.LocalToGlobal.IndefiniteReal.CxPassRep
public import Formalism.LocalToGlobal.Divisibility.RowLatLemmas
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Realised
public import Development.AbelianVarietyTheory.Definitions.Divisors.TupleReadBaseTupleEqFamily
public import Development.AbelianVarietyTheory.Definitions.Divisors.TwistedPlaceChoiceLiesOverPair
public import Formalism.LocalRingCardinality.DataDIV
public import Formalism.LocalRingCardinality.DataExtra
public import Formalism.LocalRingCardinality.DataGatTies
public import Formalism.LocalRingCardinality.DataParams₂
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.Divisibility.ClassSum
public import Formalism.LocalToGlobal.Divisibility.GoodPartHermitianSpec
public import Formalism.LocalToGlobal.Divisibility.HeckeRI
public import Formalism.LocalToGlobal.Divisibility.InertRationalAdjoint
public import Formalism.LocalToGlobal.Divisibility.LiftLat
public import Formalism.LocalToGlobal.Divisibility.ProjLemmas
public import Formalism.LocalToGlobal.Divisibility.RowLat
public import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
public import Formalism.SharpRestriction.GrowthBounds.IsResidueClassZero
public import Init.Core
public import Init.Data.Function
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Range
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Order.Notation

@[expose] public section

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain Formalism.L2 Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Indef Formalism.IndefR.Cx GlobalTheory.BigTop GlobalTheory.BigTop.Fun
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.BigTop.Fun
theorem eV0_mem_goodF_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz), p.PointConditions' → ∀ (t : Tup p) (y : Fin ((Df p).nV t) → D.what₂.LL), eV0 p t y ∈ (p.P.A3.A.fam.R t).goodF p.P.A3.A.fam.X := by
  intro D L hT Gi Gl Kc Y cX ex Csz p _ t y
  set B := p.P.A3.A.fam.R t
  set F := p.P.A3.A.fam
  obtain ⟨u, hu⟩ := Formalism.IndefR.CxPass.PassRep.range_vE_le B F.X p.P.P0 p.P.ψ0 ⟨y, rfl⟩
  have hrange : LinearMap.range (B.vE ⟨F.X, ⊥, 1⟩).mulVecLin =
      LinearMap.range (B.S.gaMat B.r (goodAt F.X ⊥ 1)).mulVecLin :=
    (image_idempotent_spec _ _ (B.S.gaMat B.r (goodAt F.X ⊥ 1))).2
  obtain ⟨z, hz⟩ : (B.vE ⟨F.X, ⊥, 1⟩).mulVecLin u ∈ LinearMap.range (B.S.gaMat B.r (goodAt F.X ⊥ 1)).mulVecLin :=
    hrange ▸ ⟨u, rfl⟩
  refine ⟨B.S.basis.equivFun.symm z, B.S.basis.equivFun.injective ?_⟩
  rw [← CSD.gaMat_mulVec_equivFun, LinearEquiv.apply_symm_apply]
  simp only [Matrix.mulVecLin_apply] at hu hz
  rw [hz, hu]
  show _ = B.S.basis.equivFun (B.S.basis.equivFun.symm ((B.vE (F.lvl p.P.P0 p.P.ψ0)).mulVecLin y))
  rw [LinearEquiv.apply_symm_apply]
  rfl
end GlobalTheory.BigTop.Fun
end
end
