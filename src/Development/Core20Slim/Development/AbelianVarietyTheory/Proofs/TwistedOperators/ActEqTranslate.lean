module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicUnitaryEqRealMulFiniteSplit
public import Batteries.Logic
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.Divisibility.ClassSum
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Formalism.LocalToGlobal.Divisibility.LiftLat
public import Formalism.LocalToGlobal.Divisibility.RowLat
public import Formalism.LocalToGlobal.HermitianColumns.InLocalDiscriminantKernel
public import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
public import Formalism.LocalToGlobal.IndefiniteReal.Bridge
public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.SatakeDualWeyl.Statement
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.PropLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Set.CoeSort
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FormAction

theorem exists_rangeRestrict_eq {G H : Type} [Group G] [Group H] (f : G →* H) (K : Subgroup G)
    (h : ∀ g, ∃ a ∈ f.ker, ∃ k ∈ K, g = a * k) (x : f.range) : ∃ k ∈ K, f.rangeRestrict k = x := by
  obtain ⟨_, g, rfl⟩ := x
  obtain ⟨a, ha, k, hk, rfl⟩ := h g
  refine ⟨k, hk, Subtype.ext ?_⟩
  show f k = f (a * k)
  rw [map_mul, MonoidHom.mem_ker.1 ha, one_mul]

theorem exists_lift {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank)
    (q : (levEnv V β L).Q) : ∃ κ, (finHom V).rangeRestrict κ = q.1 ∧
    IsLevelLift V β L (rTup β L (Formalism.UG.bc (swapAE D) q.1.1)) κ ∧
      ((((levEnv V β L).ch q)⁻¹ : ℂˣ) : ℂ) = (levChi V β (flagL L) κ)⁻¹ := by
  refine (exists_rangeRestrict_eq (finHom V) (GfC V) (GlobalTheory.UnitarySplit.real_finite_split D V).1 q.1).imp fun k hk => ?_
  have e0 : finHom V k = q.1.1 := congrArg Subtype.val hk.2
  have e1 : finE V k = Formalism.UG.bc (swapAE D) q.1.1 := (finE_eq V k).trans (congrArg (Formalism.UG.bc (swapAE D)) e0)
  have e2 : (levEnv V β L).ch q = levFn β (flagL L) (Formalism.UG.bc (swapAE D) q.1.1) := rfl
  have hc : levChi V β (flagL L) k = (((levEnv V β L).ch q : ℂˣ) : ℂ) :=
    congrArg Units.val ((congrArg (levFn β (flagL L)) e1).trans e2.symm)
  have h1 : Formalism.UG.bc (swapAE D) q.1.1 ∈ lev D.sp.cm V.gram β (flagL L) := q.2
  have hp : finE V k ∈ parLev D.sp.cm V.gram β L := e1.symm ▸ h1.1
  exact ⟨hk.2, ⟨hk.1, hp, congrArg (rTup β L) e1⟩, (Units.val_inv_eq_inv_val _).trans (congrArg (·⁻¹) hc.symm)⟩

theorem act_eq_translate : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.grp_red_R → R.models_jX → ∀ t (g : G) (x : (A.fam.R t).S.Forms), ∃ κ, IsLevelLift D.sp.X' R.βX (R.datXt t) (R.eG g) κ ∧ ∀ h, (R.HX t).e (R.jX t ((A.fam.R t).r g x)) h = (levChi _ R.βX (flagL (R.datXt t)) κ)⁻¹ • (R.HX t).e (R.jX t x) (h * (finHom _).rangeRestrict κ) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R hred hj t g x
  refine ((R.B.R t).act_tie.red_surj g).elim fun q hq => ?_
  have hg : rTup R.βX (R.datXt t) (Formalism.UG.bc (swapAE D) q.1.1) = R.eG g := (hred t q).symm.trans (congrArg R.eG hq)
  have ha := (R.B.R t).act_tie.act_eq g q hq x
  refine (exists_lift D.sp.X' R.βX (R.datXt t) q).imp fun κ hκ => ⟨hg ▸ hκ.2.1, fun h => ?_⟩
  have e1 := congrFun (hj t ((A.fam.R t).r g x)) h
  have e2 := hj t x
  have e3 := congrFun ha h
  refine (e1.trans e3).trans ?_
  exact congrArg₂ (fun (a : ℂ) (z : R.cX.W) => a • z) hκ.2.2 ((congrFun e2 _).trans (congrArg (fun z => R.B.jR t x (h * z)) hκ.1)).symm

end GlobalTheory.FormAction

end
