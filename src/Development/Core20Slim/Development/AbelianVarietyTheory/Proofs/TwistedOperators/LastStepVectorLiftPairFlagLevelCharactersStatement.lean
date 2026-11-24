module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.LastStepVectorLiftPairFlagLevelCharacters
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Formalism.LocalToGlobal.Divisibility.LiftLat
public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lastVector_lift_pair_flagLevel_characters : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.models_inf → R.chain_ωX → R.chain_vX → ∀ t (g0 : G0 R.Pg D.R.r) κ κ', IsLevelLift (Yc D (D.R.m - 1)) (R.βY (D.R.m - 1)) (R.datYt t (D.R.m - 1) R.triv) g0 κ → IsLevelLift D.sp.X' R.βX (R.datXt t) g0 κ' → (levChi _ (R.βY (D.R.m - 1)) (flagL (R.datYt t (D.R.m - 1) R.triv)) κ)⁻¹ • R.ωX t (κ, κ') (R.vX t) = (levChi _ R.βX (flagL (R.datXt t)) κ')⁻¹ • R.vX t := by
  first | exact @GlobalTheory.StepLaw.last_step_law | exact GlobalTheory.StepLaw.last_step_law | (intros; apply GlobalTheory.StepLaw.last_step_law <;> assumption)
