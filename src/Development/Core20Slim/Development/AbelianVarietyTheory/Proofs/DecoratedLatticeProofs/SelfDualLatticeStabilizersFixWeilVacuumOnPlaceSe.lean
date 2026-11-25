module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.OmSplitHalves
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatticeVacuumIffPlacewiseStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InLatticeStabilizerAtPlaceOfSupportedStabilizerStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsPlaceStabilizerPartialProductsFiniteSetStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TendstoUnitaryAdelicPointsAgreeOnGrowingFinsetStatement
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnramifiedCharacter
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Classical
public import Init.Core
public import Init.Data.List.Basic
public import Init.Data.List.Lemmas
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Notation.Prod
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Empty
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Order.Filter.AtTopBot.Defs
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.Filter.Tendsto
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Neighborhoods
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer
open Filter Topology

namespace GlobalTheory.StabSetFix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem stab_fix_vac : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : Om S T), IsWeilDatumO ψ S T χS χT om → ∀ (LS : Lat S) (LT : Lat T), IsSelfDualC S LS → IsSelfDualC T LT → ∀ (P : Pl D → Prop), (∀ v, P v → Tame D v ∧ GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D χS v ∧ GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D χT v) → ∀ f, Vac ψ S T LS LT P f → ∀ κ κ', InK S LS P κ → InK T LT P κ' → om (κ, κ') f = f := by
  intro D ψ S T χS χT om hW LS LT hS hT P hP f hf κ κ' hκ hκ'
  have hloc := ((GlobalTheory.T.latticeVacuum_iff_placewise D ψ S T χS χT om hW LS LT hS hT P (fun v hv => (hP v hv).1) f).1.1 hf)
  have one_inK : ∀ (V : HSp D) (L : Lat V) (v : Pl D), InK V L (· = v) 1 := by
    intro V L v
    refine ⟨one_mem _, fun y _ => ?_⟩
    have h1 : Formalism.L2.Theta.mt V 1 = 1 := by simp [Formalism.L2.Theta.mt]
    rw [h1, Matrix.one_mulVec]
  have single : ∀ v, P v → ∀ y y', InK S LS (· = v) y → InK T LT (· = v) y' → om (y, y') f = f :=
    fun v hv y y' hy hy' => GlobalTheory.VacStabFixed.vacFixedAt D v ψ S T χS χT om hW (hP v hv).2.1 (hP v hv).2.2 LS LT hS hT f
      hloc.1 (hloc.2 v hv).2 y y' (GlobalTheory.T.inLatticeStabilizerAtPlace_of_supportedStabilizer D S LS v y hS hy) (GlobalTheory.T.inLatticeStabilizerAtPlace_of_supportedStabilizer D T LT v y' hT hy')
  have listS : ∀ l : List (GA D S), (∀ y ∈ l, ∃ v, P v ∧ InK S LS (· = v) y) → om (l.prod, 1) f = f := by
    intro l
    induction l with
    | nil => intro _; rw [List.prod_nil, Prod.mk_one_one, map_one, Module.End.one_apply]
    | cons y l ih =>
      intro h
      obtain ⟨v, hv, hy⟩ := h y (List.mem_cons_self ..)
      have e : ((y * l.prod, (1 : GA D T)) : GA D S × GA D T) = (y, 1) * (l.prod, 1) := by simp
      rw [List.prod_cons, e, map_mul, Module.End.mul_apply, ih (fun z hz => h z (List.mem_cons_of_mem _ hz)),
        single v hv y 1 hy (one_inK T LT v)]
  have listT : ∀ l : List (GA D T), (∀ y ∈ l, ∃ v, P v ∧ InK T LT (· = v) y) → om (1, l.prod) f = f := by
    intro l
    induction l with
    | nil => intro _; rw [List.prod_nil, Prod.mk_one_one, map_one, Module.End.one_apply]
    | cons y l ih =>
      intro h
      obtain ⟨v, hv, hy⟩ := h y (List.mem_cons_self ..)
      have e : (((1 : GA D S), y * l.prod) : GA D S × GA D T) = (1, y) * (1, l.prod) := by simp
      rw [List.prod_cons, e, map_mul, Module.End.mul_apply, ih (fun z hz => h z (List.mem_cons_of_mem _ hz)),
        single v hv 1 y (one_inK S LS v) hy]
  choose lS hlS hiS hinS houtS using GlobalTheory.T.exists_placeStabilizer_partialProducts_finiteSet D S LS P κ hS hκ
  choose lT hlT hiT hinT houtT using GlobalTheory.T.exists_placeStabilizer_partialProducts_finiteSet D T LT P κ' hT hκ'
  have tS := GlobalTheory.T.tendsto_unitaryAdelicPoints_agree_on_growing_finset D S κ (fun Fs => (lS Fs).prod) hiS hinS houtS
  have tT := GlobalTheory.T.tendsto_unitaryAdelicPoints_agree_on_growing_finset D T κ' (fun Fs => (lT Fs).prod) hiT hinT houtT
  funext w
  have hc := ((hW.om_cont f hloc.1 w).tendsto (κ, κ')).comp (tS.prodMk_nhds tT)
  have heq : ∀ Fs, f w = ((fun p : GA D S × GA D T => om p f w) ∘ fun Fs => ((lS Fs).prod, (lT Fs).prod)) Fs := by
    intro Fs
    have e : (((lS Fs).prod, (lT Fs).prod) : GA D S × GA D T) = ((lS Fs).prod, 1) * (1, (lT Fs).prod) := by simp
    simp only [Function.comp_apply]
    rw [e, map_mul, Module.End.mul_apply, listT _ (hlT Fs), listS _ (hlS Fs)]
  exact tendsto_nhds_unique hc (tendsto_const_nhds.congr heq)

end GlobalTheory.StabSetFix
