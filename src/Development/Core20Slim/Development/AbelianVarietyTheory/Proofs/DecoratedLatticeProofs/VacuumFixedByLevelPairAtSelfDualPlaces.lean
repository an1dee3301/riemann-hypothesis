module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValueDoubleExact
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualLatticeStabilizersFixWeilVacuumOnPlaceSeStatement
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnramifiedCharacter
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Classical
public import Init.Core
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
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Notation.Prod
public import Mathlib.Algebra.Quotient
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Quotient.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.Order.BoundedOrder.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Notation
public import Mathlib.Order.SetNotation
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Lattice
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Tactic.Push

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair)
open GlobalTheory.FinPl

noncomputable section

namespace GlobalTheory.VacFixP

theorem idAt_eq_bot {D : D7} {P : Pl D → Prop} (hP : ∀ v, ¬ P v) : idAt D P = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Ideal.mem_bot]
  refine GlobalTheory.FinPlLoc.eq_zero_of_comp x hx.1 fun w => ?_
  exact (Submodule.mem_iInf _).1 hx.2 ⟨w, hP w⟩

theorem eq_one_of_grpAt {D : D7} {S : HSp D} {P : Pl D → Prop} (hP : ∀ v, ¬ P v) {κ : GA D S}
    (h : κ ∈ grpAt S P) : κ = 1 := by
  unfold grpAt congGrp at h
  rw [idAt_eq_bot hP, MonoidHom.mem_ker, MonoidHom.comp_apply] at h
  have h2 : matHom S κ = 1 := by
    apply Units.ext
    ext i j
    have := congrArg (fun g : GL (Fin S.rank) (AE D ⧸ (⊥ : Ideal (AE D))) => g.val i j) h
    simp only [Matrix.GeneralLinearGroup.map_apply, Units.val_one] at this
    rw [Units.val_one]
    rw [Matrix.one_apply] at this ⊢
    have h1 : ((if i = j then 1 else 0 : AE D ⧸ (⊥ : Ideal (AE D)))) = Ideal.Quotient.mk ⊥ (if i = j then 1 else 0) := by
      split_ifs <;> simp
    rw [h1, Ideal.Quotient.eq, Ideal.mem_bot, sub_eq_zero] at this
    exact this
  unfold matHom at h2
  exact Subgroup.subtype_injective _ (h2.trans (map_one _).symm)

theorem vac_fix_on : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : Om S T), IsWeilDatumO ψ S T χS χT om → ∀ (LS : Lat S) (LT : Lat T) (P : Pl D → Prop), (∀ v, P v → IsSelfDualC S LS ∧ IsSelfDualC T LT ∧ Tame D v ∧ CharUnramAt D χS v ∧ CharUnramAt D χT v) → ∀ f, Vac ψ S T LS LT P f → ∀ κ κ', InK S LS P κ → InK T LT P κ' → om (κ, κ') f = f := by
  intro D ψ S T χS χT om hW LS LT P hP f hf κ κ' hκ hκ'
  by_cases hex : ∃ v, P v
  · obtain ⟨v, hv⟩ := hex
    obtain ⟨hS, hT, -⟩ := hP v hv
    exact GlobalTheory.T.selfDualLatticeStabilizers_fix_weilVacuum_on_placeSet D ψ S T χS χT om hW LS LT hS hT P (fun w hw => (hP w hw).2.2) f hf κ κ' hκ hκ'
  · push_neg at hex
    rw [eq_one_of_grpAt hex hκ.1, eq_one_of_grpAt hex hκ'.1, Prod.mk_one_one, map_one]
    rfl

end GlobalTheory.VacFixP
