module

public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GenFinSt
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntCoordsEv
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinPartIdemMulMemIff
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.AtTauExUniqueHolds
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnramifiedCharacter
public import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
public import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
public import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.InfFam
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Classical
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.NonUnitalHom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Empty
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Finsupp.SMul
public import Mathlib.Data.Finsupp.SMulWithZero
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.Order.SetNotation
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Lattice
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Free

@[expose] public section

noncomputable section

open scoped Matrix TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open GlobalTheory.AdelicU GlobalTheory.StdUnn IsDedekindDomain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace PositivityTheory.Rg.Sw.Glob.GenUnitH

variable {D : D7}

theorem compAt_eq (v : GlobalTheory.FinPl.Pl D) (z : AE D) :
    GlobalTheory.FinPl.compAt D v z = GlobalTheory.AdelicU.compFin D.host.F D.host.E v z :=
  GlobalTheory.EmbChart.map_evalV_map_sndA v z

theorem compFin_tensAt_ne {v w : GlobalTheory.FinPl.Pl D} (h : w ≠ v) (y : Ev D v) :
    GlobalTheory.AdelicU.compFin D.host.F D.host.E w (GlobalTheory.EmbChart.tensAt D.host.E v y) = 0 := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy, add_zero]
  | tmul a x =>
    show GlobalTheory.AdelicU.evFin D.host.F w (GlobalTheory.EmbChart.atPlace v a) ⊗ₜ[D.host.F] x = 0
    rw [show GlobalTheory.AdelicU.evFin D.host.F w (GlobalTheory.EmbChart.atPlace v a) = 0 from GlobalTheory.AdelicU.evalV_singleFin_ne h a,
      TensorProduct.zero_tmul]

theorem infPart_tensAt (v : GlobalTheory.FinPl.Pl D) (y : Ev D v) : infPart D (GlobalTheory.EmbChart.tensAt D.host.E v y) = 0 := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy, add_zero]
  | tmul a x =>
    show fstA D.host.F (GlobalTheory.EmbChart.atPlace v a) ⊗ₜ[D.host.F] x = 0
    rw [show fstA D.host.F (GlobalTheory.EmbChart.atPlace v a) = 0 from rfl, TensorProduct.zero_tmul]

theorem tensAt_mem_idAt (v : GlobalTheory.FinPl.Pl D) (y : Ev D v) :
    GlobalTheory.EmbChart.tensAt D.host.E v y ∈ GlobalTheory.FinPl.idAt D (· = v) := by
  unfold GlobalTheory.FinPl.idAt
  refine Ideal.mem_inf.2 ⟨RingHom.mem_ker.2 (infPart_tensAt v y), ?_⟩
  refine (Submodule.mem_iInf _).2 fun w => RingHom.mem_ker.2 ?_
  rw [compAt_eq]
  exact compFin_tensAt_ne w.2 y

theorem tensAt_mem_intAt (v : GlobalTheory.FinPl.Pl D) (y : Ev D v) (hy : y ∈ intLoc D.host.F D.host.E v) :
    GlobalTheory.EmbChart.tensAt D.host.E v y ∈ GlobalTheory.FinPl.intAt D (· = v) :=
  ⟨tensAt_mem_idAt v y, (GlobalTheory.EmbChart.finPart_tensAt_mem_iff y).2 hy⟩

theorem glueEntry (z : ∀ v : GlobalTheory.FinPl.Pl D, Ev D v) (hz : ∀ v, z v ∈ intLoc D.host.F D.host.E v) :
    ∃ s : AE D, infPart D s = 0 ∧ ∀ v, GlobalTheory.FinPl.compAt D v s = z v := by
  obtain ⟨s, hs0, hs⟩ := GlobalTheory.FinPlLoc.glue D (fun v => GlobalTheory.EmbChart.tensAt D.host.E v (z v))
    (fun v => tensAt_mem_idAt v (z v)) ⟨∅, fun v _ => tensAt_mem_intAt v (z v) (hz v)⟩
  refine ⟨s, hs0, fun v => ?_⟩
  have h := hs v
  unfold GlobalTheory.FinPl.idOff at h
  have h2 : GlobalTheory.FinPl.compAt D v (s - GlobalTheory.EmbChart.tensAt D.host.E v (z v)) = 0 :=
    RingHom.mem_ker.1 ((Submodule.mem_iInf _).1 h ⟨v, rfl⟩)
  rw [map_sub, sub_eq_zero, compAt_eq v (GlobalTheory.EmbChart.tensAt _ v _), GlobalTheory.EmbChart.compFin_tensAt] at h2
  exact h2

theorem finExt {x y : Af D.host.F ⊗[D.host.F] D.host.E}
    (h : ∀ v : GlobalTheory.FinPl.Pl D, GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin D v x = GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin D v y) : x = y := by
  have key : ∀ (x : Af D.host.F ⊗[D.host.F] D.host.E) (v : GlobalTheory.FinPl.Pl D) (k : Fin 2),
      (Algebra.TensorProduct.basis (Fv D.host.F v) (Formalism.IndefR.Eqv.basE D)).repr (GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin D v x) k =
        evalV D.host.F v ((Formalism.IndefR.Eqv.basAf D).repr x k) := by
    intro x v k
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [map_add (f := _), Finsupp.add_apply, ha, hb]
    | tmul a e =>
      show (Algebra.TensorProduct.basis (Fv D.host.F v) (Formalism.IndefR.Eqv.basE D)).repr
        (evalV D.host.F v a ⊗ₜ[D.host.F] e) k = _
      rw [Formalism.IndefR.Eqv.basAf, Algebra.TensorProduct.basis_repr_tmul, Algebra.TensorProduct.basis_repr_tmul]
      simp only [Finsupp.smul_apply, Finsupp.mapRange_apply, smul_eq_mul, map_mul, AlgHom.commutes]
  apply (Formalism.IndefR.Eqv.basAf D).ext_elem
  intro k
  apply GlobalTheory.AdelicU.af_ext
  intro u
  rw [← key, ← key, h]

end PositivityTheory.Rg.Sw.Glob.GenUnitH

namespace PositivityTheory.Rg.Sw.Glob

theorem unitAE : UnitAE := by
  intro D d hτ hv
  choose z' hz'mem hz'inv using fun v => (hv v).2
  obtain ⟨s, -, hs⟩ := GenUnitH.glueEntry z' hz'mem
  let x := Formalism.IndefR.Eqv.glueA D (Formalism.IndefR.Eqv.splitInv D fun τ => (Formalism.IndefR.Eqv.psiT D τ d)⁻¹) (finPart D s)
  have hx : ∀ v, GlobalTheory.FinPl.compAt D v x = z' v := fun v => by
    show GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin D v (finPart D x) = _
    rw [Formalism.IndefR.Eqv.finPart_glueA]
    exact hs v
  have hdx : d * x = 1 := by
    apply Formalism.IndefR.Eqv.ae_ext' D
    · intro τ
      rw [map_mul, Formalism.IndefR.Eqv.psiT_glueA, mul_inv_cancel₀ (hτ τ), map_one]
    · apply GenUnitH.finExt
      intro v
      show GlobalTheory.FinPl.compAt D v (d * x) = GlobalTheory.FinPl.compAt D v 1
      rw [map_mul, map_one, hx v, hz'inv v]
  exact ⟨⟨d, x, hdx, by rw [mul_comm]; exact hdx⟩, rfl⟩

end PositivityTheory.Rg.Sw.Glob
