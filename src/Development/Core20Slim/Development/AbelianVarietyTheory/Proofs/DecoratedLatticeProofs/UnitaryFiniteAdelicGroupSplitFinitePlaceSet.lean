module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OneSubIdemQMulSelf
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SingleMemIdAt
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlaceIdempotentActsOnSupportedAndOff
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlacewiseToAdelicDecompositionForall
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentTwistedGroupEndomorphism
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.SatakeDualWeyl.Statement
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Subtype.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.PropLemmas
public import Init.SimpLemmas
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
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
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
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.SetNotation
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf  GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinPl.SetCut

section Alg

variable {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n]






end Alg

variable {D : D7}

theorem mem_idOff_iff (P : Pl D → Prop) (a : AE D) : a ∈ idOff D P ↔ ∀ w, P w → GlobalTheory.FinPl.compAt D w a = 0 := by
  simp only [idOff, Submodule.mem_iInf, RingHom.mem_ker, Subtype.forall]

theorem mem_GfC_iff_entries (V : HSp D) (g : GA D V) :
    g ∈ GfC V ↔ ∀ i j, infPart D ((Formalism.L2.Theta.mt V g - 1) i j) = 0 := by
  rw [GlobalTheory.UnitaryIdemCut.mem_GfC_iff, Units.ext_iff]
  change (Formalism.L2.Theta.mt V g).map (infPart D) = 1 ↔ _
  rw [← Matrix.ext_iff]
  refine forall_congr' fun i => forall_congr' fun j => ?_
  rw [Matrix.sub_apply, RingHom.map_sub, sub_eq_zero, Matrix.map_apply]
  by_cases hij : i = j
  · subst hij
    rw [Matrix.one_apply_eq, Matrix.one_apply_eq, RingHom.map_one]
  · rw [Matrix.one_apply_ne hij, Matrix.one_apply_ne hij, RingHom.map_zero]

theorem mem_grpAt_iff_parts (V : HSp D) (P : Pl D → Prop) (g : GA D V) :
    g ∈ grpAt V P ↔ ∀ i j, infPart D ((Formalism.L2.Theta.mt V g - 1) i j) = 0 ∧
      ∀ w, ¬ P w → GlobalTheory.FinPl.compAt D w ((Formalism.L2.Theta.mt V g - 1) i j) = 0 := by
  rw [grpAt, mem_congGrp_iff]
  exact forall_congr' fun i => forall_congr' fun j => mem_supportedOnPlacesIdeal_iff_components_zero_elsewhere D P _

theorem mem_grpOff_iff_parts (V : HSp D) (P : Pl D → Prop) (g : GA D V) :
    g ∈ grpOff V P ↔ ∀ i j w, P w → GlobalTheory.FinPl.compAt D w ((Formalism.L2.Theta.mt V g - 1) i j) = 0 := by
  rw [grpOff, mem_congGrp_iff]
  exact forall_congr' fun i => forall_congr' fun j => mem_idOff_iff P _

theorem grpAt_le_GfC (V : HSp D) (P : Pl D → Prop) : grpAt V P ≤ GfC V := fun g hg =>
  (mem_GfC_iff_entries V g).2 fun i j => ((mem_grpAt_iff_parts V P g).1 hg i j).1

theorem grpAt_le_grpOff (V : HSp D) (P P' : Pl D → Prop) (h : ∀ p, P p → ¬ P' p) : grpAt V P ≤ grpOff V P' := fun g hg =>
  (mem_grpOff_iff_parts V P' g).2 fun i j w hw => ((mem_grpAt_iff_parts V P g).1 hg i j).2 w fun h' => h w h' hw
















end GlobalTheory.FinPl.SetCut

end
