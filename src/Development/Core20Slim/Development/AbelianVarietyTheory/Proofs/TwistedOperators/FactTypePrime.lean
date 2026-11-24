module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ColLieApply
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteDimensionalModel
public import Development.AbelianVarietyTheory.Definitions.Foundations.StandardFiveNontrivial
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Formalism.LocalToGlobal.HermitianColumns.InLocalDiscriminantKernel
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.InclusionInjective
public import Formalism.SatakeDualWeyl.Statement
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Submonoid.Operations
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Quot
public import Mathlib.GroupTheory.DoubleCoset
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Maps

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Datum (InfFam)

namespace GlobalTheory.DefFree

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

instance factTypePrime (D : D7) (k : Fin 2) : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩

theorem finE_mem (V : HSp D) (h : GA D V) : finE V h ∈ UA D.sp.cm V.gram := by
  have h0 : matHom V h ∈ HR (AF D.host.F) D.sp.cm.sig V.gram := by
    let h' : HR (AF D.host.F) D.sp.cm.sig V.gram := h
    exact h'.2
  have h1 := Formalism.UG.P.bc_mem _ (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig)
    (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom ?c1 _ _ h0
  have h2 := Formalism.UG.P.bc_mem _ (Formalism.UG.sigR D.sp.cm.sig (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F)) (swapAE D) ?c2 _ _ h1
  convert h2 using 1
  case e'_5 => rfl
  case e'_4 =>
    unfold UA Formalism.UG.UPts
    congr 1
  case c2 =>
    apply RingHom.ext
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a e => simp [swapAE, sigR, Formalism.UG.sigR]
    | add x y hx hy => simp only [RingHom.comp_apply, map_add (f := _)] at hx hy ⊢; rw [hx, hy]
  case c1 =>
    apply RingHom.ext
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a e => simp [sigR]
    | add x y hx hy => simp only [RingHom.comp_apply, map_add (f := _)] at hx hy ⊢; rw [hx, hy]

def finU (V : HSp D) : GA D V →* UA D.sp.cm V.gram := (finE V).codRestrict _ (finE_mem V)

theorem coe_finU (V : HSp D) (h : GA D V) : (finU V h : GL (Fin V.rank) (EAf D)) = finE V h := rfl

def clsA (V : HSp D) (K : Subgroup (GL (Fin V.rank) (EAf D))) (h : GA D V) : Cl D.sp.cm V.gram K :=
  Quotient.mk'' (finU V h)






end GlobalTheory.DefFree

end
