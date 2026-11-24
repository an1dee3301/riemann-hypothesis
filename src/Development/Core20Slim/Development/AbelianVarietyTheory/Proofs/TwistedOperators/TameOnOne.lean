module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnitaryOnTheta
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Formalism.LocalToGlobal.HermitianColumns.InLocalDiscriminantKernel
public import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Classical
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Basic
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.UnitBall
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StepLaw

variable {D : D7}

def TameOn (χ : (AE D)ˣ →* Circle) (e : AE D) (P : Finset (Pl D.host.E))
    (c : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) : Prop :=
  ∀ x : (AE D)ˣ, infPart D (x : AE D) = 1 → ∀ hx : toEAf D (x : AE D) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E,
    toEAf D ((x⁻¹ : (AE D)ˣ) : AE D) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E → cA D e * (x : AE D) = cA D e →
    ∀ u : ∀ PP : Pl D.host.E, (kP PP)ˣ, (∀ PP ∈ P, (u PP : kP PP) = resS D.host.F PP ⟨toEAf D (x : AE D), hx⟩) →
      ((χ x : Circle) : ℂ) = ∏ PP ∈ P, ((c PP (u PP) : ℂˣ) : ℂ)

def vacScal {S T : HSp D} (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)) (P : Finset (Pl D.host.E))
    (cS cT : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (g : GA D S) (h : GA D T) : ℂ :=
  ∏ PP ∈ P, (((cT PP (Matrix.GeneralLinearGroup.det (redFn βS PP (finE S g))) : ℂˣ) : ℂ)⁻¹ *
    ((cS PP (Matrix.GeneralLinearGroup.det (redFn βT PP (finE T h))) : ℂˣ) : ℂ))


open Classical in
def resChr {T0 : Type} (L : LevCh D T0) (t : T0) (n : ℕ) (PP : Pl D.host.E) : (kP PP)ˣ →* ℂˣ :=
  if PP ∈ L.Pg then (L.chi n PP)⁻¹ else L.xiR t PP

end GlobalTheory.StepLaw

end
