module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.Foundations.MemL2OfBoundedContinuousInvariant
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Data.Cast
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
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
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Instances.Matrix

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open Formalism.IndefR.Lift (liftInt)
open GlobalTheory.Cusp (constTerm frameFlag)
open scoped TensorProduct

namespace GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def adel {m n : ℕ} (x : Matrix (Fin m) (Fin n) D.host.E) : Matrix (Fin m) (Fin n) (AE D) := x.map (incA D)

abbrev ct {m n : ℕ} (x : Matrix (Fin m) (Fin n) D.host.E) : Matrix (Fin n) (Fin m) D.host.E :=
  Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) x





def IsAutCharGL (t : ℕ) (μ : GL (Fin t) (AE D) →* Circle) : Prop :=
  Continuous μ ∧ ∀ a : GL (Fin t) D.host.E, μ (Matrix.GeneralLinearGroup.map (incA D) a) = 1

def IsAutCharU (V : HSp D) (ξ : GA D V →* Circle) : Prop := Continuous ξ ∧ ∀ γ ∈ GQ V, ξ γ = 1

def detPow {t : ℕ} (a : GL (Fin t) (AE D)) (n : ℕ) : ℝ :=
  (GlobalTheory.Doubling.absE D.host.F D.host.E (Matrix.GeneralLinearGroup.det a) : ℝ) ^ ((n : ℝ) / 2)

def ratMx (D : D7) (m n : ℕ) : AddSubgroup (Mx D m n) :=
  ((incA D).toAddMonoidHom.mapMatrix (m := Fin m) (n := Fin n)).range

section Target

variable (ψ : AddChar (AF D.host.F) ℂ) (S T T' : HSp D) {t : ℕ} (ι : T'.V →ₗ[D.host.E] T.V)
  (C : Matrix (Fin T.rank) (Fin t) D.host.E)


end Target

section Source

variable (ψ : AddChar (AF D.host.F) ℂ) (S S' T : HSp D) {t : ℕ} (ι : S'.V →ₗ[D.host.E] S.V)
  (C : Matrix (Fin S.rank) (Fin t) D.host.E)


end Source

end GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions

end
