module

public import Mathlib
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaSourceAction
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HalfLinearCocycle
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ChosenSeries
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.RealPlaceAnalysis.Complexify
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Map
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum
open Formalism.IndefR.Mult (DSModel dualPar parA parB)
open Formalism.MainNotions.SchurIrreducible (AdmGK ARi ARiiiUp ARiiiDown ARiiiLine DiscreteSeriesBlattner admQ5)
open GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction hiding Mat
open GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix (SignCompat plainMat barMat)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (fockIp)
open GlobalTheory.Chain (signed)
open GlobalTheory.Chain.RealIt (LPol locS locT IsPolyIso)
open MeasureTheory Matrix
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ArchRec

abbrev Mn (n : ℕ) : Type := Matrix (Fin n) (Fin n) ℂ

section Cover

variable {p q r s : ℕ} {T₁ : GrpData p q} {T₂ : GrpData r s}

def IsGK {W : Type} [AddCommGroup W] [Module ℂ W] (a : Mat p q →ₗ[ℂ] Module.End ℂ W) : Prop :=
  IsLieAct a ∧ (∀ v, ∃ F : Submodule ℂ W, FiniteDimensional ℂ F ∧ v ∈ F ∧ KStable a F) ∧
    ∀ v, v ∈ ⨆ μ : Ix p q → ℚ, wtSub a μ


def ctr (R : DSRep T₁) (U : Type) [AddCommGroup U] [Module ℂ U] (v : R.HK.V) : R.HK.V ⊗[ℂ] U →ₗ[ℂ] U :=
  TensorProduct.lift (LinearMap.lsmul ℂ U ∘ₗ (innerₛₗ ℂ (R.ι v) ∘ₗ R.ι))



def TIntw {W : Type} [AddCommGroup W] [Module ℂ W] (a₁ : Mat p q →ₗ[ℂ] Module.End ℂ W)
    (a₂ : Mat r s →ₗ[ℂ] Module.End ℂ W) (M₁ : GKMod p q) (M₂ : GKMod r s) (f : W →ₗ[ℂ] M₁.V ⊗[ℂ] M₂.V) : Prop :=
  (∀ X, f ∘ₗ a₁ X = TensorProduct.map (M₁.act X) LinearMap.id ∘ₗ f) ∧
    ∀ Y, f ∘ₗ a₂ Y = TensorProduct.map LinearMap.id (M₂.act Y) ∘ₗ f

variable {σ : Type} (a₁ : Mat p q →ₗ[ℂ] Module.End ℂ (MvPolynomial σ ℂ))
  (a₂ : Mat r s →ₗ[ℂ] Module.End ℂ (MvPolynomial σ ℂ))

def CJoint (Λ₁ : Ix p q → ℚ) (Λ₂ : Ix r s → ℚ) (Φ : MvPolynomial σ ℂ) : Prop :=
  (∃ d, Φ.IsHomogeneous d ∧ (∀ Z ∈ pR p q, (a₁ Z Φ).IsHomogeneous (d + 2)) ∧
    ∀ Z ∈ pR r s, (a₂ Z Φ).IsHomogeneous (d + 2)) ∧ IsHW a₁ Λ₁ Φ ∧ IsHW a₂ Λ₂ Φ

variable (R₁ : DSRep T₁) (R₂ : DSRep T₂) (Λ₁ : Ix p q → ℚ) (Λ₂ : Ix r s → ℚ)




def TensNo : Prop :=
  ∀ (MM : GKMod r s) (f : MvPolynomial σ ℂ →ₗ[ℂ] R₁.HK.V ⊗[ℂ] MM.V), TIntw a₁ a₂ R₁.HK MM f → f = 0


end Cover

def phi {p q n : ℕ} (br : Bool) (e : Ix p q ≃ Fin n) (Z : Mat p q) : Mn n := if br then barMat e Z else plainMat e Z




def cjc (cj : Bool) (z : ℂ) : ℂ := if cj then conj z else z

section Comparison₂

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} {p q : ℕ} {T : GrpData p q}


structure Comparison₂ (R : DSRep T) (M : DSModel V S) (τ : D.what₂.Tau) (br cj : Bool) (e : Ix p q ≃ Fin V.rank) (m : ℤ)
    (U : M.H τ → R.U.H) : Prop where
  add : ∀ x y, U (x + y) = U x + U y
  smul : ∀ (z : ℂ) x, U (z • x) = cjc cj z • U x
  bij : Function.Bijective U
  norm : ∀ x, ‖U x‖ = ‖x‖
  grp : ∀ (g : T.G) (x : M.H τ), R.U.π g (U x) =
    ((T.sq g : ℂˣ) : ℂ) ^ (-m) • U (M.σ τ (phi br e ((T.cov g : GL (Ix p q) ℂ) : Mat p q)) x)
  kfin : ∀ x : M.H τ, IsKFin (M.ε τ) (M.σ τ) x ↔ U x ∈ Set.range R.ι


end Comparison₂


section Side

variable {ι σ Z : Type} {n p q : ℕ}

structure Side (A : Mn n → (Z → ℂ) → (Z → ℂ)) (pt : MvPolynomial ι ℂ → (Z → ℂ))
    (κ : MvPolynomial ι ℂ ≃ₗ[ℂ] MvPolynomial σ ℂ) (φ : Mat p q → Mn n) (c : ℚ)
    (a : Mat p q →ₗ[ℂ] Module.End ℂ (MvPolynomial σ ℂ)) : Prop where
  der : ∀ Y ∈ upq p q, ∀ P P', PolDer A pt (φ Y) P P' ↔ κ P' = a Y (κ P) + ((c : ℂ) * Y.trace) • κ P
  wt : ∀ (μ : Ix p q → ℚ) P, κ P ∈ wtSub a μ ↔ ∀ x : Ix p q → ℝ,
    A (φ (Matrix.diagonal fun j => Complex.exp ((x j : ℂ) * Complex.I))) (pt P) =
      Complex.exp (((∑ j, ((μ j + c : ℚ) : ℝ) * x j : ℝ) : ℂ) * Complex.I) • pt P





end Side

def IsFrameOf {n : ℕ} (G s : Mn n) (ε : Fin n → Bool) (fr : Mn n) : Prop :=
  IsUnit fr ∧ frᴴ * Formalism.REAL.Jm ε * fr = G ∧ s = fr⁻¹ * Formalism.REAL.Jm ε * fr


section Theta

variable {D : D7} (ψ : AddChar (AF D.host.F) ℂ) {S T : HSp D}




end Theta






end GlobalTheory.ArchRec

end
