module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.NodeYPredEqChainVertexAtRowZeroLast
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HermitianOrthogonalExtensionData
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Classical
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Localization.FractionRing

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid
open scoped Pointwise TensorProduct InnerProductSpace

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IndefiniteRowSideFullHecke.IwahoriMembership

variable {D : D7}

section Local


variable (D) in
abbrev Oh : Subring (Datum.EAf D) := Formalism.L2.Herm.intAf D.host.F D.host.E

def InI (I : Ideal (𝓞 D.host.E)) (z : Datum.EAf D) : Prop := ∃ h : z ∈ Oh D, (⟨z, h⟩ : Oh D) ∈ idS D.host.F I

variable (e : AE D) (I : Ideal (𝓞 D.host.E)) (ν : (AE D)ˣ →* Circle)

variable {a a' d₁ d₂ : ℕ}

variable (hd : a + a' = d₁ + d₂) (h : GL (Fin (d₁ + d₂)) (AE D))

end Local

section Models

variable (ψ : AddChar (AF D.host.F) ℂ)


open Classical in
def IsDatOwn (ε : Bool) (S T : Node D) (e : AE D) (f₀ : WO S.V T.V → ℂ)
    (φ : Matrix (Fin T.V.rank) (Fin S.V.rank) (Datum.EAf D) → ℂ) (f : WO S.V T.V → ℂ) : Prop :=
  IsSBHalf e (latO (sgn ε S.V) T.V S.Λ T.Λ fun _ => True)
      (fun x : WO S.V T.V => if IsHalf e x then φ (frMapO S.V T.V S.β T.β x) else 0) ∧
    IsThetaAt ψ (symplO (sgn ε S.V) T.V) (heisO ψ (sgn ε S.V) T.V) e (latO (sgn ε S.V) T.V S.Λ T.Λ fun _ => True) 1 f₀
      (fun x : WO S.V T.V => if IsHalf e x then φ (frMapO S.V T.V S.β T.β x) else 0) f


end Models

section Grid

variable {G₀ : Type} [Group G₀] [Fintype G₀] {Pl0 T : Type} {A : FamIn D.what₂.LL G₀ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (G : GridDat R)





end Grid

section Basic₂

variable {G₀ : Type} [Group G₀] [Fintype G₀] {Pl0 T : Type} {A : FamIn D.what₂.LL G₀ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {G : GridDat R}

end Basic₂

end GlobalTheory.IndefiniteRowSideFullHecke.IwahoriMembership

end
