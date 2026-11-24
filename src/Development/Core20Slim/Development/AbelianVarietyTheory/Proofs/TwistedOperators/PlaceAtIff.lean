module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ChainMatrices
public import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
public import Development.AbelianVarietyTheory.Definitions.Divisors.BplusOfEquivariant
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsNotRelZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum
public import Development.AbelianVarietyTheory.Definitions.Divisors.InvVolConjLevelOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatSelfDualOfUnimod
public import Development.Core20Slim.Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.StepUnfold
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Formalism.LocalToGlobal.Divisibility.LiftLat
public import Formalism.LocalToGlobal.HermitianColumns.InLocalDiscriminantKernel
public import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemSum
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Classical
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.List.Basic
public import Init.Data.Nat.Package
public import Init.Data.Order.Lemmas
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Insert
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.GroupTheory.DoubleCoset
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal

namespace GlobalTheory.LocAsm

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R)


open Classical in
def PlaceCl (s : ℤˣ) (t : T) (w : Pl D.host.E)
    (β : Cosets (G := locGrid ch.G t w) one_le_sLen (givenLevel ch.G t w)) (ζ : ℂ) : Prop :=
  ∀ e, IsIdemSum e {w} → ∀ (M : Vol ch.G) (hM : M.Is t) (r r₀ h : Pts ch.G),
    OneLoc t w e r (fun j => if j ∈ idx D then sgnAt ch.G t s w j * (repsAt ch.G t w).elt β (D.R.m, j) else 1) →
    OneLoc t w e r₀ (fun j => if j = 0 then (stair (locGrid ch.G t w) (unifAt w) (cosExp ch.G w) j)⁻¹ else 1) →
    (∀ j, j ≤ D.R.m → ∃ δ, IsTilt ch.G j δ ∧ δ⁻¹ * h j ∈ GlobalTheory.FinPl.grpOff _ (· = w.under (𝓞 D.host.F))) →
    ∀ (φ : ∀ b : GlobalTheory.SplitFlip.Edge, Matrix (Fin ((locGrid ch.G t w).rank b.tgt)) (Fin ((locGrid ch.G t w).rank b.src)) (Kw w) → ℂ),
      (∀ i j x, φ (.ex i j) x = 1) → ∀ v f : SchDown ch.G t, (∀ j, IsThetaFunO ch.W.ψ _ _ (v j)) →
      (∀ j : Fin D.R.m, IsLocVec ch.W (.mu t D.R.m j) e (v j) (fun y => if IsHalf e y then φ (.theta D.R.m j)
        (ch.S.B.coord t w (X := (D.R.m, j + 1)) (Y := (D.R.m, j)) ⟨le_rfl, j.2⟩ ⟨le_rfl, j.2.le⟩
          (y.map fun a => cpt w (toEAf D a))) else 0) (f j)) →
      ∀ (I : Type) (S : Finset I) (x : I → ℂ) (d : I → ∀ j : Fin D.R.m, FinDatum ch.G t (.top t j)) (c : I → Combs ch.G),
        (∀ i ∈ S, ∀ j : Fin D.R.m, (d i j).e = e ∧ IsCombOf ch.W (d i j) ((c i).1 j)) →
        (∀ y : ∀ j : Fin D.R.m, WO (ch.G.V (.top j)) (ch.G.V (.top (j + 1))), (∀ j, IsHalf e (y j)) →
          ∑ i ∈ S, x i * ∏ j, (d i j).fn (y j) = flatTensor one_le_sLen (psiAt ch.W w) (unitVol w)
            (moved (locGrid ch.G t w) (keepAt ch.G w) ((repsAt ch.G t w).elt β)
              ((locGrid ch.G t w).lines₂ (GlobalTheory.SplitFlip.oppositePath D.R.m) φ)) (ch.S.toGridChoice.colAt t w y) 0) →
        ∀ u, evT (conAt ch.W hM f (h * r)) 1 u 0 = ζ * ∑ i ∈ S, x i * evT (combC ch.W (c i) (conAt ch.W hM v (h * r₀))) 1 u 0

theorem placeAt_iff (s : ℤˣ) : PlaceAt ch s ↔ ∃ (κ : Pl D.host.E → ℂ) (z : T → Pl D.host.E → ℂˣ),
    (∀ t w, z t w ∈ xiVals R.toLevCh t) ∧ (∀ w, w ∉ ch.G.pl.W0 → κ w = 1) ∧
    ∀ t, ∀ w ∈ locPl ch.G t, ∀ β : Cosets (G := locGrid ch.G t w) one_le_sLen (givenLevel ch.G t w), ∃ ζ : ℂ,
      ((w ∈ ch.G.pl.W0 → ∀ i, β i = DoubleCoset.mk _ _ (stair (locGrid ch.G t w) (unifAt w) (cosExp ch.G w) (i + 1))) →
        ζ = κ w * (z t w : ℂ)⁻¹) ∧ PlaceCl ch s t w β ζ := Iff.rfl

end GlobalTheory.LocAsm

end
