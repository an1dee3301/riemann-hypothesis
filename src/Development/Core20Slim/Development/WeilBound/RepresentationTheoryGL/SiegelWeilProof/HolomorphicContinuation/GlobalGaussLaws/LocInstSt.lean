module

public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.FourierZeroN
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ModerateGrowthSchwartz
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobData
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.IsSingTest
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.NullSec
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Block
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

variable {D : D7} {n : ℕ}

def sLd {m : ℕ} (L : GR n → ((Fin m → Fin n → ℂ) → ℂ) → ((Fin m → Fin n → ℂ) → ℂ)) (c : ℝ) (P : PX m n) (y : GR n) : ℂ :=
  L y (fP c P) 0

def pqOf {m : ℕ} (ε : Fin m → Bool) (l : D.what₂.Tau → ℝ) (τ : D.what₂.Tau) : ℕ × ℕ :=
  if 0 < l τ then (cnt ε true, cnt ε false) else (cnt ε false, cnt ε true)

def LIl : Prop :=
  ∀ D n V ψ χ θ μ ω H l s ν τ ε fr ι, Cx D n V ψ χ θ μ ω H l s ν τ ε fr ι → l τ ≠ 0

def LIlin : Prop :=
  ∀ D n V ψ χ θ μ ω H l s ν τ ε fr ι, Cx D n V ψ χ θ μ ω H l s ν τ ε fr ι → TensMem → ∀ L, IsLocOp ω l s τ fr ι L →
    (∀ (y : GR n) (a : ℂ) (P Q : PX V.rank n), L y (fP (cLoc l τ) (a • P + Q)) = a • L y (fP (cLoc l τ) P) + L y (fP (cLoc l τ) Q)) ∧
    ∀ P : PX V.rank n, L 1 (fP (cLoc l τ) P) = fP (cLoc l τ) P

def LIlaw : Prop :=
  ∀ D n V ψ χ θ μ ω H l s ν τ ε fr ι, Cx D n V ψ χ θ μ ω H l s ν τ ε fr ι → TensMem → ∀ L, IsLocOp ω l s τ fr ι L →
    ∃ e : ℤ, ∀ (P : PX V.rank n) (y g : GR n), (mR y).toBlocks₂₁ = 0 →
      sLd L (cLoc l τ) P (y * g) = F0 (pqOf ε l τ).1 (pqOf ε l τ).2 e y * sLd L (cLoc l τ) P g

def LIcell : Prop :=
  ∀ D n V ψ χ θ μ ω H l s ν τ ε fr ι, Cx D n V ψ χ θ μ ω H l s ν τ ε fr ι → TensMem → ∀ L, IsLocOp ω l s τ fr ι L →
    ∃ C : ℂ, C ≠ 0 ∧ ∀ (P : PX V.rank n) (g : GR n) (b : Matrix (Fin n) (Fin n) ℂ), b.IsHermitian → mR g = JJ n * nU b →
      sLd L (cLoc l τ) P g = C * secN ε (cLoc l τ) (tLoc l τ) P b

def LIcont : Prop :=
  ∀ D n V ψ χ θ μ ω H l s ν τ ε fr ι, Cx D n V ψ χ θ μ ω H l s ν τ ε fr ι → TensMem → ∀ L, IsLocOp ω l s τ fr ι L →
    ∀ P : PX V.rank n, Continuous (sLd L (cLoc l τ) P)

def LIrho : Prop :=
  ∀ D n V ψ χ θ μ ω H l s ν τ ε fr ι, Cx D n V ψ χ θ μ ω H l s ν τ ε fr ι → TensMem → ∀ L, IsLocOp ω l s τ fr ι L →
    ∃ ρ : GR n → PX V.rank n →ₗ[ℂ] PX V.rank n, (∀ (k : GR n) P, InK (mR k) → L k (fP (cLoc l τ) P) = fP (cLoc l τ) (ρ k P)) ∧
      ∀ P, ∃ W : Submodule ℂ (PX V.rank n), FiniteDimensional ℂ W ∧ P ∈ W ∧ (∀ k : GR n, InK (mR k) → ∀ Q ∈ W, ρ k Q ∈ W) ∧
        ∀ Q ∈ W, ∀ l' : PX V.rank n →ₗ[ℂ] ℂ, ContinuousOn (fun k : GR n => l' (ρ k Q)) {k | InK (mR k)}

def LIkact : Prop :=
  ∀ D n V ψ χ θ μ ω H l s ν τ ε fr ι, Cx D n V ψ χ θ μ ω H l s ν τ ε fr ι → TensMem → ∀ L, IsLocOp ω l s τ fr ι L →
    ∀ ρ : GR n → PX V.rank n →ₗ[ℂ] PX V.rank n, (∀ (k : GR n) P, InK (mR k) → L k (fP (cLoc l τ) P) = fP (cLoc l τ) (ρ k P)) →
      ∀ P (g k : GR n), InK (mR k) → sLd L (cLoc l τ) P (g * k) = sLd L (cLoc l τ) (ρ k P) g

def LIvac : Prop :=
  ∀ (m n : ℕ) (ε : Fin m → Bool) (c t : ℝ) (p q : ℕ) (e : ℤ), 0 < c →
    ((t = c ∧ p = cnt ε true ∧ q = cnt ε false) ∨ (t = -c ∧ p = cnt ε false ∧ q = cnt ε true)) →
    ∀ (S : GR n → ℂ) (C : ℂ), Continuous S → S 1 = 1 →
      (∀ (y g : GR n), (mR y).toBlocks₂₁ = 0 → S (y * g) = F0 p q e y * S g) →
      (∀ (g : GR n) (b : Matrix (Fin n) (Fin n) ℂ), b.IsHermitian → mR g = JJ n * nU b → S g = C * secN ε c t (1 : PX m n) b) →
      ∀ g, S g = F0 p q e g

def LIkvac : Prop :=
  ∀ D n V ψ χ θ μ ω H l s ν τ ε fr ι, Cx D n V ψ χ θ μ ω H l s ν τ ε fr ι → TensMem → ∀ L, IsLocOp ω l s τ fr ι L →
    ∀ e : ℤ, (∀ g : GR n, sLd L (cLoc l τ) 1 g = F0 (pqOf ε l τ).1 (pqOf ε l τ).2 e g) →
    ∀ k : GR n, InK (mR k) → L k (fP (cLoc l τ) 1) = F0 (pqOf ε l τ).1 (pqOf ε l τ).2 e k • fP (cLoc l τ) 1

end PositivityTheory.Rg.Sw.Glob
