module

public import Development.Core20Slim.Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.ThetaOrbits
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ModerateGrowthSchwartz
public import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
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
public import Init.Core
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.ExistsUnique
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Set.Operations
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.SummationFilter
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.GramSchwartzFunctions.EC

open GlobalTheory.StdUnn

section Field

variable {K : Type} [Field K]

def cT (σ : K →+* K) {a b : ℕ} (x : Matrix (Fin a) (Fin b) K) : Matrix (Fin b) (Fin a) K := (x.map σ).transpose

def Jm (K : Type) [Field K] (n : ℕ) : Matrix (Fin (n + n)) (Fin (n + n)) K := blk4 0 1 (-1) 0

def IsUnitary (σ : K →+* K) {N : ℕ} (J g : Matrix (Fin N) (Fin N) K) : Prop := cT σ g * J * g = J

def IsSiegelP {n : ℕ} (g : Matrix (Fin (n + n)) (Fin (n + n)) K) : Prop :=
  ∀ i j : Fin n, g (finSumFinEquiv (Sum.inr i)) (finSumFinEquiv (Sum.inl j)) = 0

def eId (K : Type) [Field K] (n r : ℕ) : Matrix (Fin n) (Fin n) K := Matrix.diagonal fun i => if (i : ℕ) < r then 1 else 0

def wr (K : Type) [Field K] (n r : ℕ) : Matrix (Fin (n + n)) (Fin (n + n)) K :=
  blk4 (1 - eId K n r) (eId K n r) (-eId K n r) (1 - eId K n r)

def nB {n : ℕ} (b : Matrix (Fin n) (Fin n) K) : Matrix (Fin (n + n)) (Fin (n + n)) K := blk4 1 b 0 1

def mA (σ : K →+* K) {n : ℕ} (a : Matrix (Fin n) (Fin n) K) : Matrix (Fin (n + n)) (Fin (n + n)) K :=
  blk4 a 0 0 (cT σ a)⁻¹

def extB {n r : ℕ} (b : Matrix (Fin r) (Fin r) K) : Matrix (Fin n) (Fin n) K :=
  fun i j => if h : (i : ℕ) < r ∧ (j : ℕ) < r then b ⟨i, h.1⟩ ⟨j, h.2⟩ else 0

def IsCompl {n r : ℕ} (c : Matrix (Fin r) (Fin n) K) (a : Matrix (Fin n) (Fin n) K) : Prop :=
  IsUnit a.det ∧ ∀ (i : Fin n) (hi : (i : ℕ) < r), a i = c ⟨i, hi⟩

def repMat (σ : K →+* K) {n r : ℕ} (b : Matrix (Fin r) (Fin r) K) (a : Matrix (Fin n) (Fin n) K) :
    Matrix (Fin (n + n)) (Fin (n + n)) K :=
  wr K n r * nB (extB b) * mA σ a

end Field

def Bruhat : Prop :=
  ∀ (K : Type) [Field K] (σ : K →+* K), (∀ x, σ (σ x) = x) → (2 : K) ≠ 0 → ∀ n : ℕ,
  ∀ c : ∀ U : Submodule K (Fin n → K), Matrix (Fin (Module.finrank K U)) (Fin n) K,
    (∀ U, LinearIndependent K (c U) ∧ Submodule.span K (Set.range (c U)) = U) →
  ∀ a : ∀ U : Submodule K (Fin n → K), Matrix (Fin n) (Fin n) K, (∀ U, IsCompl (c U) (a U)) →
    (∀ (U : Submodule K (Fin n → K)) (b : Matrix (Fin (Module.finrank K U)) (Fin (Module.finrank K U)) K), cT σ b = b →
      IsUnit (repMat σ b (a U)).det ∧ IsUnitary σ (Jm K n) (repMat σ b (a U))) ∧
    ∀ g : Matrix (Fin (n + n)) (Fin (n + n)) K, IsUnit g.det → IsUnitary σ (Jm K n) g →
      ∃! q : (Σ U : Submodule K (Fin n → K), {b : Matrix (Fin (Module.finrank K U)) (Fin (Module.finrank K U)) K // cT σ b = b}),
        IsSiegelP (g * (repMat σ q.2.1 (a q.1))⁻¹)

def RatPts : Prop :=
  ∀ (D : D7) (n : ℕ),
    (∀ γ ∈ GF D n, ∃ g : Matrix (Fin (n + n)) (Fin (n + n)) D.host.E, IsUnit g.det ∧
      IsUnitary (D.sp.cm.sig : D.host.E →+* D.host.E) (Jst D n) g ∧ mat γ = g.map (incA D)) ∧
    (∀ g : Matrix (Fin (n + n)) (Fin (n + n)) D.host.E, IsUnit g.det →
      IsUnitary (D.sp.cm.sig : D.host.E →+* D.host.E) (Jst D n) g → ∃ γ ∈ GF D n, mat γ = g.map (incA D)) ∧
    (∀ γ ∈ GF D n, ∀ g : Matrix (Fin (n + n)) (Fin (n + n)) D.host.E, mat γ = g.map (incA D) →
      (γ ∈ P D n ↔ IsSiegelP g))

def PInv : Prop :=
  ∀ (D : D7) (n : ℕ) (V : HSp D) ψ χ θ μ ω, HidaSetting D n V ψ χ θ μ ω →
  ∀ Φ : schwartzA θ V.rank n, LeftInv (P D n ⊓ GF D n) (fun γ => (ω γ Φ).1 0)

def ThetaInv : Prop :=
  ∀ (D : D7) (n : ℕ) (V : HSp D) ψ χ θ μ ω, HidaSetting D n V ψ χ θ μ ω →
  ∀ Φ : schwartzA θ V.rank n, ∀ γ ∈ GF D n,
    ∑' ξ : Matrix (Fin V.rank) (Fin n) D.host.E, (ω γ Φ).1 (ξ.map (incA D)) =
      ∑' ξ : Matrix (Fin V.rank) (Fin n) D.host.E, Φ.1 (ξ.map (incA D))

end PositivityTheory.GramSchwartzFunctions.EC
