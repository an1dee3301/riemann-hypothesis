module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAllTiedPerTied
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsAutFunOfMemCusp
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOrthogonalSumLatticeSameLatticedSpace
public import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
public import Development.AbelianVarietyTheory.Definitions.Divisors.BplusOfEquivariant
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HermitianOrthogonalExtensionData
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.NodeYPredEqChainVertexAtRowZeroLast
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ReLatSelf
public import Formalism.HermitianLattices.StatementLat
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.Divisibility.LiftLat
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Lattice.Basic
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim MeasureTheory
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RowLift

open GlobalTheory.GridJoin

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

structure RowMatchS (ch : Choice R) (G' : GlobalTheory.Grid.GridPre R) : Prop where

  V : ∀ i, i ≤ D.R.m → SameSp (ch.G.V (.grid i 0)) (G'.V i 0).V

  ν : ∀ i, i ≤ D.R.m → HEq (G'.measCol i).ν (ch.M.ν (.grid i 0))

  fd : ∀ i, i ≤ D.R.m → HEq (G'.measCol i).fd (ch.M.fd (.grid i 0))

  ker : ∀ (ρ : ch.G.RealVec) (Φ : ch.G.Datum) (i : Fin D.R.m), ∃ f,
    GlobalTheory.Grid.IsFinVec R.ψ R.θ true (G'.V ((i : ℕ) + 1) 0) (G'.V i 0) f ∧ ∃ p,
      HEq (fun h g => thetaKO (G'.X i 0).ω h g (GlobalTheory.Grid.fock R.ψ R.θ true (G'.V ((i : ℕ) + 1) 0) (G'.V i 0) f p))
        (fun h g => ch.W.kerA (.right (i : ℕ) 0) (ch.W.datum ρ Φ i) g h)

theorem transport_stepS {A A' B B' : HSp D} (eA : SameSp A' A) (eB : SameSp B' B)
    {ν : Measure (GA D A)} {fd : Set (GA D A)} {ν' : Measure (GA D A')} {fd' : Set (GA D A')}
    (hν : HEq ν ν') (hfd : HEq fd fd') {K : GA D B → GA D A → ℂ} {K' : GA D A' → GA D B' → ℂ}
    (hK : HEq K (fun h g => K' g h)) {φ : GA D A → ℂ} {φ' : GA D A' → ℂ} (hφ : HEq φ φ') {ψ : GA D B → ℂ}
    (hI : ∀ h, IntegrableOn (fun g => K h g * φ g) fd ν) (hE : ∀ h, ∫ g in fd, K h g * φ g ∂ν = ψ h) :
    (∀ h, IntegrableOn (fun g => K' g h * φ' g) fd' ν') ∧ HEq ψ (fun h => ∫ g in fd', K' g h * φ' g ∂ν') := by
  obtain ⟨L, h1, h2, rfl⟩ := eA
  obtain ⟨L', h1', h2', rfl⟩ := eB
  obtain rfl := eq_of_heq hν
  obtain rfl := eq_of_heq hfd
  obtain rfl := eq_of_heq hφ
  obtain rfl := eq_of_heq hK
  exact ⟨hI, heq_of_eq (funext hE).symm⟩

theorem isAutFun_transportS {V V' : HSp D} (e : SameSp V' V) {φ : GA D V → ℂ} {φ' : GA D V' → ℂ} (h : HEq φ φ')
    (hφ : IsAutFun V φ) : IsAutFun V' φ' := by
  obtain ⟨L, h1, h2, rfl⟩ := e
  obtain rfl := eq_of_heq h
  exact ⟨hφ.left, hφ.level, hφ.cont⟩

end GlobalTheory.RowLift

end
