module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.VacTheta
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinPt
public import Formalism.LocalToGlobal.ProjectiveLattices.CuspidalL2Subspace
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.OmAtSmulRight
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ClassFunctionSumIntegral
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.LocalToGlobal.HermitianColumns.InLocalDiscriminantKernel
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Fin.Basic
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Order.Kleene
public import Mathlib.Algebra.Order.ZeroLEOne
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Equiv
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.UnitBall
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

noncomputable section

open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area)
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG)
open GlobalTheory.NormDict

namespace GlobalTheory.NormExact

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def IsScale (D : D7) (cc : Ideal (𝓞 D.host.K)) (r : D.host.E) : Prop :=
  r * D.host.conj r * ((Ideal.absNorm D.host.ccK : ℕ) : D.host.E) = ((Ideal.absNorm cc : ℕ) : D.host.E)

def coordY (θ : InfFam D) {S T : HSp D} {a d : ℕ} (hS : S.rank = a) (hT : T.rank = d) (δ : ℂ) (r : D.host.E) (w : WO S T) :
    VC D a d :=
  fun τ i j => δ * embT D τ r * compAt θ τ w (Fin.cast hT.symm i) (Fin.cast hS.symm j)

def Reads (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) {S T : HSp D} {a d : ℕ} (hS : S.rank = a) (hT : T.rank = d)
    (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (r : D.host.E) (G : VC D a d → ℂ) (f : WO S T → ℂ) : Prop :=
  IsThetaFunO ψ S T f ∧ ∀ w : WO S T, w.map (finPart D) = 0 →
    f w = Complex.exp (-((Real.pi : ℂ) / 2) * Hf D (tor0 D cc δ) (coordY θ hS hT δ r w) (coordY θ hS hT δ r w)) *
      G (coordY θ hS hT δ r w)

structure Setup (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (r : D.host.E) :
    Prop where
  std : IsStdChar D ψ (-1)
  inf : IsInfFam θ
  gS : S.gram = 1
  gT : T.gram = 1
  crv : Formalism.MainNotions.StandardLatticesGL3.Crv D cc δ
  scale : IsScale D cc r

def finPt {S T : HSp D} {a d : ℕ} (hS : S.rank = a) (hT : T.rank = d) (r : D.host.E) (z : Matrix (Fin d) (Fin a) D.host.E) :
    WO S T :=
  GlobalTheory.VacUnique.finRat S T (Matrix.of fun i j => -(r⁻¹ * z (Fin.cast hT i) (Fin.cast hS j)))

def IsFinIdl (x : (AE D)ˣ) (y : (Formalism.MainNotions.StandardLatticesGL3.AE D)ˣ) : Prop :=
  infPart D (x : AE D) = 1 ∧
    GlobalTheory.LFun.finAdEquiv D.host.F D.host.E (finPart D (x : AE D)) = GlobalTheory.BotFormula.toFinE D (y : Formalism.MainNotions.StandardLatticesGL3.AE D)

def HasFinPart (χ : (AE D)ˣ →* Circle) {N : ℕ} (c : Formalism.MainNotions.StandardLatticesGL3.HeckeU D N) (e : ℤ) : Prop :=
  ∀ x y, IsFinIdl x y → ((χ x : Circle) : ℂ) = ((c.f y ^ e : ℂˣ) : ℂ)

def IsCongLevel {N : ℕ} (J : Subgroup (Formalism.MainNotions.StandardLatticesGL3.GA D N)) : Prop :=
  ∃ m : ℕ, 0 < m ∧ ∀ k ∈ intG D N, (∀ i j, ∃ s ∈ Formalism.MainNotions.StandardLatticesGL3.OhE D,
    (((k : GL (Fin N) (Formalism.MainNotions.StandardLatticesGL3.AE D)) : Matrix (Fin N) (Fin N) (Formalism.MainNotions.StandardLatticesGL3.AE D)) - 1) i j =
      (m : Formalism.MainNotions.StandardLatticesGL3.AE D) * s) → k ∈ J

def period (D : D7) (δ : ℂ) (r : D.host.E) (τ : D.what₂.Tau) : ℂ :=
  δ * embT D τ r / (Real.sqrt (2 * Real.pi * Formalism.L2.Pj.xiR D) : ℂ)

def normConst (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (a : ℕ) (n : D.what₂.Tau → ℕ) : ℝ :=
  ∏ τ, (Real.pi / area (lamOf D cc δ)) ^ (a * n τ)

variable {cc : Ideal (𝓞 D.host.K)} {δ t0 : ℂ} {Q : ℕ}

structure IsStdFrame (P : Pair D cc δ t0 Q) (Y : Frame P) : Prop where
  frame : IsFrame P Y
  ptA : ∀ x, GlobalTheory.BotFormula.IsFinPt Y.A (Y.ιA x) x
  ptB : ∀ h, GlobalTheory.BotFormula.IsFinPt Y.B (Y.ιB h) h

structure IsMaxLevel {P : Pair D cc δ t0 Q} (Y : Frame P) (K₀ : Subgroup (GL (Fin Y.B.rank) (Lev.EAf D)))
    (μ₀ : Measure (GA D Y.B)) : Prop where
  lev : GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral.IsOpenCompactLevel Y.B K₀
  mem_iff : ∀ h, Lev.finE Y.B (Y.ιB h) ∈ K₀ ↔ h ∈ intG D P.d
  meas : ∃ 𝓕, Links.IsMeasDef Y.B K₀ μ₀ 𝓕

structure IsExact (P : Pair D cc δ t0 Q) (X : Data P) (r : D.host.E) : Prop where
  std : IsStdFrame P X.toFrame
  inf : IsInfFam X.θ
  weil : IsWeilDatumO X.ψ X.A X.B X.χA X.χB X.om
  chA : HasFinPart X.χA P.W.chV P.W.ep
  chB : HasFinPart X.χB P.W.chV' (-P.W.ep')
  scale : IsScale D cc r
  read : Reads X.ψ X.θ X.rkA X.rkB cc δ r P.F X.vac
  const : X.c₁ = ∏ τ, period D δ r τ ^ (P.a * P.n τ)

theorem IsExact.setup {P : Pair D cc δ t0 Q} {X : Data P} {r : D.host.E} (h : IsExact P X r) :
    Setup X.ψ X.θ X.A X.B cc δ r :=
  ⟨h.weil.std, h.inf, h.std.frame.gramA, h.std.frame.gramB, P.crv, h.scale⟩

theorem isCongLevel_intG (N : ℕ) : IsCongLevel (intG D N) := ⟨1, one_pos, fun _ hk _ => hk⟩

theorem isScale_one (D : D7) : IsScale D D.host.ccK 1 := by simp [IsScale]

end GlobalTheory.NormExact
