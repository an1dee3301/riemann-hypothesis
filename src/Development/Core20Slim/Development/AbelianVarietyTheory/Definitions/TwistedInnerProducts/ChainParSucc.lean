module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.CartFrSgn

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.Chain (IsVacVec ptOf signed)
open GlobalTheory.ChainOnto (stepPar)

namespace GlobalTheory.EvenOnto

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def UpPair (t : ℕ) (S S' : SPar) (aS aT : ℚ) : Prop :=
  ∃ al be ga de : List ℚ, Formalism.MainNotions.SchurIrreducible.DataAR t al be ga de ∧ (∀ e ∈ al ++ be ++ ga ++ de, ((t : ℚ) + 3) / 2 ≤ |e|) ∧
    S = dualPar (signed (al ++ be) (ga ++ de) aT) ∧ S' = dualPar (signed (al ++ block t ++ de) (ga ++ be) aS)

structure Com (D : D7) where
  θ : InfFam D
  ψ : AddChar (AF D.host.F) ℂ
  S : Finset (HeightOneSpectrum (𝓞 D.host.F))
  n : ℕ
  t : ℕ
  m : ℕ
  χ : ℕ → ((AE D)ˣ →* Circle)
  a : ℕ → D.what₂.Tau → ℚ

structure Com.Is (c : Com D) : Prop where
  inf : IsInfFam c.θ
  std : IsStdChar D c.ψ (-1)
  hecke : ∀ k < c.m, IsHeckeChar D (c.χ k) ∧ Formalism.L2.Theta.ResEta D (c.χ k) 0
  exp : ∀ k < c.m, ∀ τ, HasInfExp D (c.χ k) τ (c.a k τ)
  unr : ∀ k < c.m, GlobalTheory.LFun.UnrOff (c.χ k) (c.S : Set (HeightOneSpectrum (𝓞 D.host.F)))
  ne : ∀ i k, i < k → k < c.m → ∀ τ, c.a i τ ≠ c.a k τ
  one_le : 1 ≤ c.n
  step : c.n + 2 ≤ c.t

structure PiLocalization₂ (D : D7) where
  V : HSp D
  par : D.what₂.Tau → SPar
  M : DSModel V par
  J : Subgroup (GA D V)
  ν : Measure (GA D V)
  fd : Set (GA D V)

abbrev PiLocalization₂.Λ (s : PiLocalization₂ D) : Submodule (𝓞 D.host.E) (Fin s.V.rank → D.host.E) := GlobalTheory.AdelicU.frameLat s.V

def intOff (c : Com D) (s : PiLocalization₂ D) : Set (GA D s.V) :=
  {g | ∀ v ∉ c.S, GlobalTheory.AdelicU.proj D.sp.cm.sig s.V.gram v g ∈ GlobalTheory.AdelicU.stabLoc D.sp.cm.sig s.V.gram s.Λ v}

def PiLocalization₂.big (s : PiLocalization₂ D) : Set (GA D s.V) := {g | ∃ b : GinfC s.V, ∃ κ ∈ s.J, g = (b : GA D s.V) * κ}

structure PiLocalization₂.Is (c : Com D) (j : ℕ) (s : PiLocalization₂ D) : Prop where
  rank : s.V.rank = c.n + j * c.t
  sigOK : s.V.SigOK
  witt : GlobalTheory.Cusp.wittIndex s.V < c.t
  selfDual : IsSelfDualC s.V s.Λ
  fin : s.J ≤ GfC s.V
  isOpen : ∃ U : Subgroup (GA D s.V), IsOpen (U : Set (GA D s.V)) ∧ ∀ k ∈ U, k ∈ GfC s.V → k ∈ s.J
  stab : ∀ k ∈ s.J, ∀ v, GlobalTheory.AdelicU.proj D.sp.cm.sig s.V.gram v k ∈ GlobalTheory.AdelicU.stabLoc D.sp.cm.sig s.V.gram s.Λ v
  off : ∀ k ∈ GfC s.V, k ∈ intOff c s → (∀ v ∈ c.S, GlobalTheory.AdelicU.proj D.sp.cm.sig s.V.gram v k = 1) → k ∈ s.J
  sph : SphOff (s.J : Set (GA D s.V)) 1 c.S
  split : ∀ (P : HeightOneSpectrum (𝓞 D.host.E)) e f, OffS D c.S P → IsPrimeIdem P e f → ∀ k ∈ s.J,
    ∃ k₁ ∈ s.J, ∃ k₂ ∈ s.J, SuppF s.V f k₁ ∧ SuppF s.V (1 - f) k₂ ∧ k = k₁ * k₂
  haar : s.ν.IsHaarMeasure
  fund : IsFundamentalDomain (GQ s.V) s.fd s.ν

abbrev PiLocalization₂.CC (c : Com D) (s : PiLocalization₂ D) : Submodule ℂ (SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) := MultT c.θ s.M (s.J : Set (GA D s.V)) 1

abbrev PiLocalization₂.val {c : Com D} {s : PiLocalization₂ D} (u : s.CC c) (v : SmT s.M) : GA D s.V → ℂ :=
  (u : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) v

def PiLocalization₂.KF (s : PiLocalization₂ D) : Submodule ℂ (SmT s.M) :=
  Submodule.span ℂ {w | ∃ v : s.M.Vec, (∀ τ, (v τ : s.M.H τ) ∈ GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.kfin s.M τ) ∧ w = PiTensorProduct.tprod ℂ v}


variable {c : Com D} {s s' : PiLocalization₂ D}

def coefW (ω : GA D s.V × GA D s'.V →* Module.End ℂ (WO s.V s'.V → ℂ)) (m : Measure (WO s.V s'.V)) (X : Set (WO s.V s'.V))
    (Φ : WO s.V s'.V → ℂ) (g : GA D s.V) : ℂ := ∫ w in X, ω (g, 1) Φ w * conj (Φ w) ∂m

structure PreStep (c : Com D) (k : ℕ) (s s' : PiLocalization₂ D) (ω : GA D s.V × GA D s'.V →* Module.End ℂ (WO s.V s'.V → ℂ))
    (f : WO s.V s'.V → ℂ) : Prop where
  weil : IsWeilDatumO c.ψ s.V s'.V (c.χ k) (c.χ k) ω
  par : ∀ τ, UpPair c.t (s.par τ) (s'.par τ) (c.a k τ) (c.a k τ)
  vac : IsVacVec c.ψ c.θ s.M s'.M f
  sph : GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.IsSphOff c.ψ s.V s'.V s.Λ s'.Λ c.S f
  law : ∀ φ, ∀ κ ∈ s.J, ∀ κ' ∈ s'.J, ω (κ, κ') (ptOf c.ψ c.θ s.M s'.M f φ) = ptOf c.ψ c.θ s.M s'.M f φ
  supp : ∀ m X, IsCovolOne (ratL s'.V s.V) m X → ∀ φ, ∀ g ∈ intOff c s, g ∉ s.big →
    coefW ω m X (ptOf c.ψ c.θ s.M s'.M f φ) g = 0

structure Step (c : Com D) (s s' : PiLocalization₂ D) where
  ω : GA D s.V × GA D s'.V →* Module.End ℂ (WO s.V s'.V → ℂ)
  f : WO s.V s'.V → ℂ
  It : PolF D s'.V.rank s.V.rank →ₗ[ℂ] SmT s'.M →ₗ[ℂ] SmT s.M
  io : s'.CC c →ₗ[ℂ] s.CC c

def Step.pt (p : Step c s s') : PolF D s'.V.rank s.V.rank → (WO s.V s'.V → ℂ) := ptOf c.ψ c.θ s.M s'.M p.f

structure Step.Is (k : ℕ) (p : Step c s s') : Prop where
  pre : PreStep c k s s' p.ω p.f
  it : IsItW c.θ s.M s'.M p.ω p.pt p.It
  io : Lift.IsIo s'.ν s'.fd (thetaKO p.ω) p.pt p.It (s'.CC c) (s.CC c) p.io

inductive Reach (c : Com D) (s₀ : PiLocalization₂ D) : ℕ → ∀ s : PiLocalization₂ D, (s.CC c →ₗ[ℂ] s₀.CC c) → Prop
  | zero : Reach c s₀ 0 s₀ LinearMap.id
  | step {k : ℕ} {s : PiLocalization₂ D} {Θ : s.CC c →ₗ[ℂ] s₀.CC c} (h : Reach c s₀ k s Θ) {s' : PiLocalization₂ D} (hs' : s'.Is c (k + 1))
      (p : Step c s s') (hp : p.Is k) : Reach c s₀ (k + 1) s' (Θ ∘ₗ p.io)





























end GlobalTheory.EvenOnto

end
