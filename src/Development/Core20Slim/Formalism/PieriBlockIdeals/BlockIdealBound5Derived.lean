module

public import Mathlib
public import Formalism.SatakeDualWeyl.Statement
public import Development.Core20Slim.Formalism.RankGapBounds.TheoremALocOfLemmaA
public import Development.Core20Slim.Formalism.PieriBlockIdeals.Statement
public import Development.Core20Slim.Formalism.PieriBlockIdeals.FactorialValuationSum
public import Development.Core20Slim.Formalism.PieriBlockIdeals.StatementLA

@[expose] public section

noncomputable section

open TensorProduct MvPolynomial CategoryTheory CategoryTheory.Limits

namespace Formalism.CohomologicalDescent.DepthNonnegative

open Formalism.UG Formalism.RankGapBounds.FormsTensorLocalization Formalism.GradedWeylDivisibility Formalism.CohomologicalDescent.LD Formalism.CohomologicalDescent.UnitNormBounds


def chainB {O : Type} [CommRing O] {ι : Type} [DecidableEq ι] {Nb : ι → Type} [∀ τ, AddCommGroup (Nb τ)]
    [∀ τ, Module O (Nb τ)] (B : ∀ τ, Submodule O (Nb τ)) (s : Finset ι) : ∀ τ, Submodule O (Nb τ) :=
  fun τ => if τ ∈ s then ⊤ else B τ






def scaleSub {O : Type} [CommRing O] (A : Type) [Ring A] [Algebra O A] (V : Type) [AddCommGroup V]
    [Module O V] [Module A V] [IsScalarTower O A V] (c : O) : Submodule A V where
  carrier := {x | ∃ y : V, x = c • y}
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by rintro _ _ ⟨y, rfl⟩ ⟨z, rfl⟩; exact ⟨y + z, by rw [smul_add]⟩
  smul_mem' := by rintro a _ ⟨y, rfl⟩; exact ⟨a • y, by rw [smul_comm]⟩

def IsSubquot (A : Type) [Ring A] (V G : Type) [AddCommGroup V] [Module A V] [AddCommGroup G]
    [Module A G] : Prop :=
  ∃ (E : Submodule A V) (ψ : E →ₗ[A] G), Function.Surjective ψ



def repOf (O : Type) [CommRing O] {A : Type} [Ring A] [Algebra O A] {G : Type} [Group G]
    {K : Subgroup G} (jK : K →* A) (W : Type) [AddCommGroup W] [Module O W] [Module A W]
    [IsScalarTower O A W] : Representation O K W :=
  ((Algebra.lsmul O O W : A →ₐ[O] Module.End O W) : A →* Module.End O W).comp jK

abbrev Forms (O : Type) [CommRing O] {A : Type} [Ring A] [Algebra O A] {G : Type} [Group G]
    (Γ : Subgroup G) {K : Subgroup G} (jK : K →* A) (W : Type) [AddCommGroup W] [Module O W]
    [Module A W] [IsScalarTower O A W] : Submodule O (G → W) :=
  AMFK O Γ K (repOf O jK W)

def HeckeStable (O : Type) [CommRing O] {A : Type} [Ring A] [Algebra O A] {G : Type} [Group G]
    (Γ : Subgroup G) {K : Subgroup G} (jK : K →* A) (T : Type) [CommRing T] (V : Type)
    [AddCommGroup V] [Module O V] [Module A V] [IsScalarTower O A V] [Module T (Forms O Γ jK V)] :
    Prop :=
  ∀ (U : Submodule A V) (t : T) (f : Forms O Γ jK V), (∀ g, (f : G → V) g ∈ U) →
    ∀ g, ((t • f : Forms O Γ jK V) : G → V) g ∈ U

def HeckeNat (O : Type) [CommRing O] {A : Type} [Ring A] [Algebra O A] {G : Type} [Group G]
    (Γ : Subgroup G) {K : Subgroup G} (jK : K →* A) (T : Type) [CommRing T] (V W : Type)
    [AddCommGroup V] [Module O V] [Module A V] [IsScalarTower O A V] [AddCommGroup W] [Module O W]
    [Module A W] [IsScalarTower O A W] [Module T (Forms O Γ jK V)] [Module T (Forms O Γ jK W)] :
    Prop :=
  ∀ (U : Submodule A V) (ψ : U →ₗ[A] W) (t : T) (f : Forms O Γ jK V) (φ : Forms O Γ jK W)
    (hf : ∀ g, (f : G → V) g ∈ U) (hf' : ∀ g, ((t • f : Forms O Γ jK V) : G → V) g ∈ U),
    (∀ g, (φ : G → W) g = ψ ⟨(f : G → V) g, hf g⟩) →
    ∀ g, ((t • φ : Forms O Γ jK W) : G → W) g = ψ ⟨((t • f : Forms O Γ jK V) : G → V) g, hf' g⟩



def cTau {ι : Type} [DecidableEq ι] (T2 : Finset ι) (ex c' : ι → ℕ) (τ : ι) : ℕ :=
  if τ ∈ T2 then min (ex τ) (c' τ) else ex τ


abbrev NablaT (O : Type) [CommRing O] (N : ℕ) {ι : Type} (lam : ι → ℕ → ℕ) : Type :=
  ⨂[O] τ : ι, dualWeyl O N N (res N (lam τ))

def deltaIn (O : Type) [CommRing O] (N : ℕ) {ι : Type} (lam : ι → ℕ → ℕ) (τ : ι) :
    Submodule O (dualWeyl O N N (res N (lam τ))) :=
  (weyl O N N le_rfl (res N (lam τ))).comap (dualWeyl O N N (res N (lam τ))).subtype

def depthAt (N k : ℕ) {ι : Type} (j : ι → ℕ) (lam : ι → ℕ → ℕ) (τ : ι) (w : Fin N → ℕ) : ℤ :=
  depth2 (res N (varpi (k + j τ))) (res N (lam τ)) w


structure Shape (N k j t q h : ℕ) (lam : ℕ → ℕ) (xm xp : ℤ) : Prop where
  what₂ : k + j + t + q = N
  anti : ∀ a b, a ≤ b → b < N → lam b ≤ lam a
  block : ∀ a, k + j ≤ a → a < k + j + t → lam a = lam (k + j)
  spread : lam 0 + N ≤ h + lam (N - 1) + 1
  cloud : ∀ a, a < k → xm ≤ UN N lam a ∧ UN N lam a ≤ xp
  lows : ∀ a, k ≤ a → a < k + j → UN N lam a < xm
  above : UN N lam (k + j) < xm
  le : xm ≤ xp
  top : xp - UN N lam (k + j) ≤ (h : ℤ)

def TopInputs (O : Type) [CommRing O] (A : Type) [Ring A] [Algebra O A] {G : Type} [Group G]
    (Γ : Subgroup G) {K : Subgroup G} (jK : K →* A) {ι : Type} [DecidableEq ι] (l N k t h : ℕ)
    (lam : ι → ℕ → ℕ) (T2 : Finset ι) (j q : ι → ℕ) (xm xp : ι → ℤ) (ecl ex i : ι → ℕ)
    [Module A (NablaT O N lam)] [IsScalarTower O A (NablaT O N lam)] (T : Type) [CommRing T]
    [Module T (Forms O Γ jK (NablaT O N lam))] (S : Submonoid T) (ϖ : O) (n₀ : ℕ)
    (e : ι → (Fin N → ℕ) → A) {Λ : Type} (L : Λ → Type) [∀ μ, AddCommGroup (L μ)]
    [∀ μ, Module O (L μ)] [∀ μ, Module A (L μ)] [∀ μ, IsScalarTower O A (L μ)]
    [∀ μ, Module T (Forms O Γ jK (L μ))] (hwt : Λ → ι → Fin N → ℕ) : Prop :=
  l.Prime ∧ (∀ m : ℕ, ¬ l ∣ m → IsUnit (m : O)) ∧ Finite (O ⧸ Ideal.span {(l : O)}) ∧
  (l : O) ∣ ϖ ^ n₀ ∧ h < l ^ 2 ∧ 1 ≤ t ∧
  (∀ τ ∈ T2, Shape N k (j τ) t (q τ) h (lam τ) (xm τ) (xp τ)) ∧
  (∀ τ ∈ T2, ∀ μ : Fin k → ℕ, ExpLe l k (res k (lam τ)) μ (ecl τ)) ∧
  (∀ τ, LA.InclZ N N le_rfl (res N (lam τ)) l (ex τ)) ∧
  (∀ (s : Finset ι) (a : A), ∀ x ∈ tensSub (chainB (deltaIn O N lam) s),
    a • x ∈ tensSub (chainB (deltaIn O N lam) s)) ∧
  (∀ τ w (x : ∀ τ, dualWeyl O N N (res N (lam τ))) (y : dualWeyl O N N (res N (lam τ))),
    (y : MvPolynomial (Fin N × Fin N) O) =
      weightedHomogeneousComponent (rowW N N) w (x τ : MvPolynomial (Fin N × Fin N) O) →
    e τ w • PiTensorProduct.tprod O x = PiTensorProduct.tprod O (Function.update x τ y)) ∧
  HeckeStable O Γ jK T (NablaT O N lam) ∧ (∀ μ, HeckeNat O Γ jK T (NablaT O N lam) (L μ)) ∧
  (∀ (Gm : Type) [AddCommGroup Gm] [Module A Gm], IsSimpleModule A Gm →
    IsSubquot A (NablaT O N lam ⧸ scaleSub A (NablaT O N lam) ϖ) Gm → ∃ μ, Nonempty (Gm ≃ₗ[A] L μ)) ∧
  (∀ μ τ, ∃ z : L μ, e τ (hwt μ τ) • z ≠ 0) ∧
  (∀ μ, IsSubquot A (NablaT O N lam ⧸ scaleSub A (NablaT O N lam) ϖ) (L μ) →
    ¬ Subsingleton (LocalizedModule S (Forms O Γ jK (L μ))) →
    ∀ τ ∈ T2, depthAt N k j lam τ (hwt μ τ) ≤ (i τ : ℤ))

def TopIncl (O : Type) [CommRing O] {A : Type} [Ring A] [Algebra O A] {G : Type} [Group G]
    (Γ : Subgroup G) {K : Subgroup G} (jK : K →* A) {ι : Type} (l N : ℕ) (lam : ι → ℕ → ℕ)
    [Module A (NablaT O N lam)] [IsScalarTower O A (NablaT O N lam)] {T : Type} [CommRing T]
    [Algebra O T] [Module T (Forms O Γ jK (NablaT O N lam))] (S : Submonoid T) (J : ℕ) : Prop :=
  ∀ y : LocalizedModule S (Forms O Γ jK (NablaT O N lam)),
    (algebraMap O T (l : O)) ^ J • y ∈
      locSet S {x : Forms O Γ jK (NablaT O N lam) |
        (x : G → NablaT O N lam) ∈ formsIn Γ K (repOf O jK (NablaT O N lam)) (tensSub (deltaIn O N lam))}








def cFloorCoarse (l N k t h : ℕ) {ι : Type} (lam : ι → ℕ → ℕ) (j q : ι → ℕ) (xm xp : ι → ℤ)
    (ecl i : ι → ℕ) (τ : ι) : ℕ :=
  ⌊cCoarse l k (j τ) t (q τ) h N (ecl τ) (xm τ) (xp τ) (UN N (lam τ) (k + j τ)) (i τ : ℝ)⌋₊



end Formalism.CohomologicalDescent.DepthNonnegative
