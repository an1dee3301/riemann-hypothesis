module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniversalAnticyclotomicCharacterLaws

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX
  GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

namespace GlobalTheory.HeightCounting.FormsStep

section Forms

variable (D : D7) (T : TwR D.LL0 D.nd) (S : RatDat D.ntw)

def readT (i : T.Tw) (b : Bool) : ↥D.LL0 →+* FractionRing (T.O i) :=
  (IsFractionRing.map (A := T.O0 i) (B := T.O i) (K := FractionRing (T.O0 i)) (L := FractionRing (T.O i))
    (T.O_inj i)).comp (if b then T.emb0 i else T.emb0b i)

def KT (i : T.Tw) (_b : Bool) : Type := FractionRing (T.O i)

instance (i : T.Tw) (b : Bool) : Field (KT D T i b) := inferInstanceAs (Field (FractionRing (T.O i)))

instance algKT (i : T.Tw) (b : Bool) : Algebra S.Ks (KT D T i b) := ((readT D T i b).comp S.kKs).toAlgebra

def WKr (j : ℕ) : Submodule S.Ks (S.WL j) := if 1 ≤ j ∧ j ≤ D.R.m then (S.A j).WK else ⊥



def FmT (i : T.Tw) (j : ℕ) (b : Bool) : Type := KT D T i b ⊗[S.Ks] ↥(WKr D S j)

instance acgFmT (i : T.Tw) (j : ℕ) (b : Bool) : AddCommGroup (FmT D T S i j b) :=
  inferInstanceAs (AddCommGroup (KT D T i b ⊗[S.Ks] ↥(WKr D S j)))

instance modKFmT (i : T.Tw) (j : ℕ) (b : Bool) : Module (FractionRing (T.O i)) (FmT D T S i j b) :=
  inferInstanceAs (Module (KT D T i b) (KT D T i b ⊗[S.Ks] ↥(WKr D S j)))

instance modOFmT (i : T.Tw) (j : ℕ) (b : Bool) : Module (T.O i) (FmT D T S i j b) :=
  Module.compHom (FmT D T S i j b) (algebraMap (T.O i) (FractionRing (T.O i)))

instance towFmT (i : T.Tw) (j : ℕ) (b : Bool) : IsScalarTower (T.O i) (FractionRing (T.O i)) (FmT D T S i j b) :=
  IsScalarTower.of_algebraMap_smul fun _ _ => rfl


end Forms

section Act

variable (D : D7) (T : TwR D.LL0 D.nd) (S : RatDat D.ntw)










def psiUT (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (i : T.Tw) (b : Bool) :
    Formalism.IndefR.NX.U D.nd →* (FractionRing (T.O i))ˣ :=
  (Units.map (readT D T i b).toMonoidHom).comp (psiUOf D.nd (NX.xiRed D) θ)

instance instFiniteFiniteLevelQuotientGroup : Finite (G0g D.nd) := by
  haveI : ∀ k, NeZero (D.host.g k) := fun k => ⟨(D.host.g_prime k).ne_zero⟩
  infer_instance











end Act

section Lat

variable (D : D7) (T : TwR D.LL0 D.nd) (S : RatDat D.ntw) (In : RatIn D S)








structure SigData where
  Sig : T.Tw → Type
  [fin : ∀ i, Fintype (Sig i)]
  jS : ∀ i, Sig i → ℕ
  jS_range : ∀ i s, 1 ≤ jS i s ∧ jS i s ≤ D.R.m
  side : ∀ i, Sig i → Bool
  hEig : ∀ i, Sig i → ℕ → PlE D.host → T.O i
  rowS : ∀ i, Sig i → D.what₂.FT

attribute [instance] SigData.fin

end Lat

section Make

variable (D : D7) (T : TwR D.LL0 D.nd) (S : RatDat D.ntw) (In : RatIn D S)









end Make

section Mt

variable (D : D7) (T : TwR D.LL0 D.nd)

structure WtData where
  Wt : T.Tw → ℕ → Bool → Type
  [acg : ∀ i j b, AddCommGroup (Wt i j b)]
  [mod : ∀ i j b, Module (FractionRing (T.O i)) (Wt i j b)]
  [fd : ∀ i j b, FiniteDimensional (FractionRing (T.O i)) (Wt i j b)]
  rhoW : ∀ i j b, Representation (FractionRing (T.O i)) (GQ D.host.E D.R.nV) (Wt i j b)

attribute [instance] WtData.acg WtData.mod WtData.fd

def toKkT (i : T.Tw) (k : ℕ) : FractionRing (T.O i) →+* FractionRing (T.Ok i k) :=
  IsFractionRing.map (A := T.O i) (B := T.Ok i k) (K := FractionRing (T.O i)) (L := FractionRing (T.Ok i k))
    (j := algebraMap (T.O i) (T.Ok i k)) (T.Ok_inj i k)

abbrev algKkT (i : T.Tw) (k : ℕ) : Algebra (FractionRing (T.O i)) (FractionRing (T.Ok i k)) := (toKkT D T i k).toAlgebra

attribute [local instance] algKkT

abbrev WkT (wt : WtData D T) (i : T.Tw) (j : ℕ) (b : Bool) (k : ℕ) : Type :=
  FractionRing (T.Ok i k) ⊗[FractionRing (T.O i)] wt.Wt i j b

def rhoKT (wt : WtData D T) (i : T.Tw) (j : ℕ) (b : Bool) (k : ℕ) :
    Representation (FractionRing (T.Ok i k)) (GQ D.host.E D.R.nV) (WkT D T wt i j b k) :=
  bcRep (K' := FractionRing (T.Ok i k)) (wt.rhoW i j b)

structure LevT (i : T.Tw) (k : ℕ) where
  J : Subgroup (GAf D.host.E D.R.nV)
  χ : J →* (FractionRing (T.Ok i k))ˣ
  QP : Finset (PlE D.host)
  DP : Finset (PlE D.host)
  sp : PlE D.host → SplitPlace D.host.E
  redG : ∀ kv : (Σ kk : Fin 2, D.nd.PlG kk),
    (sp (NX.pG D kv)).v.adicCompletionIntegers (maximalRealSubfield D.host.E) →+* ZMod (D.host.g kv.1)


open Classical in
def MtSubT (wt : WtData D T) (i : T.Tw) (j : ℕ) (b : Bool) (k : ℕ) (Good : LevT D T i k → Prop) :
    Submodule (FractionRing (T.Ok i k)) (GAf D.host.E D.R.nV → WkT D T wt i j b k) :=
  if h : ∃ L : LevT D T i k, Good L ∧
      FiniteDimensional (FractionRing (T.Ok i k)) ↥(NX.TypeSpF D.host.E D.R.nV (FractionRing (T.Ok i k)) (rhoKT D T wt i j b k) L.J L.χ)
  then NX.TypeSpF D.host.E D.R.nV (FractionRing (T.Ok i k)) (rhoKT D T wt i j b k) h.choose.J h.choose.χ
  else ⊥

theorem fd_MtSubT (wt : WtData D T) (i : T.Tw) (j : ℕ) (b : Bool) (k : ℕ) (Good : LevT D T i k → Prop) :
    FiniteDimensional (FractionRing (T.Ok i k)) ↥(MtSubT D T wt i j b k Good) := by
  by_cases h : ∃ L : LevT D T i k, Good L ∧
      FiniteDimensional (FractionRing (T.Ok i k)) ↥(NX.TypeSpF D.host.E D.R.nV (FractionRing (T.Ok i k)) (rhoKT D T wt i j b k) L.J L.χ)
  · rw [MtSubT, dite_eq_left h]
    exact h.choose_spec.2
  · rw [MtSubT, dite_eq_right h]
    infer_instance

end Mt

section Laws

variable (D : D7) (T : TwR D.LL0 D.nd)

attribute [local instance] algKkT


open Classical in
def psiUTotT (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (i : T.Tw) (b : Bool) (u : G0g D.nd) :
    FractionRing (T.O i) :=
  if h : u ∈ Formalism.IndefR.NX.U D.nd then ((psiUT D T θ i b ⟨u, h⟩ : (FractionRing (T.O i))ˣ) : FractionRing (T.O i)) else 1


open Classical in
def gValT (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (i : T.Tw) (k : ℕ) (b : Bool)
    (kv : Σ k : Fin 2, D.nd.PlG k) (s : SplitPlace D.host.E)
    (red : s.v.adicCompletionIntegers (maximalRealSubfield D.host.E) →+* ZMod (D.host.g kv.1))
    (τ : (ZMod (D.host.g kv.1))ˣ →* (FractionRing (T.O i))ˣ)
    (x : Matrix (Fin D.R.nV) (Fin D.R.nV) (s.v.adicCompletion (maximalRealSubfield D.host.E))) : FractionRing (T.Ok i k) :=
  toKkT D T i k (psiUTotT D T θ i b (Pi.mulSingle kv
    (NX.glOf (NX.redMat s.v red (NX.topR (Nat.le_add_right D.R.r D.R.t : D.R.r ≤ D.R.nV) x))))) *
  (if h : IsUnit (red (NX.intLift s.v (NX.detT D.R.r x))) then
    toKkT D T i k ((τ h.unit : (FractionRing (T.O i))ˣ) : FractionRing (T.O i)) else 1)

def baseCoeffToFractionRing (i : T.Tw) : T.O0 i →+* FractionRing (T.O i) :=
  (algebraMap (T.O i) (FractionRing (T.O i))).comp (algebraMap (T.O0 i) (T.O i))

def baseCoeffToExtFractionRing (i : T.Tw) (k : ℕ) : T.O0 i →+* FractionRing (T.Ok i k) :=
  (algebraMap (T.Ok i k) (FractionRing (T.Ok i k))).comp ((algebraMap (T.O i) (T.Ok i k)).comp (algebraMap (T.O0 i) (T.O i)))

def TauTameT (i : T.Tw) (j : ℕ) (b : Bool) (kv : Σ kk : Fin 2, D.nd.PlG kk) : Prop :=
  ∃ τ : (ZMod (D.host.g kv.1))ˣ →* (FractionRing (T.O i))ˣ, ∀ (x : (ZMod (D.host.g kv.1))ˣ) (u : 𝓞 D.host.E),
    (((x : ZMod (D.host.g kv.1)).val : 𝓞 D.host.E) - u) ∈ (NX.pG D kv).asIdeal →
    ((τ x : (FractionRing (T.O i))ˣ) : FractionRing (T.O i)) = baseCoeffToFractionRing D T i (NX.tameVal (T.chi1 i j b) (NX.pG D kv) 1 u).1


open Classical in
def tauT (i : T.Tw) (j : ℕ) (b : Bool) (kv : Σ kk : Fin 2, D.nd.PlG kk) :
    (ZMod (D.host.g kv.1))ˣ →* (FractionRing (T.O i))ˣ :=
  if h : TauTameT D T i j b kv then h.choose else 1

def badVT (i : T.Tw) (Q : Finset (PlE D.host)) : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E))) :=
  {v | ∃ w : PlE D.host, NG.OverPl w v ∧ (w ∈ Q ∨ (∃ k, w ∈ placesOver D.host.E (D.host.g k)) ∨ w ∈ T.pD i)}

def LevLawsT (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host)
    (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (i : T.Tw) (j : ℕ) (b : Bool) (k : ℕ)
    (Q : Finset (PlE D.host)) (ψ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* (T.Ok i k)ˣ) (L : LevT D T i k) : Prop :=
  (∃ N : ℕ, 0 < N ∧ ∀ κ, NG.Cong D.host.E D.R.nV N κ → ∃ h : κ ∈ L.J, L.χ ⟨κ, h⟩ = 1) ∧
  NX.HypOutsideF L.J L.χ (badVT D T i Q) ∧
  L.QP = qpOf D Pq Q ∧ L.DP = qpOf D Pq (T.pD i) ∧
  L.QP ⊆ Q ∧ (∀ P ∈ Q, ∃ P' ∈ L.QP, P' = P ∨ IsConjPl D.host P P') ∧
  (∀ P ∈ L.QP, ∀ P' ∈ L.QP, ¬ IsConjPl D.host P P') ∧
  L.DP ⊆ T.pD i ∧ (∀ P ∈ T.pD i, ∃ P' ∈ L.DP, P' = P ∨ IsConjPl D.host P P') ∧
  (∀ P ∈ L.DP, ∀ P' ∈ L.DP, ¬ IsConjPl D.host P P') ∧
  (∀ P, (P ∈ L.QP ∨ P ∈ L.DP ∨ ∃ kv, P = NX.pG D kv) → (L.sp P).w = P) ∧
  (∀ κ : GAf D.host.E D.R.nV, κ ∈ L.J ↔ κ ∈ Umax D.host.E D.R.nV ∧
    (∀ kv, NX.InLevG (L.sp (NX.pG D kv)).v D.R.r (NX.locM (L.sp (NX.pG D kv)) κ)) ∧
    (∀ P ∈ L.QP, NX.InParah (L.sp P).v D.R.r (NX.locM (L.sp P) κ)) ∧
    (∀ P ∈ L.DP, NX.InParah (L.sp P).v D.R.r (NX.locM (L.sp P) κ))) ∧
  ∀ κ (h : κ ∈ L.J), ((L.χ ⟨κ, h⟩ : (FractionRing (T.Ok i k))ˣ) : FractionRing (T.Ok i k)) =
    (∏ kv : (Σ kk : Fin 2, D.nd.PlG kk), gValT D T θ i k b kv (L.sp (NX.pG D kv)) (L.redG kv) (tauT D T i j b kv)
      (NX.locM (L.sp (NX.pG D kv)) κ)) *
    (∏ P ∈ L.QP, algebraMap (T.Ok i k) (FractionRing (T.Ok i k))
      (NX.tameVal ψ P 1 (NX.resRep (L.sp P) P (NX.detT D.R.r (NX.locM (L.sp P) κ)))).1) *
    (∏ P ∈ L.DP, baseCoeffToExtFractionRing D T i k (NX.tameVal (T.delta i) P (if b then 1 else -1)
      (NX.resRep (L.sp P) P (NX.detT D.R.r (NX.locM (L.sp P) κ)))).1)

end Laws

section Exp

variable (D : D7) (T : TwR D.LL0 D.nd) (S : RatDat D.ntw)



attribute [local instance] algKkT

abbrev MtVT (In : RatIn D S) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (wt : WtData D T) (i : T.Tw) (j : ℕ)
    (b : Bool) (k : ℕ) (Q : Finset (PlE D.host)) (ψ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* (T.Ok i k)ˣ) : Type :=
  ↥(MtSubT D T wt i j b k (LevLawsT D T Pq In.θ i j b k Q ψ))

instance fdMtVT (In : RatIn D S) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (wt : WtData D T) (i : T.Tw)
    (j : ℕ) (b : Bool) (k : ℕ) (Q : Finset (PlE D.host)) (ψ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* (T.Ok i k)ˣ) :
    FiniteDimensional (FractionRing (T.Ok i k)) (MtVT D T S In Pq wt i j b k Q ψ) :=
  fd_MtSubT D T wt i j b k _









end Exp

section Extra

variable (D : D7) (T : TwR D.LL0 D.nd) (S : RatDat D.ntw)




end Extra

end GlobalTheory.HeightCounting.FormsStep
