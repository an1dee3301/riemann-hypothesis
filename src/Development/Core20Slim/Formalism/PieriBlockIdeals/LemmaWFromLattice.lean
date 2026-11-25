module

public import Formalism.PieriBlockIdeals.CapelliCentralEnveloping

@[expose] public section

noncomputable section

open Finset PowerSeries

namespace Formalism.CohomologicalDescent.FrobeniusPeriodChange

open Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors

section Subst

variable {R : Type} [CommRing R]

def gamSer (lam : R) (un : R⟦X⟧) : R⟦X⟧ := X * (1 + un * (X - C lam))

def gam0 (lam : R) (un y : R⟦X⟧) : R⟦X⟧ := y.subst (gamSer lam un)

def frob0 (l : ℕ) (y : R⟦X⟧) : R⟦X⟧ := y.subst (X ^ l : R⟦X⟧)

end Subst

def IsUn (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O] (u : ℤ_[l]) (un : O⟦X⟧) :
    Prop :=
  act l O u (pi0 l O) = pi0 l O * (1 + inc l O un * q0 l O)














section Change

variable {k : Type} [CommRing k] {n : ℕ}

def chgPhi (l : ℕ) (g g' : (Matrix (Fin n) (Fin n) k⟦X⟧)ˣ) (P : Matrix (Fin n) (Fin n) k⟦X⟧) :
    Matrix (Fin n) (Fin n) k⟦X⟧ :=
  ((g⁻¹ : (Matrix (Fin n) (Fin n) k⟦X⟧)ˣ) : Matrix (Fin n) (Fin n) k⟦X⟧) * P *
    (g' : Matrix (Fin n) (Fin n) k⟦X⟧).map (frob0 l)

def chgGam (un : k⟦X⟧) (g : (Matrix (Fin n) (Fin n) k⟦X⟧)ˣ) (D : Matrix (Fin n) (Fin n) k⟦X⟧) :
    Matrix (Fin n) (Fin n) k⟦X⟧ :=
  ((g⁻¹ : (Matrix (Fin n) (Fin n) k⟦X⟧)ˣ) : Matrix (Fin n) (Fin n) k⟦X⟧) * (1 + (X : k⟦X⟧) • D) *
    (g : Matrix (Fin n) (Fin n) k⟦X⟧).map (gam0 0 un)


end Change



structure Lat (ι : Type) (n : ℕ) (O : Type) [CommRing O] where
  P : ι → Matrix (Fin n) (Fin n) O⟦X⟧
  D : ι → Matrix (Fin n) (Fin n) O⟦X⟧
  Th : ι → Matrix (Fin n) (Fin n) O



structure WLat (ι : Type) (t n : ℕ) (O F : Type) [CommRing O] [Field F] where
  red : O →+* F
  un : O⟦X⟧
  N : Lat ι n O
  Npsi : Fin t → Lat ι 1 O
  g : ι → (Matrix (Fin n) (Fin n) F⟦X⟧)ˣ
  b : Fin n → ℕ
  pos : Fin t → Fin n
  w : ι → Fin t → (F⟦X⟧)ˣ

section WLat

variable {ι : Type} {t n : ℕ} {O F : Type} [CommRing O] [Field F]

def WLat.unbar (W : WLat ι t n O F) : F⟦X⟧ := PowerSeries.map W.red W.un

def WLat.Gam (W : WLat ι t n O F) (i : ι) : Matrix (Fin n) (Fin n) F⟦X⟧ :=
  chgGam W.unbar (W.g i) ((W.N.D i).map (PowerSeries.map W.red))

def WLat.Phi (W : WLat ι t n O F) (l : ℕ) (σ : Equiv.Perm ι) (i : ι) :
    Matrix (Fin n) (Fin n) F⟦X⟧ :=
  chgPhi l (W.g i) (W.g (σ i)) ((W.N.P i).map (PowerSeries.map W.red))


def WFrame (W : WLat ι t n O F) (σ : Equiv.Perm ι) (l h : ℕ) [Fact l.Prime] [Algebra ℤ_[l] O]
    (u : ℤ_[l]ˣ) (c : ℤ_[l]) (U' : ι → Fin n → ℤ) (wt kap : ι → Fin t → ℤ) : Prop :=
  ((u : ℤ_[l]) = 1 + (l : ℤ_[l]) * c ∧ IsUnit c ∧ IsUn l O (u : ℤ_[l]) W.un) ∧
  (∀ i j, 0 ≤ U' i j ∧ U' i j ≤ (h : ℤ)) ∧ (∀ i s, 0 ≤ wt i s ∧ wt i s ≤ (h : ℤ)) ∧
  (Function.Injective W.pos ∧ ∀ s j, W.b j = W.b (W.pos s) → j = W.pos s) ∧
  (∀ i, (W.Phi l σ i).BlockTriangular W.b) ∧ (∀ i, (W.Gam i).BlockTriangular W.b) ∧
  (∀ i s,
    ((frob0 l (W.w (σ i) s : F⟦X⟧) : F⟦X⟧) : LaurentSeries F) *
        ((X : F⟦X⟧) : LaurentSeries F) ^ ((l : ℤ) * kap (σ i) s) *
        ((PowerSeries.map W.red ((W.Npsi s).P i 0 0) : F⟦X⟧) : LaurentSeries F) =
      ((W.Phi l σ i (W.pos s) (W.pos s) : F⟦X⟧) : LaurentSeries F) *
        ((W.w i s : F⟦X⟧) : LaurentSeries F) * ((X : F⟦X⟧) : LaurentSeries F) ^ kap i s) ∧
  (∀ i s,
    ((gam0 0 W.unbar (W.w i s : F⟦X⟧) : F⟦X⟧) : LaurentSeries F) *
        ((gamSer 0 W.unbar : F⟦X⟧) : LaurentSeries F) ^ kap i s *
        ((1 + X * PowerSeries.map W.red ((W.Npsi s).D i 0 0) : F⟦X⟧) : LaurentSeries F) =
      ((W.Gam i (W.pos s) (W.pos s) : F⟦X⟧) : LaurentSeries F) *
        ((W.w i s : F⟦X⟧) : LaurentSeries F) * ((X : F⟦X⟧) : LaurentSeries F) ^ kap i s)


end WLat





def IsLocExp (l : ℕ) [Fact l.Prime] (O L : Type) [CommRing O] [Algebra ℤ_[l] O] [Field L]
    (em : O →+* L) (x : O) (u : ℤ_[l]) (jj : O⟦X⟧ →+* L⟦X⟧) : Prop :=
  (∀ a, jj (C a) = C (em a)) ∧ Associated (jj (X - C x)) X ∧
  (∀ f, jj (act l O u f) = rescale (em (algebraMap ℤ_[l] O u)) (jj f))


def LatN {ι : Type} {n : ℕ} {O L : Type} [CommRing O] [Field L] (l : ℕ) [Fact l.Prime]
    [Algebra ℤ_[l] O] (N : Lat ι n O) (h : ℕ) (u : ℤ_[l]ˣ) (U' : ι → Fin n → ℤ) (em : O →+* L)
    (jj : ℕ → O⟦X⟧ →+* L⟦X⟧) : Prop :=
  (∀ i, ∃ Q : Matrix (Fin n) (Fin n) O⟦X⟧,
    (N.P i).map (inc l O) * Q = (q l O ^ h) • (1 : Matrix (Fin n) (Fin n) O⟦X⟧)) ∧
  (∀ i a b, (X - C (l : O)) ∣ N.D i a b - C (N.Th i a b)) ∧
  (∀ i, ∀ b ∈ Finset.Ioo 0 l, ∃ G H : (Matrix (Fin n) (Fin n) L⟦X⟧)ˣ,
    (N.P i).map (fun y => jj b (inc l O y)) =
      (G : Matrix (Fin n) (Fin n) L⟦X⟧) * Matrix.diagonal (fun a => (X : L⟦X⟧) ^ (U' i a).toNat) *
        (H : Matrix (Fin n) (Fin n) L⟦X⟧) ∧
    ((1 + (X : O⟦X⟧) • N.D i).map (fun y => jj b (inc l O y))) *
        ((G : Matrix (Fin n) (Fin n) L⟦X⟧) *
          Matrix.diagonal (fun a => (X : L⟦X⟧) ^ (U' i a).toNat)).map
          (rescale (em (algebraMap ℤ_[l] O (u : ℤ_[l])))) =
      (G : Matrix (Fin n) (Fin n) L⟦X⟧) * Matrix.diagonal (fun a => (X : L⟦X⟧) ^ (U' i a).toNat))


def NInputs {ι : Type} {t n : ℕ} {O F L : Type} [CommRing O] [Field F] [Field L]
    (W : WLat ι t n O F) (σ : Equiv.Perm ι) (l h : ℕ) [Fact l.Prime] [Algebra ℤ_[l] O]
    (u : ℤ_[l]ˣ) (c : ℤ_[l]) (U' : ι → Fin n → ℤ) (wt kap : ι → Fin t → ℤ) (I : Ideal O) (ζ : O)
    (em : O →+* L) (jj : ℕ → O⟦X⟧ →+* L⟦X⟧) : Prop :=
  WFrame W σ l h u c U' wt kap ∧
  (IsPrimitiveRoot ζ l ∧ ζ - 1 ∈ I ∧ Function.Injective em ∧
    ∀ b ∈ Finset.Ioo 0 l, IsLocExp l O L em (ζ ^ b - 1) (u : ℤ_[l]) (jj b)) ∧
  LatN l W.N h u U' em jj ∧ ∀ s, LatN l (W.Npsi s) h u (fun i _ => wt i s) em jj



end Formalism.CohomologicalDescent.FrobeniusPeriodChange
