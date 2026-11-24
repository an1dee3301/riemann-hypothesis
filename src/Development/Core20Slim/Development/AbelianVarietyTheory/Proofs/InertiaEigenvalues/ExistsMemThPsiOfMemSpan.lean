module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIsScalar

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum
  IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries
open Formalism.IndefR.Links
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx)
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.SeriesTie
attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Ser

variable {D : D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}


open Classical in
def specXi (ρ : Setup X) (Y : NExp D.R D.host D.what₂ D.LL0 N X) (i : X.Tw) (j : Fin D.R.m) (b : Bool) (k : ℕ)
    (Q : Finset (Pl D.host.E)) (M : ℕ) (χ : Multiplicative (DelQM D.host (X.l i) Q M) →* (X.Ok i k)ˣ) (h : GA D (Vc D j))
    (P : PolF D (Wc D j).rank (Vc D j).rank) : GA D (Wc D j) → ℂ :=
  ∑ a, ρ.eOk i b k (χ (Multiplicative.ofAdd (spread Y i Q M (ρ.ch i) a)) : X.Ok i k) • ρ.xi i j b Y Q M h P a


end Ser

end GlobalTheory.SeriesTie

namespace GlobalTheory.SeriesTie
attribute [local instance] Formalism.BasicNotions.Host.cmStar

section SpecLoc

variable {D : D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}


open Classical in
def specLoc (ρ : Setup X) (Y : NExp D.R D.host D.what₂ D.LL0 N X) (i : X.Tw) (j : Fin D.R.m) (b : Bool) (k : ℕ)
    (Q : Finset (Pl D.host.E)) (M : ℕ) (χ : Multiplicative (DelQM D.host (X.l i) Q M) →* (X.Ok i k)ˣ)
    (PP : ↥(half (ρ.ch i) (admissibleConjugatePairPlaces X i Q M))) (y : Matrix (Fin (Wc D j).rank) (Fin (Vc D j).rank) (kP PP.1)) : ℂ :=
  ∑ c : ZMod (X.l i ^ M), ρ.eOk i b k (χ (Multiplicative.ofAdd (spread Y i Q M (ρ.ch i) (Pi.single PP c))) : X.Ok i k) *
    ((Base.univFam (univOf Y i (admissibleConjugatePairPlaces X i Q M) M ρ.rc) (ρ.β j) PP.1 c y : ℚ) : ℂ)

def specSer (ρ : Setup X) (Y : NExp D.R D.host D.what₂ D.LL0 N X) (i : X.Tw) (j : Fin D.R.m) (b : Bool) (k : ℕ)
    (Q : Finset (Pl D.host.E)) (M : ℕ) (χ : Multiplicative (DelQM D.host (X.l i) Q M) →* (X.Ok i k)ˣ) (h : GA D (Vc D j))
    (P : PolF D (Wc D j).rank (Vc D j).rank) : GA D (Wc D j) → ℂ :=
  twistBy (Wc D j) (ρ.tw i b k Q (χ.comp (Y.delU i Q M))).chi
    (series (ρ.B i j b).F (ρ.om i j b 1) ((ρ.B i j b).vecAt (half (ρ.ch i) (admissibleConjugatePairPlaces X i Q M)) (specLoc ρ Y i j b k Q M χ)) h P)

end SpecLoc

end GlobalTheory.SeriesTie

namespace GlobalTheory.SeriesTie
attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Ser2

variable {D : D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}


end Ser2

end GlobalTheory.SeriesTie
