module

public import Mathlib
public import Formalism.SatakeDualWeyl.Statement

@[expose] public section

noncomputable section

open TensorProduct

namespace Formalism.RankGapBounds.FormsTensorLocalization

open Formalism.UG


def tensSub {k : Type} [CommRing k] {ι : Type} {A : ι → Type} [∀ i, AddCommGroup (A i)]
    [∀ i, Module k (A i)] (B : ∀ i, Submodule k (A i)) : Submodule k (⨂[k] i, A i) :=
  LinearMap.range (PiTensorProduct.map fun i => (B i).subtype)

def formsIn {G : Type} [Group G] {k : Type} [CommRing k] {W : Type} [AddCommGroup W]
    [Module k W] (Γ K : Subgroup G) (ρK : Representation k K W) (U : Submodule k W) :
    Submodule k (G → W) :=
  AMFK k Γ K ρK ⊓ Submodule.pi Set.univ (fun _ => U)

def locSet {T : Type} [CommRing T] {M : Type} [AddCommGroup M] [Module T M]
    (S : Submonoid T) (N : Set M) : Set (LocalizedModule S M) :=
  {y | ∃ x ∈ N, ∃ s : S, LocalizedModule.mk x s = y}


end Formalism.RankGapBounds.FormsTensorLocalization
