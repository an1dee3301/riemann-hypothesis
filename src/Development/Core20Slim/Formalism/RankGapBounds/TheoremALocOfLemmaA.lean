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




end Formalism.RankGapBounds.FormsTensorLocalization
