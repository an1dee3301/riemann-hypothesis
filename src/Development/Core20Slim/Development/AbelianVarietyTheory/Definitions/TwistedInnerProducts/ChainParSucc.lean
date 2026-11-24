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


structure Com (D : D7) where
  θ : InfFam D
  ψ : AddChar (AF D.host.F) ℂ
  S : Finset (HeightOneSpectrum (𝓞 D.host.F))
  n : ℕ
  t : ℕ
  m : ℕ
  χ : ℕ → ((AE D)ˣ →* Circle)
  a : ℕ → D.what₂.Tau → ℚ


structure PiLocalization₂ (D : D7) where
  V : HSp D
  par : D.what₂.Tau → SPar
  M : DSModel V par
  J : Subgroup (GA D V)
  ν : Measure (GA D V)
  fd : Set (GA D V)









variable {c : Com D} {s s' : PiLocalization₂ D}



































end GlobalTheory.EvenOnto

end
