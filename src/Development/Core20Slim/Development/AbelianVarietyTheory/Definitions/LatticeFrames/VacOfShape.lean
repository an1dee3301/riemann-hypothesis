module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlaceLaws
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.LatticeFrames.DoubleCollapse

@[expose] public section

set_option genSizeOfSpec false
set_option genInjectivity false

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (CharUnramAt)
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl

namespace GlobalTheory.SeeSaw

variable {D : D7}

structure TDat (c : Comm D) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) where

  p : ι → SplitPt D k
  I : List ι

  q : Unif k
  χ : ι → AddChar k Circle
  hχ : ∀ i, HasConductor (χ i) 1

  β : ∀ j i, Frame (p i) (c.X j) (Fin (c.X j).rank)
  Q : ∀ j, ι → Pair k (Fin (c.X j).rank)

  β₀ : ∀ j ρ h i, Frame (p i) (c.bes j ρ h).V₀ (Fin (c.X j).rank ⊕ Fin 1)
  M : ∀ j ρ h, Lat (c.bes j ρ h).V₀

  ζ₀ : Fin c.Lz.rank → D.host.E
  γ : ∀ i, Frame (p i) c.T (Fin c.T.rank)
  γ₀ : ∀ n, n = D.R.m → ∀ i, Frame (p i) (c.X n) (Fin c.T.rank ⊕ Fin 1)

variable {c : Comm D} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {ι : Type}




@[reducible] def VCom.withT (v : VCom c) (Sad : ∀ j, (GA D (c.X j) → ℂ) → GA D (c.X j) → ℂ)
    (op : ∀ j, BiOp (c.X j) (c.X (j + 1)) (c.X (j + 1 + 1))) : VCom c := { v with Sad := Sad, op := op }

variable (v : VCom c) (o : TDat c k ι)











end GlobalTheory.SeeSaw

end
