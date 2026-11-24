module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevChiLift
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicTransportMeasureSecond
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsDatOfTower
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.LatticeFrames.NotBadPrimeBase
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.LatticeFrames.TopFormula
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiPinnedWithFinIff
public import Formalism.LocalRingCardinality.PosOfIsomEmb
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsDefiniteOfAllPlus
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MultValueLeftContLevel

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Fam.FamInhab

open GlobalTheory.Fam.Inhab

variable {D : D7}
variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks]
  [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (P : LevelP R.Pg D.R.r ℂ)




























section Read

variable {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {At : ColumnsAtT D.R C} {Pm : PeriodMap D.R C}
  {M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C At Pm} {bad : Set (HeightOneSpectrum (𝓞 D.host.F))}
  (K : ClassesAtPrimes M bad)

variable {K}

end Read

end GlobalTheory.Fam.FamInhab

end
