module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.ThetaSeriesTies
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ResidueInjectivityAt
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.FoundationProofs.SplitOffBadOfSuppSplitOff
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.FoundationProofs.NablaDeltaOperatorLatticePreserved
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LatticeExtensionAlongFieldEmbeddingDuals
public import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec
public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.SecondStepGluing

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TraceClassRank

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT
open GlobalTheory.FormTies GlobalTheory.OnTies
open Formalism.HermitianLatticesTheory (localization₂)
open scoped TensorProduct Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Lat


variable {K : Type} [Field K] [NumberField K] {n n' : ℕ}


end Lat

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

section Adelic

variable {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m)










variable {R i}













end Adelic

end GlobalTheory.TraceClassRank
