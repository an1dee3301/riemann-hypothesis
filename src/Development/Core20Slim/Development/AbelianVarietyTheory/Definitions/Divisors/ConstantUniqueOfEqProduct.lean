module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Formalism.LocalRingCardinality.SpanPowerMembership.Spaces
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.Divisors.MarkAd
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsInfFamAndStdChar
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnitaryOnTheta
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.Divisibility.LiftLat
public import Formalism.LocalToGlobal.ProjectiveLattices.CuspidalL2Subspace

@[expose] public section

open NumberField Matrix IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult
  Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT GlobalTheory.WeilParts
open scoped TensorProduct Classical

namespace GlobalTheory.AdTh.PairModel

noncomputable section

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}



variable {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {C : Core D} [Algebra C.Q.c.F D.what₂.LL] {R : RealDat D A C.Q.c.F} {i : Fin D.R.m} {Tp : Type} {tup : Tp → T0}

end

end GlobalTheory.AdTh.PairModel
