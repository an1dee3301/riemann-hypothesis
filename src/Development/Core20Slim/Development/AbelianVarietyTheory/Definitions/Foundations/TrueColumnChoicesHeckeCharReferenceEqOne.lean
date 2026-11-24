module

public import Mathlib
public import Formalism.LocalRingCardinality.DataTheta
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsUnitaryOfOrder
public import Formalism.FrobeniusOrbits.Statement
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ZsmulGeneratorEqZeroOfProjection
public import Init.Data.Int.Basic
public import Init.Prelude
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Logic.Equiv.Defs

@[expose] public section

noncomputable section
section

open NumberField IsDedekindDomain

namespace GlobalTheory.Mem.Chr

open Formalism.BasicNotions Formalism.FrobeniusOrbits

def embTau (D : D7) (τ : D.what₂.Tau) : D.host.E →+* ℂ := D.host.emb ((D.eTau τ : D.R.Psi) : D.R.GG)

def eExp (D : D7) (j : Fin D.R.m) (g : D.R.Psi) : ℚ := (D.hc (D.eTau.symm g)).e j

structure CharFrame (D : D7) where

  P : PiBar D.host

  W : Omg D.host

  mu0 : Fin D.R.m → HChar D.host.E
  eta : HChar D.host.E
  chiPsi : HChar D.host.E
  del : HChar D.host.E
  del' : HChar D.host.E
  isMu0 : ∀ j, IsMu0 P W (eExp D j) j.1 (mu0 j)
  isEta : IsEtaT D.host eta
  isChi : IsChiPsi D.host chiPsi
  isDel : IsDelta D.host.pde del
  isDel' : IsDelta D.host.pde' del'






end GlobalTheory.Mem.Chr

end
