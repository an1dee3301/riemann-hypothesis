module

public import Mathlib
public import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.FglInvariant
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddXYZOrChordXYZOrOriginXYZNeZero
public import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.CompInv
public import Init.Data.Int.Basic
public import Init.Prelude
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.PowerSeries.Basic

@[expose] public section

noncomputable section

open Formalism.L2.Th1.A ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

universe u v

namespace GlobalTheory.WeierstrassFormal

section Series

open PowerSeries

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] (W : WeierstrassCurve R)





variable (φ : R →+* S)

end Series

section Group

open MvPowerSeries

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] (W : WeierstrassCurve R)

def formalGroup : FormalGroup R where
  toPowerSeries := fgl W
  zero_constantCoeff := (fglChord R W).2.2.2.2.1
  lin_coeff_X := (fglChord R W).2.2.2.2.2.1
  lin_coeff_Y := (fglChord R W).2.2.2.2.2.2
  assoc := by
    obtain ⟨F, hF, -⟩ := fglGroup R W
    rw [← hF]
    exact F.assoc

@[simp] theorem formalGroup_toPowerSeries : (formalGroup W).toPowerSeries = fgl W := rfl



variable {σ : Type*}

theorem map_zsmul (φ : R →+* S) (n : ℤ) : PowerSeries.map φ (zSer W n) = zSer (W.map φ) n :=
  zSerMap R S φ W n

end Group

section Law

open MvPowerSeries

variable {R S : Type} [CommRing R] [CommRing S]

variable (W : WeierstrassCurve R)

end Law

section Points

open MvPowerSeries WeierstrassCurve WeierstrassCurve.Projective GlobalTheory.AddLaw

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) {σ : Type*}




variable {K : Type v} [Field K] (φ : MvPowerSeries σ R →+* K)

end Points

section Examples

open MvPowerSeries

variable {R : Type u} [CommRing R]


end Examples

end GlobalTheory.WeierstrassFormal
