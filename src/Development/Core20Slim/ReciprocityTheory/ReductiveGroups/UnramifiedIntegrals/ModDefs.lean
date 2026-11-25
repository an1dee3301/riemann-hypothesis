module

public import Mathlib
public import Formalism.LocalToGlobal.TorsionIntegrality.CMGoodModels.Statement
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Int.DivMod.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Nat.Div.Basic
public import Init.Data.Nat.Dvd
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Topology
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Finset.Range
public import Mathlib.Data.Finset.Sigma
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Int.Cast.Lemmas
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.NumberTheory.ArithmeticFunction.Defs
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.NumberTheory.Divisors
public import Mathlib.NumberTheory.ModularForms.Basic
public import Mathlib.NumberTheory.ModularForms.Discriminant
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Basic
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.SummationFilter
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.OpenPartialHomeomorph.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open ModularForm EisensteinSeries ModularFormClass

namespace ReciprocityTheory.ChartRestriction.L1

def DD (τ : ℍ) : ℂ := ModularForm.discriminant τ

def AA (τ : ℍ) : ℂ := E₄ τ ^ 3

def jT (τ : ℍ) : ℂ := AA τ / DD τ

def Tm (m : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (m.divisors.sigma fun a => Finset.range (m / a)).image fun x => (x.1, x.2, m / x.1)

def pt (a b e : ℕ) (τ : ℍ) : ℍ := UpperHalfPlane.ofComplex (((a : ℂ) * τ + b) / e)

def fac (t : ℕ × ℕ × ℕ) (τ : ℍ) : ℂ :=
  AA τ * DD (pt t.1 t.2.1 t.2.2 τ) - AA (pt t.1 t.2.1 t.2.2 τ) * DD τ

def Gm (m : ℕ) (τ : ℍ) : ℂ := ∏ t ∈ Tm m, fac t τ

def zetaC (m : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / m)

def Rm (m : ℕ) : Subring ℂ := Subring.closure {zetaC m}

def CoeffIn (R : Subring ℂ) (f : PowerSeries ℂ) : Prop := ∀ n, PowerSeries.coeff n f ∈ R

def IsTauOf (L : PeriodPair) (c : ℂ) (τ : ℍ) : Prop :=
  c ≠ 0 ∧ ∀ x : ℂ, x ∈ L.lattice ↔ ∃ u v : ℤ, x = c * (u * (τ : ℂ) + v)

def Tmat (t : ℕ × ℕ × ℕ) : Matrix (Fin 2) (Fin 2) ℤ := !![(t.1 : ℤ), (t.2.1 : ℤ); 0, (t.2.2 : ℤ)]

def IsMF (k : ℤ) (f : ℍ → ℂ) : Prop := ∃ g : ModularForm 𝒮ℒ k, ∀ τ, g τ = f τ

def e4Z : PowerSeries ℤ :=
  PowerSeries.mk fun n => if n = 0 then 1 else 240 * (ArithmeticFunction.sigma 3 n : ℤ)

def e6Z : PowerSeries ℤ :=
  PowerSeries.mk fun n => if n = 0 then 1 else -504 * (ArithmeticFunction.sigma 5 n : ℤ)

def aZ : PowerSeries ℤ := e4Z ^ 3

def dZ : PowerSeries ℤ := PowerSeries.mk fun n => PowerSeries.coeff n (e4Z ^ 3 - e6Z ^ 2) / 1728

def aC : PowerSeries ℂ := aZ.map (Int.castRingHom ℂ)

def dC : PowerSeries ℂ := dZ.map (Int.castRingHom ℂ)

def xp {R : Type*} [CommRing R] (k : ℕ) (f : PowerSeries R) : PowerSeries R :=
  PowerSeries.mk fun n => if k ∣ n then PowerSeries.coeff (n / k) f else 0

def Conv (f : PowerSeries ℂ) : Prop :=
  ∀ x : ℂ, ‖x‖ < 1 → Summable fun n => ‖PowerSeries.coeff n f‖ * ‖x‖ ^ n

def ev (f : PowerSeries ℂ) (x : ℂ) : ℂ := ∑' n, PowerSeries.coeff n f * x ^ n

def sub1 (c : ℂ) (k : ℕ) (f : PowerSeries ℂ) : PowerSeries ℂ := xp k (PowerSeries.rescale c f)

def facSer (m : ℕ) (t : ℕ × ℕ × ℕ) : PowerSeries ℂ :=
  xp m aC * sub1 (zetaC t.2.2 ^ t.2.1) (t.1 ^ 2) dC - sub1 (zetaC t.2.2 ^ t.2.1) (t.1 ^ 2) aC * xp m dC

def prodSer (m : ℕ) : PowerSeries ℂ := ∏ t ∈ Tm m, facSer m t

def LowUnit (R : Subring ℂ) (f : PowerSeries ℂ) (n0 : ℕ) (u : ℂ) : Prop :=
  u ∈ R ∧ u⁻¹ ∈ R ∧ u ≠ 0 ∧ (∀ n < n0, PowerSeries.coeff n f = 0) ∧ PowerSeries.coeff n0 f = u

def qm (m : ℕ) (τ : ℍ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * τ / m)

end ReciprocityTheory.ChartRestriction.L1
