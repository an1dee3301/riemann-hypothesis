module

public import Mathlib
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegIdxOfIsStd
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseFits
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemPairLat
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnitCharTriangle
public import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Classical
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Int.Order
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Omega.Coeffs
public import Init.Omega.Constraint
public import Init.Omega.Int
public import Init.Omega.LinearCombo
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Even
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.UnitBall
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fin.SuccPred
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Defs
public import Mathlib.Order.Defs.Lattice
public import Mathlib.RingTheory.Norm.Defs
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SqStepBig

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Geo Chars)

variable {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts}

def EmbCM (Bs : Base D.host.F D.host.E) : Prop := ∀ w, ∃ τ, ∀ x, (Bs.emb w).1 x = starRingEnd ℂ (tauE D τ x)

def OverH (c : D.host.E) (A : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) {n : ℕ}
    (V : Spc D.host.F D.host.E n) : Prop :=
  ∃ h : A.rank = n, V.J = c • Matrix.reindex (finCongr h) (finCongr h) A.gram ∧
    ∀ y, y ∈ V.L ↔ (fun i => star (y (finCongr h i))) ∈ Λ

def OverW (WW : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin WW.rank → D.host.E)) {d : ℕ} (Z : Spc D.host.F D.host.E d) : Prop :=
  ∃ h : WW.rank = d, Z.J = D.host.xi0 • Matrix.reindex (finCongr h) (finCongr h) WW.gram.transpose ∧
    ∀ y, y ∈ Z.L ↔ (fun i => y (finCongr h i)) ∈ GlobalTheory.SkewLat.scLat D.host.AA Λ

def Over {A A' WW : HSp D} (X : Tri T A A' WW) {a a' : ℕ} (Γ : Geo D.sp.cm.sig a a') : Prop :=
  OverH 1 A X.rA.Λ Γ.V ∧ OverH (-1) A' X.rA'.Λ Γ.V' ∧ OverW WW X.rW.Λ Γ.W

def Fit (G : GridData Lc sc) (W : G.Weil) (i j : Fin D.R.m) (t μ₀ : T) (Bs : Base D.host.F D.host.E) (a a' : ℕ) : Prop :=
  GlobalTheory.SqStep.BaseFits G W i j t Bs ∧ Bs.IsGood D.sp.cm.sig ∧ EmbCM Bs ∧ (GlobalTheory.SqStep.chs G i j t).IsGood Bs a a' ∧
    (GlobalTheory.SqStep.chs G i j μ₀).IsGood Bs a a' ∧ ∀ w, ((a + a' : ℕ) : ℤ) < Bs.mα w - Bs.mβ w

theorem OverH.eq {c : D.host.E} {A : HSp D} {Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)} {n : ℕ}
    {V V₂ : Spc D.host.F D.host.E n} (h : OverH c A Λ V) (h₂ : OverH c A Λ V₂) : V₂.J = V.J ∧ V₂.L = V.L := by
  obtain ⟨e, hJ, hL⟩ := h
  obtain ⟨e₂, hJ₂, hL₂⟩ := h₂
  exact ⟨hJ₂.trans hJ.symm, Submodule.ext fun y => (hL₂ y).trans (hL y).symm⟩

theorem OverW.eq {WW : HSp D} {Λ : Submodule (𝓞 D.host.E) (Fin WW.rank → D.host.E)} {d : ℕ}
    {Z Z₂ : Spc D.host.F D.host.E d} (h : OverW WW Λ Z) (h₂ : OverW WW Λ Z₂) : Z₂.J = Z.J ∧ Z₂.L = Z.L := by
  obtain ⟨e, hJ, hL⟩ := h
  obtain ⟨e₂, hJ₂, hL₂⟩ := h₂
  exact ⟨hJ₂.trans hJ.symm, Submodule.ext fun y => (hL₂ y).trans (hL y).symm⟩

theorem Fit.down_left {G : GridData Lc sc} {W : G.Weil} {i j : Fin D.R.m} {t μ₀ : T} {Bs : Base D.host.F D.host.E} {b a' : ℕ}
    (h : Fit G W i j t μ₀ Bs (b + 2) a') : Fit G W i j t μ₀ Bs b a' := by
  obtain ⟨h1, h2, h3, c, c₀, hk⟩ := h
  refine ⟨h1, h2, h3, ⟨c.heckeα, c.heckeβ, c.resα, fun x => ?_, c.expα, c.expβ, c.disj, c.sub, c.ram, c.unrα, c.unrβ, c.good⟩,
    ⟨c₀.heckeα, c₀.heckeβ, c₀.resα, fun x => ?_, c₀.expα, c₀.expβ, c₀.disj, c₀.sub, c₀.ram, c₀.unrα, c₀.unrβ, c₀.good⟩, fun w => ?_⟩
  · rw [c.resβ x]; simp [pow_add]
  · rw [c₀.resβ x]; simp [pow_add]
  · have := hk w
    push_cast at this ⊢
    omega

theorem Fit.down_right {G : GridData Lc sc} {W : G.Weil} {i j : Fin D.R.m} {t μ₀ : T} {Bs : Base D.host.F D.host.E} {a b : ℕ}
    (h : Fit G W i j t μ₀ Bs a (b + 2)) : Fit G W i j t μ₀ Bs a b := by
  obtain ⟨h1, h2, h3, c, c₀, hk⟩ := h
  refine ⟨h1, h2, h3, ⟨c.heckeα, c.heckeβ, fun x => ?_, c.resβ, c.expα, c.expβ, c.disj, c.sub, c.ram, c.unrα, c.unrβ, c.good⟩,
    ⟨c₀.heckeα, c₀.heckeβ, fun x => ?_, c₀.resβ, c₀.expα, c₀.expβ, c₀.disj, c₀.sub, c₀.ram, c₀.unrα, c₀.unrβ, c₀.good⟩, fun w => ?_⟩
  · rw [c.resα x]; simp [pow_add]
  · rw [c₀.resα x]; simp [pow_add]
  · have := hk w
    push_cast at this ⊢
    omega

end GlobalTheory.SqStepBig

end
