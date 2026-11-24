module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacesToAdeles
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.AllPositions
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalModelRestrictedToLineSlice
public import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ContinuousResTSymm
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaFunctionProductsSlicesOrthogonalDecompositi
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Basic
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Notation.Prod
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Valuation.ValuativeRel.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Instances.Matrix

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SliceLeft

open GlobalTheory.MixModel.OrthDec GlobalTheory.LocFlat.CFac GlobalTheory.SliceLine

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k)
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']

def boxL (c : SB (Matrix n Unit k)) : SB (Matrix n n' k) →ₗ[ℂ] SB (Matrix n (n' ⊕ Unit) k) where
  toFun Ξ := box Ξ c
  map_add' Ξ Ξ' := Subtype.ext (funext fun x => by simp [box, splitCols, add_mul])
  map_smul' a Ξ := Subtype.ext (funext fun x => by simp [box, splitCols]; ring)

theorem heis_slice_left {S A L T : HSp D} (d : OrthDec S A L) (ψ : AddChar (AF D.host.F) ℂ) (f : WO S T → ℂ)
    (u u' : WO A T) (w : WO L T) :
    heisO ψ S T ((d.resS T).symm (u', 0)) f ((d.resS T).symm (u, w)) =
      heisO ψ A T u' (fun u => f ((d.resS T).symm (u, w))) u := by
  simp only [heisO]
  rw [d.symplOH_resS, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, GlobalTheory.MixModel.symplOH_zero_right, add_zero,
    ← map_add, Prod.mk_add_mk, add_zero]

theorem isHalf_slice_left {S A L T : HSp D} (d : OrthDec S A L) {a : AE D} {y : WO A T} (hy : IsHalf a y) :
    IsHalf a ((d.resS T).symm (y, 0)) := by
  intro i j
  rw [resS_symm_apply, Matrix.zero_mul, add_zero, Matrix.mul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [← mul_assoc, hy i l]

end GlobalTheory.SliceLeft

namespace GlobalTheory.SliceLeft

open GlobalTheory.MixModel.OrthDec GlobalTheory.LocFlat.CFac GlobalTheory.SliceLine

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k)
variable {ρ : ℕ} {B : BesLev D ρ} {s : k} {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
  {FA : Frame k B.A.rank n'} {F₀ : Frame k B.V₀.rank (n' ⊕ Unit)} {FL : Frame k B.L.rank Unit}

theorem up_fromCols_left (h : p.IsCoreFrame B s FA F₀) (hL : ∀ r, FL.β r () = s * p.pr (B.ζ r)) {S : HSp D}
    (FS : Frame k S.rank n) (x : Matrix n n' k) :
    p.up F₀ FS (fromCols x 0) = (B.o.resS S).symm (p.up FA FS x, 0) := by
  have k1 : x * FA.γ * B.o.qA.map (p.π.comp (incA D)) * F₀.β = fromCols x (0 : Matrix n Unit k) := by
    rw [beta_eq p h hL, Matrix.mul_fromCols]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (B.o.qA.map _) (B.o.iA.map _), ← Matrix.map_mul, B.o.qA_iA,
      ← Matrix.mul_assoc (B.o.qA.map _) (B.o.iB.map _), ← Matrix.map_mul, B.o.qA_iB]
    simp [FA.γβ]
  have k2 : fromCols x (0 : Matrix n Unit k) * F₀.γ = x * FA.γ * B.o.qA.map (p.π.comp (incA D)) := by
    rw [← k1, Matrix.mul_assoc (x * FA.γ * B.o.qA.map (p.π.comp (incA D))) F₀.β F₀.γ, F₀.βγ, Matrix.mul_one]
  rw [resS_symm_apply, Matrix.zero_mul, add_zero]
  unfold Place.up
  rw [pA, map_ι_mul, rat_map_π]
  congr 1
  rw [Matrix.mul_assoc FS.β (fromCols x 0) F₀.γ, k2]
  simp only [Matrix.mul_assoc]

theorem resS_up_fst (h : p.IsCoreFrame B s FA F₀) (hL : ∀ r, FL.β r () = s * p.pr (B.ζ r)) {S : HSp D}
    (FS : Frame k S.rank n) (t : Matrix n (n' ⊕ Unit) k) :
    (B.o.resS S (p.up F₀ FS t)).1 = p.up FA FS t.toCols₁ := by
  have k1 : t * F₀.γ * B.o.iA.map (p.π.comp (incA D)) * FA.β = t.toCols₁ := by
    calc t * F₀.γ * B.o.iA.map (p.π.comp (incA D)) * FA.β
        = ((t * F₀.γ) * fromCols (B.o.iA.map (p.π.comp (incA D)) * FA.β)
            (B.o.iB.map (p.π.comp (incA D)) * FL.β)).toCols₁ := by
          rw [Matrix.mul_fromCols, toCols₁_fromCols, Matrix.mul_assoc (t * F₀.γ)]
      _ = ((t * F₀.γ) * F₀.β).toCols₁ := by rw [← beta_eq p h hL]
      _ = t.toCols₁ := by rw [Matrix.mul_assoc, F₀.γβ, Matrix.mul_one]
  have k2 : t * F₀.γ * B.o.iA.map (p.π.comp (incA D)) = t.toCols₁ * FA.γ := by
    rw [← k1, Matrix.mul_assoc (t * F₀.γ * B.o.iA.map (p.π.comp (incA D))) FA.β FA.γ, FA.βγ, Matrix.mul_one]
  rw [resS_apply]
  dsimp only
  unfold Place.up
  rw [jA, map_ι_mul, rat_map_π]
  simp only [Matrix.mul_assoc] at k2 ⊢
  rw [k2]

end GlobalTheory.SliceLeft

namespace GlobalTheory.SliceLeft

open GlobalTheory.MixModel.OrthDec GlobalTheory.LocFlat.CFac GlobalTheory.SliceLine

theorem toCols_add_left {k n n' : Type} [Field k] (t : Matrix n (n' ⊕ Unit) k) (x : Matrix n n' k) :
    (t + fromCols x (0 : Matrix n Unit k)).toCols₁ = t.toCols₁ + x ∧
      (t + fromCols x (0 : Matrix n Unit k)).toCols₂ = t.toCols₂ :=
  ⟨by ext i j; simp, by ext i j; simp⟩

theorem slice_left : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesLev D ρ) (S : HSp D) (s : k) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (FA : Frame k B.A.rank n') (F₀ : Frame k B.V₀.rank (n' ⊕ Unit)) (FS : Frame k S.rank n), p.IsCoreFrame B s FA F₀ → ∀ T₀, p.IsModel ψ F₀ FS T₀ → ∀ (c : SB (Matrix n Unit k)) (w₀ : WO B.L S), ∃ T', p.IsModel ψ FA FS T' ∧ ∀ (Ξ : SB (Matrix n n' k)) (Ψ : SB (Matrix n (n' ⊕ Unit) k)), (∀ x, Ψ.1 x = Ξ.1 x.toCols₁ * c.1 (Matrix.of fun r _ => x r (Sum.inr ()))) → ∀ u, T' Ξ u = T₀ Ψ ((B.o.resS S).symm (u, w₀)) := by
  intro D k _ _ _ _ p ψ ρ B S s n n' _ _ _ _ FA F₀ FS h T₀ hT c w₀
  obtain ⟨FL, hFL, -⟩ := slice_line D k p ψ ρ B S s n n' FA F₀ FS h T₀ hT
  let T' : SB (Matrix n n' k) →ₗ[ℂ] (WO B.A S → ℂ) :=
    (LinearMap.funLeft ℂ ℂ (fun u : WO B.A S => (B.o.resS S).symm (u, w₀))).comp (T₀.comp (boxL c))
  have hT' : ∀ Ξ u, T' Ξ u = T₀ (box Ξ c) ((B.o.resS S).symm (u, w₀)) := fun _ _ => rfl
  refine ⟨T', ⟨fun Φ => ?_, fun x Φ Φ' hΦ => ?_, fun y hy Φ Φ' hΦ => ?_⟩, fun Ξ Ψ hΨ u => ?_⟩
  · exact GlobalTheory.BoxSlice.isThetaFunO_slice_left B.o (hT.theta (box Φ c)) w₀
  · have e := hT.trans (fromCols x 0) (box Φ c) (box Φ' c) (fun t => by
      rw [box_apply, box_apply, hΦ, (toCols_add_left t x).1, (toCols_add_left t x).2])
    funext u
    rw [hT', e, up_fromCols_left p h hFL, heis_slice_left]
    rfl
  · have e := hT.modul ((B.o.resS S).symm (y, 0)) (isHalf_slice_left B.o hy) (box Φ c) (box Φ' c) (fun t => by
      simp only [box_apply, hΦ, B.o.symplO_resS, AddEquiv.apply_symm_apply, resS_up_fst p h hFL, symplO_zero_right',
        add_zero]
      ring)
    funext u
    rw [hT', e, heis_slice_left]
    rfl
  · have e : Ψ = box Ξ c := Subtype.ext (funext fun x => by rw [hΨ, box_apply]; rfl)
    rw [hT', e]

end GlobalTheory.SliceLeft
