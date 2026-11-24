module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsWeilDatumAnisotropicKernelPair
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CombAtSingleZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
public import Development.AbelianVarietyTheory.Definitions.Divisors.BplusOfEquivariant
public import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsGLSubmatrix
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsDatOfTower
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ContinuousResTSymm
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CmHostImaginaryGeneratorNeZero
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowBesZeroE
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.SpanPowerMembership.Spaces
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SatakeDualWeyl.Statement
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Classical
public import Init.Core
public import Init.Data.Bool
public import Init.Data.Cast
public import Init.Data.Fin.Lemmas
public import Init.Data.Int.Basic
public import Init.Data.Int.Lemmas
public import Init.Data.Int.Order
public import Init.Data.List.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Nat.Lemmas
public import Init.Data.Zero
public import Init.Omega.Coeffs
public import Init.Omega.Constraint
public import Init.Omega.Int
public import Init.Omega.LinearCombo
public import Init.Prelude
public import Init.PropLemmas
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Nonempty
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import Mathlib.RingTheory.Localization.FractionRing

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR Formalism.IndefR.Links GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.ChiGrid GlobalTheory.Unf
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowChain

open GlobalTheory.FunObj GlobalTheory.RowUnf

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (Wl : G.Weil) (t : T) {M : Vol G}

abbrev pLine (D : D7) : HSp D := Examples₂.posSpace (E := D.host.E) Examples₂.star_isIntegral 1

theorem pLine_gram : (pLine D).gram = antiDiagonalSignGramMatrix 1 (1 : D.host.E) := by
  refine Matrix.ext fun i j => ?_
  have e : ∀ a b : Fin 1, (Examples₂.stdSpace (E := D.host.E) Examples₂.star_isIntegral 1 (fun _ => false) 1 0).gram a b = 1 :=
    fun a b => by rw [Examples₂.stdSpace_gram_apply, Subsingleton.elim a b]; simp [Examples₂.sgn]
  exact (e i j).trans (by simp [antiDiagonalSignGramMatrix]; exact ⟨Fin.val_eq_zero i, Fin.val_eq_zero j⟩)

def topOrth : OrthDec (G.V (.top D.R.m)) (G.V (.grid D.R.m D.R.m)) (pLine D) where
  iA := frameMat _ _ G.sp.topDec.ι
  iB := G.sp.topDec.a
  isoA := frameMat_isom G.sp.topDec
  isoB := G.sp.topDec.gram.trans pLine_gram.symm
  orth := perp_sub' G.sp.topDec id
  rank_add := G.sp.topDec.rank

def topOrthAt {n : ℕ} (h : D.R.m = n) : OrthDec (G.V (.top n)) (G.V (.grid D.R.m D.R.m)) (pLine D) :=
  Eq.rec (motive := fun k _ => OrthDec (G.V (.top k)) (G.V (.grid D.R.m D.R.m)) (pLine D)) (topOrth G) h

def topEmb {n : ℕ} (h : D.R.m = n) : GA D (G.V (.grid D.R.m D.R.m)) → GA D (G.V (.top n)) :=
  Eq.rec (motive := fun k _ => GA D (G.V (.grid D.R.m D.R.m)) → GA D (G.V (.top k))) (stabilizerEmbedding G.sp.topDec) h

def lastTau : Matrix (Fin (GlobalTheory.SeeSaw.Model.nLine D).rank) (Fin (pLine D).rank) D.host.E := Matrix.of fun _ _ => -D.host.xi0

variable {G t}

def lastDat (hM : M.Is t) (j : ℕ) (hj : j + 2 * 0 + 2 = D.R.m) (vN : VolN (besDecAt G j 0 hj)) (g : GA D (G.V (.grid D.R.m j)))
    (Φ₁ : WO (G.V (.grid D.R.m j)) (G.V (.grid D.R.m (j + 1))) → ℂ)
    (Φ₂ : WO (G.V (.grid D.R.m (j + 1))) (G.V (.grid D.R.m D.R.m)) → ℂ) :
    WO (G.V (.top j)) (G.V (.top (j + 1))) → WO (G.V (.top (j + 1))) (G.V (.top (j + 1 + 1))) → ℂ :=
  GlobalTheory.FinPl.lastBi (besAt G hM j 0 hj vN).o (topOrthAt G (show D.R.m = j + 1 + 1 by omega)) lastTau
    (flatBF (lastAt G Wl t hM j hj vN).s ((lastAt G Wl t hM j hj vN).s.om (g, 1) Φ₁))
    (fun w => Φ₂ ((rowJac G (j + 1) (by omega) 0 (by omega)).ext0 _ w))

end GlobalTheory.RowChain

namespace GlobalTheory.RowChain

open GlobalTheory.FunObj GlobalTheory.RowUnf

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (Wl : G.Weil) (t : T) {M : Vol G}

theorem topOrth_emb (h : GA D (G.V (.grid D.R.m D.R.m))) : (topOrth G).emb (h, 1) = stabilizerEmbedding G.sp.topDec h :=
  (embRel_iff G.sp.topDec h _).1 ((topOrth G).embRel_left G.sp.topDec.ι rfl h)

variable {G t}

noncomputable def colPer (hM : M.Is t) : (σ j : ℕ) → (hj : j + 2 * σ + 2 = D.R.m) → (vN : VolN (besDecAt G j σ hj)) →
    (chainFrom G Wl t hM σ j hj vN).Data → Fn G (.grid D.R.m D.R.m) → (GA D (G.V (.top j)) → ℂ) →
    GA D (G.V (.grid D.R.m j)) → (chainFrom G Wl t hM σ j hj vN).Var → ℂ
  | 0, j, hj, vN, Φ, F, φ, g, _ =>
    ∫ h' in M.fd (.grid D.R.m D.R.m), F h' * GlobalTheory.SeeSaw.biLift (Wl.om (.top t j)) (Wl.om (.top t (j + 1)))
      (volAt hM (.top j) (by show j ≤ D.R.m; omega)) (volAt hM (.top (j + 1)) (by show j + 1 ≤ D.R.m; omega)) φ
      (lastDat Wl hM j hj vN g Φ.1 Φ.2) (topEmb G (show D.R.m = j + 1 + 1 by omega) h') ∂M.ν (.grid D.R.m D.R.m)
  | σ + 1, j, hj, vN, Φ, F, φ, g, h =>
    colPer hM σ (j + 1 + 1) (by omega) (GlobalTheory.Unf.Inhab.nonempty_volN _).some Φ.2.2 F
      (GlobalTheory.SeeSaw.biLift (Wl.om (.top t j)) (Wl.om (.top t (j + 1)))
        (volAt hM (.top j) (by show j ≤ D.R.m; omega)) (volAt hM (.top (j + 1)) (by show j + 1 ≤ D.R.m; omega)) φ
        (contr (linkAt hM j σ hj vN (by omega) (GlobalTheory.Unf.Inhab.nonempty_volN _).some) (G.V (.top (j + 1)))
          ((GlobalTheory.Unf.Inhab.nonempty_volM D _ _).some)
          (flatBF (B := besAt G hM j (σ + 1) hj vN) (J := jacAt G hM (j + 1) (σ + 1) (by omega)) (stepAt G Wl t hM j (by omega) (besDecAt G j (σ + 1) hj) (rowJac G (j + 1) (by omega) (σ + 1) (by omega)))
            ((stepAt G Wl t hM j (by omega) (besDecAt G j (σ + 1) hj) (rowJac G (j + 1) (by omega) (σ + 1) (by omega))).om
              (g, h.1) Φ.1))
          (flatFB (J := jacAt G hM (j + 1) (σ + 1) (by omega))
            (B := besAt G hM (j + 1 + 1) σ (by omega) (GlobalTheory.Unf.Inhab.nonempty_volN _).some) (stepAt G Wl t hM (j + 1) (by omega) (rowJac G (j + 1) (by omega) (σ + 1) (by omega))
              (besDecAt G (j + 1 + 1) σ (by omega)))
            ((stepAt G Wl t hM (j + 1) (by omega) (rowJac G (j + 1) (by omega) (σ + 1) (by omega))
              (besDecAt G (j + 1 + 1) σ (by omega))).om (h.1, h.2.1) Φ.2.1))))
      h.2.1 h.2.2

end GlobalTheory.RowChain
