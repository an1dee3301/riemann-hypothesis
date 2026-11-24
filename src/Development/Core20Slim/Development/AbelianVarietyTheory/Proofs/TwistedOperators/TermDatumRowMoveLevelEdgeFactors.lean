module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairPtsClasses
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairPtsEqSum
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.MovFn
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlippedLocalTotalTensorFixedByInnerVertexLevelStatement
public import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum
public import Development.AbelianVarietyTheory.Definitions.Divisors.InvVolConjLevelOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneCosetOfIsTensor
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Fin.Basic
public import Init.Data.Int.Basic
public import Init.Data.Int.Lemmas
public import Init.Data.Int.Order
public import Init.Data.List.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Nat.Coprime
public import Init.Data.Nat.Gcd
public import Init.Data.Nat.Lemmas
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Ext
public import Init.Omega.Coeffs
public import Init.Omega.Constraint
public import Init.Omega.Int
public import Init.Omega.LinearCombo
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Notation.Pi.Basic
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.Kleene
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.UnitBall
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Logic.Function.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.OuterMeasure.AE
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Filter.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.RingTheory.Valuation.ValuativeRel.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.RowVertexInv GlobalTheory.SplitFlip
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section
namespace GlobalTheory.FlatRowMove

variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem fill_move (G : Grid k) (hs : 1 ≤ G.s) {j : ℕ} (hj : j + 1 < G.m)
    (κ : GL (Fin (G.rank (j + 1, G.m))) k) (x : ColArgs G) (y : RowArgs G) (e : Vars G) :
    fill hs x (Function.update (Function.update y j (y j * κ.val)) (j + 1) (κ⁻¹.val * y (j + 1))) e =
      G.moveArgs .one (Pi.mulSingle (j + 1, G.m) κ) (fill hs x y e) := by
  funext b
  cases b with
  | theta i l =>
    by_cases hi : i = G.m
    · subst hi
      have h1 : (Pi.mulSingle (j + 1, G.m) κ : G.VertexGroup) (G.m, l) = 1 :=
        Pi.mulSingle_eq_of_ne (by intro h; simp [Prod.ext_iff] at h; omega) _
      have h2 : (Pi.mulSingle (j + 1, G.m) κ : G.VertexGroup) (G.m, l + 1) = 1 :=
        Pi.mulSingle_eq_of_ne (by intro h; simp [Prod.ext_iff] at h; omega) _
      simp only [Grid.moveArgs, Edge.src, Edge.tgt, h1, h2, map_one, inv_one, Units.val_one,
        Matrix.one_mul, Matrix.mul_one, fill_theta]
    · simp [fill, Grid.moveArgs, hi]
  | ex i l =>
    by_cases hl : l = G.m
    · subst hl
      simp only [Grid.moveArgs, Edge.src, Edge.tgt, fill_ex]
      by_cases hij : i = j
      · subst hij
        have h1 : (Pi.mulSingle (i + 1, G.m) κ : G.VertexGroup) (i, G.m) = 1 :=
          Pi.mulSingle_eq_of_ne (by intro h; simp [Prod.ext_iff] at h) _
        rw [h1, Pi.mulSingle_eq_same, Function.update_of_ne (by omega), Function.update_self,
          map_one, Units.val_one, Matrix.mul_one, Assignment.read, invT_inv_val, Matrix.transpose_mul]
      · by_cases hij' : i = j + 1
        · subst hij'
          have h1 : (Pi.mulSingle (j + 1, G.m) κ : G.VertexGroup) (j + 1 + 1, G.m) = 1 :=
            Pi.mulSingle_eq_of_ne (by intro h; simp [Prod.ext_iff] at h) _
          rw [h1, Pi.mulSingle_eq_same, Function.update_self, map_one, inv_one, Units.val_one,
            Matrix.one_mul, Assignment.read, invT_val, Matrix.transpose_mul]
        · have h1 : (Pi.mulSingle (j + 1, G.m) κ : G.VertexGroup) (i, G.m) = 1 :=
            Pi.mulSingle_eq_of_ne (by intro h; simp [Prod.ext_iff] at h; omega) _
          have h2 : (Pi.mulSingle (j + 1, G.m) κ : G.VertexGroup) (i + 1, G.m) = 1 :=
            Pi.mulSingle_eq_of_ne (by intro h; simp [Prod.ext_iff] at h; omega) _
          rw [h1, h2, Function.update_of_ne hij', Function.update_of_ne hij]
          simp only [map_one, inv_one, Units.val_one, Matrix.one_mul, Matrix.mul_one]
    · simp [fill, Grid.moveArgs, hl]

theorem mulSingle_comm (G : Grid k) {X : ℕ × ℕ} (κ : GL (Fin (G.rank X)) k) (g : G.VertexGroup) (hg : g X = 1) :
    Pi.mulSingle X κ * g = g * Pi.mulSingle X κ := by
  funext Y
  by_cases hY : Y = X
  · subst hY; simp [hg]
  · simp [Pi.mulSingle_eq_of_ne hY]

variable [MeasurableSpace k] [BorelSpace k]

theorem flat_move (G : Grid k) (hs : 1 ≤ G.s) (ψ : AddChar k Circle) (ν : Measure k) (keep : Bool)
    (g : G.VertexGroup) (T : G.Args → ℂ) {j : ℕ} (hj : j + 1 < G.m) (κ : GL (Fin (G.rank (j + 1, G.m))) k)
    (hg : g (j + 1, G.m) = 1)
    (hT : G.pathAct .one (oppositePath G.m) (Pi.mulSingle (j + 1, G.m) κ) T = T) (x : ColArgs G) (y : RowArgs G) :
    ((oppositePath G.m).map (G.edgeFactor .one (Pi.mulSingle (j + 1, G.m) κ))).prod *
      flatTensor hs ψ ν (GlobalTheory.FunObj.moved G keep g T) x
        (Function.update (Function.update y j (y j * κ.val)) (j + 1) (κ⁻¹.val * y (j + 1))) =
      flatTensor hs ψ ν (GlobalTheory.FunObj.moved G keep g T) x y := by
  have hF : ∀ z, ((oppositePath G.m).map (G.edgeFactor .one (Pi.mulSingle (j + 1, G.m) κ))).prod *
      GlobalTheory.FunObj.moved G keep g T (G.moveArgs .one (Pi.mulSingle (j + 1, G.m) κ) z) = GlobalTheory.FunObj.moved G keep g T z := by
    intro z
    have h := congrFun (congrArg (G.pathAct .one (oppositePath G.m) g) hT) z
    rw [← Grid.pathAct_mul, ← mulSingle_comm G κ g hg, Grid.pathAct_mul] at h
    simp only [GlobalTheory.FunObj.moved]
    rw [← h]
    simp only [Grid.pathAct]
    ring
  simp only [flatTensor, flatIntegrand, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun e => ?_)
  simp only [fill_move G hs hj κ x y e, ← mul_assoc, hF]

theorem term_datum_move : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T} {Φ : G.Datum} (β : CosFam G t) {μ₀ : T}, L.Is μ₀ → (Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q)) → (∀ P ∈ L.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) → t ∈ U → ∀ (w : locPl G t) (j : ℕ), j + 1 < D.R.m →
    ∀ (κ : GL (Fin ((locGrid G t w.1).rank (j + 1, (locGrid G t w.1).m))) (Kw w.1)), κ ∈ givenLevel G t w.1 (j + 1, D.R.m) →
    ∀ (x : ColArgs (locGrid G t w.1)) (y : RowArgs (locGrid G t w.1)),
    ((oppositePath D.R.m).map ((locGrid G t w.1).edgeFactor .one (Pi.mulSingle (j + 1, D.R.m) κ))).prod *
      (S.term t Φ β w).datum x (Function.update (Function.update y j (y j * κ.val)) (j + 1) (κ⁻¹.val * y (j + 1))) =
    (S.term t Φ β w).datum x y := by
  intro D T L sc G W U S t Φ β μ₀ hL hde hc ht w j hj κ hκ x y
  have hT := GlobalTheory.T.flippedLocalTotalTensor_fixed_by_innerVertex_level S Φ ht hL hde hc w.1 w.2 j hj κ hκ
  have hg : ((repsAt G t w.1).elt (β w)) (j + 1, D.R.m) = 1 := by
    simp only [Reps.elt, onColumn]
    exact dif_neg (by show j + 1 ≠ D.R.m; omega)
  exact flat_move (locGrid G t w.1) _ _ _ _ _ _ hj κ hg hT x y

end GlobalTheory.FlatRowMove
