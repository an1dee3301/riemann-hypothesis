module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairPtsClasses
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairPtsEqSum
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.MovFn
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnderMemAndPlaceAboveEqOfMem
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationLeOneOfMem
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitThetaGridIsAdmissibleFlipTensorStatement
public import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.InvVolConjLevelOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemSum
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Int.Lemmas
public import Init.Data.Int.Order
public import Init.Data.List.Basic
public import Init.Data.List.Lemmas
public import Init.Data.List.Nat.Range
public import Init.Data.List.Range
public import Init.Data.Nat.Basic
public import Init.Data.Nat.Coprime
public import Init.Data.Nat.Gcd
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Omega.Coeffs
public import Init.Omega.Constraint
public import Init.Omega.Int
public import Init.Omega.LinearCombo
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Basic
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Notation.Pi.Basic
public import Mathlib.Algebra.Order.Kleene
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.Logic.Function.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.RingTheory.Valuation.ValuativeRel.Basic
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.RowVertexInv GlobalTheory.SplitFlip
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.FlipVertexInv

open GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.TopLevelInv

theorem flips_isAdmissible {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] {Γ : Grid k} {ψ : AddChar k Circle} {ϖ : kˣ}
    {e : ℕ} (hϖ : IsUnif ϖ) (hψ : HasConductor ψ 1) (he : 1 ≤ e) :
    ∀ (l : List (ℕ × ℕ)) (St : Γ.PiLocalization₂), (∀ x ∈ l, CondLE ϖ e (Γ.nu x.1 x.2)) → CanFlip St.path l →
      (∀ X, IsOpen (St.level X : Set (GL (Fin (Γ.rank X)) k)) ∧ St.level X ≤ KO k _) → St.IsAdmissible .one ϖ e →
      (St.flips .one ψ ϖ e l).IsAdmissible .one ϖ e := by
  intro l
  induction l with
  | nil => intro St _ _ _ hT; exact hT
  | cons x l ih =>
    intro St hν hc hJ hT
    obtain _ | ⟨hp, hc'⟩ := hc
    refine ih (St.flip .one ψ ϖ e x) (fun y hy => hν y (List.mem_cons_of_mem _ hy)) hc' (fun X => ?_)
      (GlobalTheory.T.splitThetaGrid_isAdmissible_flipTensor ψ ϖ e hϖ hψ he St x (hν x List.mem_cons_self) hp hJ hT)
    change IsOpen (Γ.flipLevel x.1 x.2 St.level X : Set (GL (Fin (Γ.rank X)) k)) ∧ Γ.flipLevel x.1 x.2 St.level X ≤ _
    by_cases hX : X = (x.1 + 1, x.2 + 1)
    · subst hX; simp only [Grid.flipLevel, Function.update_self]; exact ⟨isOpen_KO, le_rfl⟩
    · simp only [Grid.flipLevel, Function.update_of_ne hX]; exact hJ X

theorem mem_flipOrder {m : ℕ} {x : ℕ × ℕ} (hx : x ∈ flipOrder m) : x.1 < m ∧ x.2 < m := by
  simp only [flipOrder, List.mem_flatMap, List.mem_map, List.mem_range] at hx
  obtain ⟨i, hi, j, hj, rfl⟩ := hx
  exact ⟨hi, hj⟩

theorem mem_inner_opposite {m j : ℕ} (hj : j + 1 < m) : (j + 1, m) ∈ innerVertices (oppositePath m) := by
  obtain ⟨n, hn⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  have h : Edge.ex (j + 1) m ∈ (oppositePath m).tail := by
    rw [oppositePath, hn, List.range_succ_eq_map, List.map_cons, List.cons_append, List.tail_cons]
    exact List.mem_append_left _ (List.mem_map.2 ⟨j + 1, List.mem_map.2 ⟨j, List.mem_range.2 (by omega), rfl⟩, rfl⟩)
  exact List.mem_map.2 ⟨_, h, rfl⟩

theorem main : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T} (Φ : G.Datum), t ∈ U → ∀ {μ₀ : T}, L.Is μ₀ → (Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q)) → (∀ P ∈ L.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) → ∀ (w : Pl D.host.E), w ∈ locPl G t → ∀ (j : ℕ), j + 1 < D.R.m →
    ∀ (κ : GL (Fin ((locGrid G t w).rank (j + 1, D.R.m))) (Kw w)), κ ∈ givenLevel G t w (j + 1, D.R.m) →
    (locGrid G t w).pathAct .one (oppositePath D.R.m) (Pi.mulSingle (j + 1, D.R.m) κ) (Tflip W S.B t Φ w) =
      Tflip W S.B t Φ w := by
  intro D T L sc G W U S t Φ _ μ₀ hL hde hc w hw j hj κ hκ
  have hg := (Good.locGrid_isGood hL G W t hde hc).1 w hw
  have hm : 0 < D.R.m := by omega
  have h00 := hg.square 0 hm 0 hm
  have hν : ∀ x ∈ flipOrder D.R.m, CondLE (unifAt w) (depthAt G w) ((locGrid G t w).nu x.1 x.2) := by
    intro x hx
    obtain ⟨hi, hj⟩ := mem_flipOrder hx
    rw [← Grid.alpha_div_beta]
    exact (hg.square x.1 hi x.2 hj).condν
  have hfl : (flipStage t w S.B W Φ).IsAdmissible .one (unifAt w) (depthAt G w) :=
    flips_isAdmissible h00.unif h00.cond h00.one_le (flipOrder D.R.m) (givenStage t w S.B Φ) hν (canFlip_flipOrder _).1
      (fun X => GivenAdm.givenLevel_open hL hw X) (GivenAdm.givenStage_isAdmissible hL S.B t Φ hw)
  obtain ⟨hp, hl⟩ := flipStage_path_level t w S.B W Φ
  have := hfl.invariant (j + 1, D.R.m) (hp ▸ mem_inner_opposite hj) κ (hl ▸ hκ)
  rw [hp] at this
  exact this

end GlobalTheory.FlipVertexInv
