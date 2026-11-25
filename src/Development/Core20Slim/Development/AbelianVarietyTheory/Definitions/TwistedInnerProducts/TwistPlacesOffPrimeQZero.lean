module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CmQuadraticFormEqAlternatingForm

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.Mem GlobalTheory.Mem.Top

namespace GlobalTheory.RowEx

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw










section Clauses

variable {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc} {W : G.Weil} {K : Type} [Field K]
  (σ : K →+* ℂ) (S : GridChoice W Set.univ)









end Clauses








section Agree

variable {X X' : Stages} {T T' : Type} {L : LevCh X.toD7 T} {L' : LevCh X'.toD7 T'}

structure LAgree (L : LevCh X.toD7 T) (L' : LevCh X'.toD7 T') (μ₀ : T) (μ₀' : T') (ι : T' → T) : Prop where

  pre : X'.B.toPre = X.B.toPre

  is : L.Is μ₀

  is' : L'.Is μ₀'

  C : ∃ (f : Fr X.B.toPre) (f' : Fr X'.B.toPre), HEq f' f ∧ L.C = Fr.at X f ∧ L'.C = Fr.at X' f'

  base : ι μ₀' = μ₀

  xi : ∀ t, HEq (L'.xiH t) (L.xiH (ι t))

  Q : ∀ t, HEq (L'.Q t) (L.Q (ι t))

  β : L.βX = 1 ∧ L'.βX = 1

variable {sc : GlobalTheory.ChiGrid.Consts}

structure GAgree (G : GridData L sc) (G' : GridData L' sc) : Prop where

  v0 : HEq G'.pl.v0 G.pl.v0

  w : HEq G'.pl.w G.pl.w

  chiH : HEq G'.ch.chiH G.ch.chiH

  chi : HEq G'.ch.chi G.ch.chi

  grid : ∀ i j, HEq (G'.V (.grid (i + 1) j)) (G.V (.grid (i + 1) j)) ∧ HEq (G'.Λ (.grid (i + 1) j)) (G.Λ (.grid (i + 1) j))

  top : ∀ j, HEq (G'.V (.top j)) (G.V (.top j)) ∧ HEq (G'.Λ (.top j)) (G.Λ (.top j))

  rowDec : ∀ j h h', HEq (G'.rowDec j h').ι (G.rowDec j h).ι ∧ HEq (G'.rowDec j h').a (G.rowDec j h).a

  topDec : HEq G'.sp.topDec.ι G.sp.topDec.ι ∧ HEq G'.sp.topDec.a G.sp.topDec.a

variable {G : GridData L sc} {G' : GridData L' sc}

def mapPair (ι : T' → T) : Pair T' → Pair T
  | .chi i j => .chi i j
  | .mu t i j => .mu (ι t) i j
  | .core i => .core i
  | .top t j => .top (ι t) j

structure WAgree (W : G.Weil) (W' : G'.Weil) (ι : T' → T) : Prop where

  ψ : HEq W'.ψ W.ψ

  θ : HEq W'.θ W.θ

  cart : ∀ Y, DefNode X'.toD7.R.m Y → HEq (W'.cart Y) (W.cart Y)

  om : ∀ p, DefPair X'.toD7.R.m p → HEq (W'.om p) (W.om (mapPair ι p))

variable {W : G.Weil} {W' : G'.Weil}

structure SAgree (S : GridChoice W Set.univ) (S' : GridChoice W' Set.univ) (ι : T' → T) : Prop where

  β : ∀ i j, HEq (S'.B.β (i + 1) j) (S.B.β (i + 1) j)

  βp : ∀ j, HEq (S'.βp j) (S.βp j)

  fr : ∀ Y, DefNode X'.toD7.R.m Y → HEq (S'.N.fr Y) (S.N.fr Y) ∧ HEq (S'.N.u Y).1 (S.N.u Y).1

  δ : S'.Z.δ = S.Z.δ

  vac : ∀ p, DefPair X'.toD7.R.m p → HEq (S'.Z.vac p) (S.Z.vac (mapPair ι p)) ∧ S'.Z.c0 p = S.Z.c0 (mapPair ι p)

  PA : HEq S'.PA S.PA

structure Agree (S : GridChoice W Set.univ) (S' : GridChoice W' Set.univ) (μ₀ : T) (μ₀' : T') (ι : T' → T) : Prop where

  l : LAgree L L' μ₀ μ₀' ι

  g : GAgree G G'

  w : WAgree W W' ι

  s : SAgree S S' ι


end Agree

















end GlobalTheory.RowEx

end
