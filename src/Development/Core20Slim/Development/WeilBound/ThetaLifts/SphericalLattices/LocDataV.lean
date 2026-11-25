module

public import Development.Core20Slim.Development.WeilBound.ThetaLifts.SphericalLattices.HoweDefs
public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceLocalFieldDataExistsStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceUnimodularHermitianFrameCoordinatesStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalSchroedingerFamilyAtPlaceStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalWeilOperatorsSupportedAtPlaceStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalWeilOperatorNormalisesSchroedingerOperatorStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceLatticeVacuumFixedAndUniqueStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceBothStabilisersFixVacuumStatement
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
public import Formalism.SatakeDualWeyl.Statement
public import Formalism.SatakeDualWeyl.StatementF
public import Formalism.SatakeDualWeyl.StatementG
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Core
public import Init.Data.Function
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Invertible.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Group.WithOne.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.GroupWithZero.WithZero
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Order.Kleene
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.BoundedOrder.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Trace.Defs
public import Mathlib.RingTheory.Valuation.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.Topology.Algebra.Valued.ValuationTopology
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.UniformSpace.Cauchy
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

namespace PositivityTheory.Sph

open scoped Matrix TensorProduct
open NumberField IsDedekindDomain Topology GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

theorem locDataV {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {B : Base F E} {a a' : ℕ} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W}
    (hT : IsTriple B G X om om') {v : Pl F} {w : HeightOneSpectrum (𝓞 E)} (hin : Formalism.UG.IsInertAt F E v w)
    (hvT : v ∉ X.T) : LocData G.M om v := by
  obtain ⟨L, iF, iC, iVl, iCS, ϖ, σL, q, δ, ψL, ι, hunr, hodd, hδ, hpi, hpn, hinj, him, hmul, hσ, hint, hψ⟩ :=
    GlobalTheory.T.inert_place_local_field_data_exists F E σ B hT.base v w hin
  obtain ⟨JS, JT, Xm, iV, iW, hiS, hiT, hhS, hhT, hψ2, himX, hlat1, hlat2, hact, hUV, hUW, hKV, hKW⟩ :=
    GlobalTheory.T.inertPlace_unimodular_hermitianFrame_coordinates F E σ B a a' G hT.base hT.geo v w hin L ϖ σL q δ ψL ι hunr hodd hδ hinj him hmul hσ hint hψ
  obtain ⟨ρ, hρ0, hρmul, hρA, hρspan⟩ := GlobalTheory.T.exists_local_schroedinger_family_at_place F v B.ψ hT.base.std (hT.base.inert v w hin).2.2 G.M.co
    (Matrix (Fin (a + a')) (Fin a) L) Xm
    (fun x y => ψL ((GlobalTheory.Hk3.locH σL δ JS JT x y + σL (GlobalTheory.Hk3.locH σL δ JS JT x y)) / 2)) himX hψ2
  let j := iV.prodMap iW
  obtain ⟨ω, hω⟩ := GlobalTheory.T.exists_localWeilOperators_supportedAtPlace F E σ B a a' G X om om' hT v _ j (fun g => ⟨hUV g.1, hUW g.2⟩)
  have hnorm := GlobalTheory.T.localWeilOperator_normalises_schroedingerOperator F E σ B a a' G X om om' hT v _ Xm (fun y => (himX _).2 ⟨y, rfl⟩) ρ hρA _ j ω hω
    (fun g x => ((g.2 : GL (Fin (a + a')) L) : Matrix (Fin (a + a')) (Fin (a + a')) L) * x *
      (((g.1 : GL (Fin a) L)⁻¹ : GL (Fin a) L) : Matrix (Fin a) (Fin a) L)) (fun g x => hact g.1 g.2 x)
  obtain ⟨hvac, huniq⟩ := GlobalTheory.T.inertPlace_latticeVacuum_fixed_and_unique F E σ B a a' G X om om' hT v w hin hvT _ Xm
    (fun u => ∀ i j, u i j ∈ Formalism.UG.intL L) hlat1 hlat2 ρ hρA
  have hfix := GlobalTheory.T.inert_place_both_stabilisers_fix_vacuum F E σ B a a' G X om om' hT v w hin hvT
  have hvSB := (hT.geo.hM.vac v).1
  have hv0 := (hT.geo.hM.vac v).2.1
  let s : SB (Fin a × Fin (a + a') → Fv F v) := ⟨G.M.vac v, hvSB⟩
  have hs0 : s ≠ 0 := fun h => hv0 (congrArg Subtype.val h)
  have hspan := hρspan s hs0
  have hωs : ∀ (g : Formalism.UG.UJ σL (JS : Matrix (Fin a) (Fin a) L)) (h : Formalism.UG.UJ σL (JT : Matrix (Fin (a + a')) (Fin (a + a')) L)),
      (g : GL (Fin a) L) ∈ Formalism.UG.GLint (Fin a) (Formalism.UG.intL L) →
      (h : GL (Fin (a + a')) L) ∈ Formalism.UG.GLint (Fin (a + a')) (Formalism.UG.intL L) → ω (g, h) s = s := by
    intro g h hg hh
    exact Subtype.ext ((hω (g, h) s (G.M.vac v)).1 (hfix _ (hKV g hg) _ (hKW h hh))).symm
  refine ⟨L, iF, iC, iVl, iCS, ϖ, σL, q, δ, JS, JT, ψL, ρ, ω, iV, iW, s, ?_, hs0, fun u hu => hvac s rfl u hu, hspan, rfl,
    hUV, hUW, hKV, hKW, fun g h m φ₁ _ => (hω (g, h) m φ₁).trans eq_comm⟩
  exact
    { unr := hunr
      odd := hodd
      intS := hiS
      intT := hiT
      hermS := hhS
      hermT := hhT
      delta := hδ
      psi_int := hpi
      psi_ne := hpn
      rho_zero := hρ0
      rho_mul := hρmul
      span := by
        rw [eq_top_iff, ← hspan]
        refine Submodule.span_mono ?_
        rintro _ ⟨x, rfl⟩
        exact ⟨x, s, fun u hu => hvac s rfl u hu, rfl⟩
      norm := fun g h x => hnorm (g, h) x
      fix := by
        intro g h hg hh s' hs'
        obtain ⟨c, hc⟩ := huniq s' hs'
        have e : s' = c • s := Subtype.ext hc
        rw [e, map_smul, hωs g h hg hh] }

end PositivityTheory.Sph

end
