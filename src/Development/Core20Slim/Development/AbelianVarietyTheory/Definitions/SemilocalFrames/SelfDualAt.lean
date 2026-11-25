module

public import Mathlib
public import Formalism.LocalToGlobal.HermitianForms.PsiZeroNontrivialCharacter
public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.AfsplitB

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.UG NumberField IsDedekindDomain Matrix
open scoped TensorProduct

namespace GlobalTheory.St.G

abbrev Ad (F : Type) [Field F] [NumberField F] : Type := FiniteAdeleRing (𝓞 F) F

abbrev OAd (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] : Subring (E ⊗[F] Ad F) :=
  tensInt (F := F) (Ad F) (intOE E) (intAd F)


section Lat

variable (F : Type) {E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}


variable {F}




variable (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E)





end Lat



section Frame

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
  (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E)


variable {σ J} {Λ : Submodule (OAd F E) (Fin n → E ⊗[F] Ad F)} {g k : ℕ}





end Frame

end GlobalTheory.St.G

end
