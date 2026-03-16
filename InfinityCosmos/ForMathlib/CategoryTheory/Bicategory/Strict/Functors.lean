import Mathlib.CategoryTheory.Bicategory.Functor.StrictPseudofunctor
import Mathlib.CategoryTheory.Bicategory.Strict.Pseudofunctor
import Mathlib.CategoryTheory.Bicategory.NaturalTransformation.Pseudo
import Mathlib.CategoryTheory.Bicategory.Modification.Pseudo
/-
  This file is ment to provide a clean API for what are normaly called 2-functors.
  This is done by combineing to concepts in mathlib and building on them.
  These concepts are
  1) Strict Pseudofunctors, which are pseudofunctors such that `mapId` and `mapComp` are given by `eqToIso _`.
  2) Pseudofunctors between Strict Bicategories
-/

universe w₁ w₂ w₃ w₄ v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

namespace CategoryTheory

open Bicategory

/- TwoFunctor here is defined as a StrictPseudofunctor between
  Strict Bicategories. This can also just be done explicitly
  so the structure TwoFunctor is not "strictly" nesisary.
  I am not sure of best practices here but it should not be
  dificult to fix.
-/
structure TwoFunctor (A : Type u₁) (B : Type u₂) [Bicategory.{w₁, v₁} A] [Strict A]
  [Bicategory.{w₂, v₂} B] [Strict B] extends StrictPseudofunctor A B

scoped[CategoryTheory.Bicategory] infixr:26 " ⥤² " => TwoFunctor

variable (A : Type u₁) (B : Type u₂) (C : Type u₃) (D : Type u₄) [Bicategory.{w₁, v₁} A]
  [Bicategory.{w₂, v₂} B] [Bicategory.{w₃, v₃} C] [Bicategory.{w₄, v₄} D]

open scoped Pseudofunctor.StrongTrans

instance : CategoryStruct (A ⥤ᵖ B) := by
  exact Pseudofunctor.StrongTrans.categoryStruct
  -- Hom F G := Pseudofunctor.StrongTrans F.toPseudofunctor G.toPseudofunctor
  -- id F := Pseudofunctor.StrongTrans.id F.toPseudofunctor
  -- comp α β := Pseudofunctor.StrongTrans.vcomp α β

instance (F G : A ⥤ᵖ B): Category (F ⟶ G) := Pseudofunctor.StrongTrans.homCategory


#check Bicategory.comp_whiskerRight

instance : Bicategory (A ⥤ᵖ B) where
  whiskerLeft {a b c} f g h η := by
    fconstructor
    fconstructor
    . exact fun d => f.app d ◁ (η.as.app d)
    . intros d k t
      rcases η with ⟨⟨ηa,ηn⟩⟩
      simp [CategoryStruct.comp,Pseudofunctor.StrongTrans.vcomp]
      let ηn1 := ηn t
      let lemma1 : f.app d ◁ (g.naturality t).hom ≫ f.app d ◁ ηa d ▷ c.map t ≫ (α_ (f.app d) (h.app d) (c.map t)).inv = f.app d ◁ ((g.naturality t).hom ≫ ηa d ▷ c.map t) ≫ (α_ (f.app d) (h.app d) (c.map t)).inv := by
        exact Eq.symm (whiskerLeft_comp_assoc (f.app d) (g.naturality t).hom (ηa d ▷ c.map t) (α_ (f.app d) (h.app d) (c.map t)).inv)
      rw [lemma1, <- (ηn t)]
      simp only [<- Category.assoc, associator_inv_naturality_right]
      simp [<- Category.assoc]
      congr 1
      simp only [associator_inv_naturality_right, Category.assoc]
      congr 1
      simp only [<- associator_naturality_right]
      exact whisker_exchange_assoc (f.naturality t).hom (ηa k) (α_ (f.app d) (b.map t) (h.app k)).hom
  whiskerRight {a b c f g } η γ := by
    fconstructor
    fconstructor
    . exact fun d => (η.as.app d) ▷ γ.app d
    . intros d k t
      rcases η with ⟨⟨ηa,ηn⟩⟩
      simp [CategoryStruct.comp,Pseudofunctor.StrongTrans.vcomp]
      let ηn1 := ηn t
      simp at ηn1
      rw [<- Category.assoc, associator_inv_naturality_middle,<- associator_inv_naturality_left,Category.assoc]
      congr 1
      simp only [<- Category.assoc, <- comp_whiskerRight,ηn1]
      congr 1
      simp [Category.assoc]
      congr 1
      rw [whiskerRight_comp_symm (ηa d) (γ.app d) (c.map t)]
      simp only [Category.assoc,(α_ (g.app d) (γ.app d) (c.map t)).inv_hom_id, Category.comp_id]
      simp only [<- Category.assoc , (α_ (f.app d) (γ.app d) (c.map t)).inv_hom_id,Category.comp_id]
      rw [associator_naturality_left]
      simp only [Category.assoc]
      congr 1
      exact Eq.symm (whisker_exchange (ηa d) (γ.naturality t).hom)
  associator {a b c d} f g h := by
    fconstructor
    . fconstructor
      fconstructor
      intro x
      refine (Bicategory.associator (f.app x) (g.app x) (h.app x)).hom
      intros x y l
      simp [CategoryStruct.comp,Pseudofunctor.StrongTrans.vcomp,Oplax.OplaxTrans.vcomp]
    . fconstructor
      fconstructor
      intro x
      refine (Bicategory.associator (f.app x) (g.app x) (h.app x)).inv
      intros x y l
      simp [CategoryStruct.comp,Pseudofunctor.StrongTrans.vcomp,Oplax.OplaxTrans.vcomp]
    . dsimp [CategoryStruct.comp,Pseudofunctor.StrongTrans.Modification.vcomp]
      congr
      funext x
      simp
    . dsimp [CategoryStruct.comp,Pseudofunctor.StrongTrans.Modification.vcomp]
      congr
      funext x
      simp
  leftUnitor {a b} f := by
    fconstructor
    . fconstructor
      fconstructor
      . exact fun x => (Bicategory.leftUnitor (f.app x)).hom
      . simp
    . fconstructor
      fconstructor
      . exact fun x => (Bicategory.leftUnitor (f.app x)).inv
      . simp
    . simp[CategoryStruct.comp,Pseudofunctor.StrongTrans.Modification.vcomp,CategoryStruct.id]
      congr
    . simp[CategoryStruct.comp,Pseudofunctor.StrongTrans.Modification.vcomp,CategoryStruct.id]
      congr
  rightUnitor {a b} f := by
    fconstructor
    . fconstructor
      fconstructor
      . exact fun x => (Bicategory.rightUnitor (f.app x)).hom
      . simp
    . fconstructor
      fconstructor
      . exact fun x => (Bicategory.rightUnitor (f.app x)).inv
      . simp
    . simp[CategoryStruct.comp,Pseudofunctor.StrongTrans.Modification.vcomp,CategoryStruct.id]
      congr
    . simp[CategoryStruct.comp,Pseudofunctor.StrongTrans.Modification.vcomp,CategoryStruct.id]
      congr
  whiskerLeft_id {a b c} f g := by
    simp
    congr 2
  whiskerLeft_comp f g h x η θ:= by
    simp
    congr 2
  comp_whiskerLeft f g h x η := by
    simp
    congr 2
  whisker_exchange η θ := by
    simp[CategoryStruct.comp,Pseudofunctor.StrongTrans.Modification.vcomp]
    congr 2
    funext x
    rw [Bicategory.whisker_exchange]
