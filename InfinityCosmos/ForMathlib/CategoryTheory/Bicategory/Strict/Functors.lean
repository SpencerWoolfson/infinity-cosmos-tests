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

variable (A : Type u₁) (B : Type u₂) (C : Type u₃) (D : Type u₄) [Bicategory.{w₁, v₁} A] [Strict A]
  [Bicategory.{w₂, v₂} B] [Strict B] [Bicategory.{w₃, v₃} C] [Strict C] [Bicategory.{w₄, v₄} D] [Strict D]

def TwoFunctor.comp (F : A ⥤² B) (G : B ⥤² C) : A ⥤² C :=
  TwoFunctor.mk (StrictPseudofunctor.comp F.toStrictPseudofunctor G.toStrictPseudofunctor)

open scoped Pseudofunctor.StrongTrans

instance : CategoryStruct (A ⥤² B) where
  Hom F G := Pseudofunctor.StrongTrans F.toPseudofunctor G.toPseudofunctor
  id F := Pseudofunctor.StrongTrans.id F.toPseudofunctor
  comp α β := Pseudofunctor.StrongTrans.vcomp α β

instance (F G : A ⥤² B): Category (F ⟶ G) := Pseudofunctor.StrongTrans.homCategory

instance : Bicategory (A ⥤² B) where
  whiskerLeft {a b c} f g h η := by
    fconstructor
    fconstructor
    . exact fun d => f.app d ◁ (η.as.app d)
    . intros d k t
      rcases a with ⟨a⟩
      rcases b with ⟨b⟩
      rcases c with ⟨c⟩
      rcases η with ⟨⟨ηa,ηn⟩⟩
      simp [CategoryStruct.comp,Pseudofunctor.StrongTrans.vcomp]
      let ηn1 := ηn t
      let lemma1 : f.app d ◁ (g.naturality t).hom ≫ f.app d ◁ ηa d ▷ c.map t ≫ (α_ (f.app d) (h.app d) (c.map t)).inv = f.app d ◁ ((g.naturality t).hom ≫ ηa d ▷ c.map t) ≫ (α_ (f.app d) (h.app d) (c.map t)).inv := by
        exact Eq.symm (whiskerLeft_comp_assoc (f.app d) (g.naturality t).hom (ηa d ▷ c.map t) (α_ (f.app d) (h.app d) (c.map t)).inv)
      rw [lemma1, <- ηn1]
      simp only [<- Category.assoc, associator_inv_naturality_right]
      refine
        (Iso.cancel_iso_inv_right
              (((((α_ (a.map t) (f.app k) (g.app k)).inv ≫ (a.map t ≫ f.app k) ◁ ηa k) ≫
                    (f.naturality t).hom ▷ h.app k) ≫
                  (α_ (f.app d) (b.map t) (h.app k)).hom) ≫
                f.app d ◁ (h.naturality t).hom)
              ((((α_ (a.map t) (f.app k) (g.app k)).inv ≫ (f.naturality t).hom ▷ g.app k) ≫
                  (α_ (f.app d) (b.map t) (g.app k)).hom) ≫
                f.app d ◁ (b.map t ◁ ηa k ≫ (h.naturality t).hom))
              (α_ (f.app d) (h.app d) (c.map t))).mpr
          ?_
      simp [<- Category.assoc]
      congr 1
      simp only [associator_inv_naturality_right, Category.assoc]
      congr 1
      simp only [<- associator_naturality_right]
      exact whisker_exchange_assoc (f.naturality t).hom (ηa k) (α_ (f.app d) (b.map t) (h.app k)).hom
  whiskerRight {a b c f g } η γ := by sorry
    -- fconstructor
    -- fconstructor
    -- . exact fun d => (η.as.app d) ▷ γ.app d 
    -- . intros d k t
    --   rcases a with ⟨a⟩
    --   rcases b with ⟨b⟩
    --   rcases c with ⟨c⟩
    --   rcases η with ⟨⟨ηa,ηn⟩⟩
    --   simp [CategoryStruct.comp,Pseudofunctor.StrongTrans.vcomp]
    --   let ηn1 := ηn t
    --   simp at ηn1
    --   rw [<- Category.assoc, associator_inv_naturality_middle, Category.assoc]
    --   congr 1
    --   rw [<- associator_inv_naturality_left, <- Category.assoc,<- Category.assoc]
    --   simp only [associator_inv_naturality_middle]
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
    refine eqToIso ?_
    congr

  rightUnitor := by sorry
  whiskerLeft_id := by sorry
  whiskerLeft_comp := by sorry
  comp_whiskerLeft := by sorry









      -- refine (cancel_mono (f.app d ◁ (h.naturality t).hom)).mpr ?_
      -- rw [whisker_exchange (f.naturality t).hom (ηa k)]
      -- simp only [Category.assoc]
      -- refine (cancel_epi ((f.naturality t).hom ▷ g.app k)).mpr ?_
      -- exact associator_naturality_right (f.app d) (b.map t) (ηa k)




        


              



    



  --   fconstructor
  --   fconstructor
  --   . intro d
  --     refine f.app d ◁ ?_
  --     exact η.as.app d
  --   . intros d k t
  --     rcases a with ⟨a⟩
  --     rcases b with ⟨b⟩
  --     rcases c with ⟨c⟩
  --     rcases η with ⟨⟨ηa,ηn⟩⟩
  --     simp
  --     simp at ηn
  --     simp [CategoryStruct.comp,Pseudofunctor.StrongTrans.vcomp]
  --     simp [<- Category.assoc]
  --     rw [associator_inv_naturality_right,Strict.associator_eqToIso]
  --     simp [Category.assoc,Strict.associator_eqToIso]
  --     simp [<- Category.assoc]
  --     congr 2
  --     . sorry

      -- rw [associator_inv_naturality_left]

      -- refine (Iso.eq_comp_inv ((f ≫ h).naturality t)).mp ?_
      -- let en := ηn t
      -- let en' := (Iso.inv_comp_eq ((g).naturality t)).mpr en
      -- rw [<- en']

      -- let help := congr_arg (fun (x : Iso _ _) => x.hom ) (Iso.trans_symm ((f ≫ h).naturality t) (α_ (f.app d) (h.app d) (c.map t)))
      -- dsimp at help
      -- rw [<-help]
      -- simp

      -- let attm1 := Pseudofunctor.StrongTrans.Modification.whiskerLeft_naturality η.as (f.app d) t
      -- let s1 :=  η.as.naturality t
      -- let s2 : a.obj d ⟶ b.obj d := f.app d
      -- let s3 := congr_arg (fun x => s2 ◁ x) s1
      -- simp [CategoryStruct.comp,Pseudofunctor.StrongTrans.vcomp]
      -- simp [Bicategory.Strict.associator_eqToIso]
      -- rw [<- Category.assoc (f.app d ◁ (g.naturality t).hom)]
      -- -- rw [<- attm1]
      -- simp at s3
      -- simp [<- Category.assoc]
      -- congr 1
      -- simp [Category.assoc]
      -- rw [<- attm1]
      -- rw [<- Category.assoc _ _ (f.app d ◁ (h.naturality t).hom)]
      -- rw [<- Category.assoc _ _ (f.app d ◁ (h.naturality t).hom)]
      -- rw [<- Category.assoc _ _ (f.app d ◁ (h.naturality t).hom)]
      -- rw [<- Category.assoc _ _ (f.app d ◁ (h.naturality t).hom)]
      -- rw [<- Category.assoc _ _ (f.app d ◁ (h.naturality t).hom)]
      -- rw [<- Category.assoc _ _ (f.app d ◁ (h.naturality t).hom)]
      -- congr 1
      -- rcases f with ⟨fa,fb,fc,fd,fe⟩
      -- simp

      -- dsimp [s2] at s3
      -- rw [whiskerLeft_comp (f.app d) (b.map t ◁ η.as.app k) ((h.naturality t).hom),attm1] at s3