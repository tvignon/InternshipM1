Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.limits.pullbacks.


Require Import UniMath.CategoryTheory.DisplayedCats.Auxiliary.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.Foundations.Sets.
Require Import UniMath.MoreFoundations.PartA.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Univalence. (* only coercions *)
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.categories.HSET.Core.
Require Import UniMath.CategoryTheory.categories.HSET.MonoEpiIso.
Require Import UniMath.CategoryTheory.categories.HSET.Univalence.
Require Import UniMath.CategoryTheory.limits.pullbacks.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.Presheaf.
Local Open Scope cat.

Require Import UniMath.CategoryTheory.DisplayedCats.Auxiliary.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.catiso.
Require Import TypeTheory.ALV2.CwF_SplitTypeCat_Cats.
Require Import TypeTheory.ALV2.SplitTypeCat_Cat_Simple.
Require Import TypeTheory.ALV1.CwF_SplitTypeCat_Maps.
Require Import TypeTheory.ALV1.CwF_SplitTypeCat_Defs.
Require Import TypeTheory.ALV1.TypeCat.

Require Import TypeTheory.ALV1.TypeCat_Reassoc.
Require Import TypeTheory.Articles.ALV_2017.
Require Import TypeTheory.ALV2.CwF_SplitTypeCat_Univalent_Cats.
Require Import TypeTheory.Auxiliary.Auxiliary.
Require Import TypeTheory.ALV2.SplitTypeCat_DiscCompCatDef_catiso.
Require Import TypeTheory.ALV2.DiscCompCatDef_Cat.
Require Import UniMath.CategoryTheory.CategoryEquality.
Local Open Scope cat.

Variable (C : category) (UC : is_univalent C).

Definition functor_data_form_iso {X Y : category} (f : X ≃ Y) (g : ∏ (a b : X), X⟦ a, b ⟧ ≃ Y⟦ f a , f b ⟧) : functor_data X Y.
Proof.
  use tpair.
  - exact f.
  - exact g.
Defined.

(*Lemma iso_imply_catiso {X Y : category} (f : X ≃ Y) (g : ∏ (a b : X), X⟦ a, b ⟧ ≃ Y⟦ f a , f b ⟧) 
(F_data := functor_data_form_iso f g : functor_data X Y) (F_ax : is_functor F_data): catiso X Y.
Proof.
  use tpair.
  - exact (F_data,,F_ax).
  - split.
    * intros a b. cbn. exact (pr2 (g a b)).
    * cbn. exact (pr2 f).
Qed.*)

Definition SplTC_typeequiv :  (SplitTy_cat C) ≃ (sty'_structure_precat C).
Proof.
  cbn.  
  apply (weq_standalone_to_regrouped C).
Defined.

Definition SplTC_equiv : (sty'_structure_precat C) ≃  (SplitTy_cat C) := invweq SplTC_typeequiv.


Lemma reind_ext_compare_irr {X : split_typecat_structure C}
{Γ : C} {A A' : (TY' C X : functor _ _) Γ : hSet} (e : A = A') (e' : A = A') :
reind_ext_compare C e = reind_ext_compare C e'.
Proof.
  induction e.
  apply (pathscomp0 (reind_ext_compare_id _ _)).
  exact (!(reind_ext_compare_id_general _ _)).
Qed.


Section morphisms_eqiv.
Variable (X Y : SplitTy_cat C).

Definition SplTC_mor_weq_f :  SplitTy_cat C ⟦ X , Y ⟧ →
sty'_structure_precat C ⟦ SplTC_typeequiv X , SplTC_typeequiv Y ⟧.
Proof.
  intros [[F_TY Gamma_ext] [F_TY_ax [Gamma_ext_ax q_ax]]].
    simple refine (_,,_).
    * simple refine (_,,_).
      +  cbn. simple refine (_,,_).
        ++  cbn. exact F_TY.
        ++ cbn. abstract( unfold is_nat_trans; cbn; intros Γ Γ' f;  apply funextsec2; intro A; exact (F_TY_ax Γ Γ' f A)).
      + cbn. intros Γ A. exact (Gamma_ext Γ A,, Gamma_ext_ax Γ A).
    * abstract(cbn; intros Γ' Γ f A; apply (pathscomp0 (q_ax Γ Γ' f A)); cbn; refine (cancel_postcomposition _ _ _ _);
      refine (cancel_precomposition _ _ _ _ _ _ _ _); cbn; unfold SplitTypeCat_Cat_Simple.Δ,F_TY_reind_ext_compare; cbn;
      set (e' := (toforallpaths (λ _ : (pr111 X) Γ, (pr111 Y) Γ')
      (λ x : (pr111 X) Γ, F_TY Γ' ((pr221 (pr1 X)) Γ x Γ' f))
      (λ x : (pr111 X) Γ, (pr221 (pr1 Y)) Γ (F_TY Γ x) Γ' f)
      (SplTC_mor_weq_f_subproof F_TY Gamma_ext F_TY_ax Γ Γ' f) A) : (F_TY Γ' (A {{f}}) = F_TY Γ A {{f}}));
      refine (pathscomp0 (maponpaths _ (reind_ext_compare_irr _ e')) _);
      reflexivity).
Defined.

Definition SplTC_mor_weq_g :  sty'_structure_precat C ⟦ SplTC_typeequiv X , SplTC_typeequiv Y ⟧ → SplitTy_cat C ⟦ X , Y ⟧.
Proof.
  intros [[[F_TY F_TY_ax] Gamma_ext] q_ax]. unfold nat_trans_data in F_TY; cbn in F_TY.
  unfold is_nat_trans in F_TY_ax; cbn in F_TY_ax. cbn in Gamma_ext. cbn in q_ax.
  simple refine (_,,_).
  * simple refine (_,,_).
    + exact F_TY.
    +  cbn. intros Γ A. exact (pr1 (Gamma_ext Γ A)).
  * cbn. simple refine (_,,_).
    + abstract( intros Γ Γ' f A; cbn; exact (toforallpaths _ _ _ (F_TY_ax Γ Γ' f) A)).
    + cbn. abstract( simple refine (_,,_); [
     intros Γ A; exact (pr2 (Gamma_ext Γ A))
     |
     cbn; intros Γ Γ' f A; apply (pathscomp0 (q_ax Γ' Γ f A)); cbn; refine (cancel_postcomposition _ _ _ _);
  refine (cancel_precomposition _ _ _ _ _ _ _ _); cbn; unfold SplitTypeCat_Cat_Simple.Δ,F_TY_reind_ext_compare; cbn;
  set (e' := (toforallpaths (λ _ : (pr111 X) Γ, (pr111 Y) Γ')
  (λ x : (pr111 X) Γ, F_TY Γ' ((pr221 (pr1 X)) Γ x Γ' f))
  (λ x : (pr111 X) Γ, (pr221 (pr1 Y)) Γ (F_TY Γ x) Γ' f) 
  (F_TY_ax Γ Γ' f) A) : (F_TY Γ' (A {{f}}) = F_TY Γ A {{f}}));
  apply pathsinv0;
  refine (pathscomp0 (maponpaths _ (reind_ext_compare_irr _ e')) _);
  reflexivity]).
Defined.

Definition SplTC_mor_weq_g_f : ∏ x : SplitTy_cat C ⟦ X , Y ⟧, SplTC_mor_weq_g(SplTC_mor_weq_f x) = x.
Proof.
  intro x. cbn. use subtypePath. 
  * intro S. apply isaprop_SplitTy_mor_axioms.
  * reflexivity.
Qed.

Lemma test ( x y : SplitTy_cat C ⟦ X , Y ⟧) (ea : λ Γ, pr11 x Γ = pr11 y a) (eb : λ transportf _ ea (pr21 x) = pr21 y ) : x = y.
Proof.
  use subtypePath.
  * intro S. apply isaprop_SplitTy_mor_axioms.
  *

Definition SplTC_mor_weq_f_g : ∏ x : sty'_structure_precat C ⟦ SplTC_typeequiv X , SplTC_typeequiv Y ⟧,
 SplTC_mor_weq_f(SplTC_mor_weq_g x) = x.
Proof.
  intros [[[a b] c] d]. use subtypePath.
    * abstract (intro y; cbn in y; do 4 (apply impred_isaprop; intro); apply (homset_property C)).
    * cbn. use total2_paths_f. abstract (use subtypePath; [
      intro x;  apply isaprop_is_nat_trans; apply (homset_property hset_category)|reflexivity]).
      cbn. admit.
Admitted.

(*)emma test ( x y : obj_ext_cat C ⟦ pr1 (SplTC_typeequiv X), pr1 (SplTC_typeequiv Y) ⟧
) (ea : pr11 x = pr11 y) (ec : ∏ Γ A,  transportf _ ea (pr1(pr2 x Γ A)) = pr1(pr2 y Γ A))  : x = y.
*)


Definition SplTC_mor_weq : SplitTy_cat C ⟦ X , Y ⟧ ≃
  sty'_structure_precat C ⟦ SplTC_typeequiv X , SplTC_typeequiv Y ⟧ := 
  (SplTC_mor_weq_f,,(isweq_iso _ SplTC_mor_weq_g SplTC_mor_weq_g_f SplTC_mor_weq_f_g)).

End morphisms_eqiv.

Definition SplTC_functor_data : functor_data (SplitTy_cat C)  (sty'_structure_precat C)
:= functor_data_form_iso SplTC_typeequiv SplTC_mor_weq.

Lemma SplTC_functor_idax : functor_idax (SplTC_functor_data).
Proof.
  intros c. 
  use total2_paths_f.
  + cbn.  unfold nat_trans_id. cbn. use total2_paths_f.
    * abstract (use subtypePath; [
      intro x; apply isaprop_is_nat_trans; apply (homset_property hset_category)
      | reflexivity]).
    * admit.
  + admit.
Admitted.

Lemma SplTC_functor_compax : functor_compax (SplTC_functor_data).
Proof.
  intros X Y Z f g.
  use total2_paths_f.
  + use total2_paths_f.
    * abstract (use subtypePath; [
      intro x; apply isaprop_is_nat_trans; apply (homset_property hset_category)
      | reflexivity]).
    * admit.
  + admit. 
Admitted.

Definition cat_equiv_SplTC : cat_equiv (SplitTy_cat C)  (sty'_structure_precat C).
Proof.
  exists (SplTC_typeequiv,, SplTC_mor_weq).
  split.
  * exact SplTC_functor_idax.
  * exact SplTC_functor_compax.
Defined.


Definition catiso_SplTC : catiso (SplitTy_cat C)  (sty'_structure_precat C) := cat_equiv_to_catiso _ _ cat_equiv_SplTC.


Lemma catiso_univalent' (A : precategory)  (B : precategory) : catiso B A → is_univalent A → is_univalent B.
Proof.
  intros F UA.
  assert (HA : has_homsets A) by (exact (pr2 UA)).
  simple refine (catiso_univalent _ _ _ _).
  * exact (A,,HA).
  * exact F.
  * exact UA.
Qed.

Lemma is_univalent_SpltTC : is_univalent (SplitTy_cat C).
Proof.
  exact (catiso_univalent' _ _ 
  catiso_SplTC (is_univalent_sty'_structure_precat UC)).
Qed.

Definition catiso_SplTC_DisCompCat : catiso (SplitTy_cat C) (DiscCompCatDef_cat C) :=
  ((SplitTy_DiscComp_functor C),,(SplitTy_DiscComp_functor_is_catiso C)).

Lemma catiso_inv {A B : category} (F : catiso A B) : catiso B A.
Proof.
  apply catiso_is_path_precat in F.
  * induction F. apply identity_catiso.
  * exact (pr2 B).
Defined.


Theorem is_univalent_Discompcat : is_univalent (DiscCompCatDef_cat C).
Proof.
  exact (catiso_univalent' _ _ 
  (catiso_inv catiso_SplTC_DisCompCat) is_univalent_SpltTC).
Qed.





 

 
