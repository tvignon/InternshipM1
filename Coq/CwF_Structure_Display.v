(**
Content :
- Some lemma on Yoneda
- Famillies of Types in CwF (DepTypes prefixe mostly)
- Pi Types in CwF (CwF_Pi prefixe)
- Sigma Types in CwF (CwF_Sig prefixe)
- Identity Types in CwF (CwF_Id prefixe)
**)

Require Import UniMath.Foundations.Sets.
Require Import UniMath.MoreFoundations.All.
Require Import TypeTheory.Auxiliary.CategoryTheoryImports.
Require Import TypeTheory.Auxiliary.Auxiliary.
Require Import TypeTheory.ALV1.CwF_def.



Notation "'pr1121' x" := (pr1(pr1(pr2(pr1(x))))) (at level 30).
Notation "'pr2121' x" := (pr2(pr1(pr2(pr1(x))))) (at level 30).

Section Fix_Category.
(** * Preliminaries *)
(** General context for a category with famillies and some usefull notations *)  
Context {CwF : cwf}.
Local Definition C : category := pr1(CwF).
Local Definition pp : mor_total(preShv(C)) := pr12 CwF.
Local Definition Ty : functor _ _ := target pp.
Local Definition Tm : functor _ _ := source pp.
(* extension of context *)
Local Definition ext (Γ : C) (A : Ty Γ : hSet) : C := pr11 pr22 CwF Γ A.
Local Notation "Γ .: A" :=  (ext Γ A) (at level 24).

Local Definition pi {Γ : C} (A : Ty Γ : hSet) : C⟦Γ.:A,Γ⟧ := pr21 pr22 CwF _ A.
(* just a simple to use pp as a nat_trans *)
Local Definition Nat_trans_morp {C : category} (Γ : C) (p : mor_total(preShv C))
: HSET_univalent_category ⟦ (pr21 p : functor _ _) Γ, (pr11 p : functor _ _) Γ ⟧ := pr12 p Γ.

Notation "p __: Γ" := (Nat_trans_morp Γ p)  (at level 24).
Local Definition pp_ (Γ : C) : (Tm Γ : hSet) → (Ty Γ : hSet) := pp __: Γ.

Lemma Ty_composition {Γ Γ' Γ'' : C} (f : C⟦Γ,Γ'⟧) (g : C⟦Γ',Γ''⟧) (A : Ty Γ'' : hSet) 
: #Ty (f;;g) A = #Ty f (#Ty g A).
Proof.
  exact (!((toforallpaths _ _ _ (!(pr22 Ty _ _ _  g f))) A)).
Qed.

Lemma Tm_composition {Γ Γ' Γ'' : C} (f : C⟦Γ,Γ'⟧) (g : C⟦Γ',Γ''⟧) (A : Tm Γ'' : hSet)
: #Tm (f;;g) A = #Tm f (#Tm g  A).
Proof.
  exact (!((toforallpaths _ _ _ (!(pr22 Tm _ _ _  g f))) A)).
Qed.

Lemma Ty_identity {Γ : C} (A : Ty Γ : hSet) : A = #Ty (identity Γ) A.
Proof.
  assert (eqA : A = (identity (pr1 Ty Γ) A)) by auto.
  rewrite eqA.
  apply (!((toforallpaths _ _ _ (pr12 Ty _ )) A)).
Qed.

(** * Tm as a Display **)
Section tm.
Local Definition tm {Γ : C} (A : Ty Γ : hSet) : UU
:= ∑ (a : Tm Γ : hSet), pp_ _ a = A.

Local Definition pr1_tm {Γ : C} {A : Ty Γ : hSet} (a : tm A) : Tm Γ : hSet := pr1 a.
Coercion pr1_tm : tm >-> pr1hSet.

Lemma ppComp1 {Γ Δ : C} {A : Ty Γ : hSet} (f : C^op ⟦Γ,Δ⟧) (a : tm A) :
  pp_ _ (# Tm f a ) = # Ty f A. 
Proof.
  apply pathsinv0, (pathscomp0(!(maponpaths (# Ty f) (pr2 a)))).
  apply pathsinv0, (toforallpaths _ _ _ (pr22 pp _ _ f) a) .
Qed.

Definition reind_cwf {Γ : C} (A : Ty Γ : hSet) {Γ'} (f : C⟦Γ',Γ⟧)
: Ty Γ' : hSet := #Ty f A.
Local Definition reind_tm {Γ Δ} (f : C^op ⟦Γ,Δ⟧) {A : Ty Γ : hSet} (x : tm A)
: tm (#Ty f A) := #Tm f x,,ppComp1 f x.

Local Definition te {Γ : C} (A : Ty Γ : hSet) : tm (#Ty (pi A) A)
:= pr12 pr22 CwF _ A.
(* proof of pp (te A) = Ty (pi A) A*)
Local Definition te' {Γ : C} (A : Ty Γ : hSet) : pp_ _ (te A) = #Ty (pi A) A := pr212 pr22 CwF Γ A.
Definition CwF_Pullback {Γ} (A : Ty Γ : hSet) : isPullback (yy A) pp (#Yo (pi A)) (yy(te A)) (cwf_square_comm (te' A)) := pr22 pr22 CwF Γ A.

Local Definition tm_transportf {Γ} {A A' : Ty Γ : hSet} (e : A = A')
: tm A ≃ tm A'.
Proof.
  use weqbandf.
  -  exact (idweq (Tm Γ : hSet)).
  -  induction e. intro x. exact (idweq _).
Defined.

Local Definition tm_transportb {Γ} {A A' : Ty Γ : hSet} (e : A = A')
: tm A' ≃ tm A := invweq(tm_transportf e).

Lemma tm_transportf_idpath {Γ} {A : Ty Γ : hSet} (t : tm A)
: tm_transportf (idpath A) t = t.
Proof.
  reflexivity.
Qed.

Lemma tm_transportb_idpath {Γ} {A : Ty Γ : hSet} (t : tm A)
: tm_transportb (idpath A) t = t.
Proof.
  reflexivity.
Qed.

Lemma tm_transportbf {Γ} {A A' : Ty Γ : hSet} (e : A = A') : tm_transportb e = tm_transportf (!e).
Proof.
  induction e.
  refine (subtypePath isapropisweq _).
  apply (idpath _).
Qed.

Lemma reind_compose_tm
{Γ Γ' Γ'' : C} (f : C⟦Γ',Γ⟧) (g : C⟦Γ'',Γ'⟧) {A : Ty Γ : hSet} (a : tm A)
: reind_tm (g ;; f) a 
= tm_transportb (Ty_composition _ _ _) (reind_tm g (reind_tm f a)).
Proof.
  apply subtypePath. 
  -  intro x. apply (setproperty (Ty Γ'' : hSet)).
  -  rewrite tm_transportbf. apply Tm_composition.
Qed.

Lemma maponpaths_2_reind_tm 
{Γ Γ' : C} {f f' : C⟦Γ',Γ⟧} (e : f = f') {A : Ty Γ : hSet} (a : tm A)
: reind_tm f a = tm_transportb (maponpaths (fun g => #Ty g A) e) (reind_tm f' a).
Proof.
  induction e.
  rewrite maponpaths_eq_idpath; [|apply idpath].
  now rewrite tm_transportb_idpath.
Qed.

Lemma tm_transportf_compose {Γ : C} {A A' A'' : Ty Γ : hSet} (e : A = A')
(e' : A' = A'') (a : tm A) 
: tm_transportf (e @ e') a = tm_transportf e' (tm_transportf e a).
Proof.
  induction e.
  induction e'.
  reflexivity.
Qed.

Lemma tm_transportf_irrelevant {Γ} {A A' : Ty Γ : hSet} (e e' : A = A')
(t : tm A)
: tm_transportf e t = tm_transportf e' t.
Proof.
  apply (maponpaths (fun e => tm_transportf e t)).
  apply (setproperty (Ty Γ : hSet)).
Qed.

Lemma tm_transport_compose {Γ Γ' Γ'' : C} (f : C⟦Γ',Γ⟧) (g : C⟦Γ'',Γ'⟧) (A : Ty Γ : hSet) (a : tm A)
: tm_transportf ((Ty_composition g f A)) (reind_tm (g;;f) a) = reind_tm g (reind_tm f a).
Proof.
  rewrite reind_compose_tm.
  rewrite tm_transportbf.
  rewrite <- tm_transportf_compose ,pathsinv0l.
  reflexivity.
Qed.

Lemma tm_transportf_bind {Γ} {A A' A'': Ty Γ : hSet} {e : A' = A} {e' : A'' = A'}
{t} {t'} {t''} (ee : t = tm_transportf e t') (ee' : t' = tm_transportf e' t'')
: t = tm_transportf (e' @ e) t''.
Proof.
  etrans. 2: { apply pathsinv0, tm_transportf_compose. }
  etrans. { eassumption. }
  apply maponpaths; assumption.
Qed.

Lemma reind_compose_tm' 
{Γ Γ' Γ'' : C} (f : C⟦Γ',Γ⟧) (g : C⟦Γ'',Γ'⟧) {A : Ty Γ : hSet} (a : tm A)
: tm_transportf (Ty_composition _ _ _)
        (reind_tm (g ;; f) a)
      = reind_tm g (reind_tm f a).
Proof.
  rewrite reind_compose_tm. rewrite tm_transportbf.
  now rewrite <- tm_transportf_compose, pathsinv0l, tm_transportf_idpath.
Qed.

Lemma reind_id_tm {Γ : C}{A : Ty Γ : hSet} (a : tm A)
: reind_tm (identity _) a
= tm_transportb ((toforallpaths _ _ _ (pr12 Ty _ )) A) a.
Proof.
  apply subtypePath. 
  -  intros x. apply (setproperty (Ty Γ : hSet)).
  -  apply ((toforallpaths _ _ _ (pr12 Tm _ )) a).
Qed.

End tm. 

Section Yoneda.
 
(** * Few usefull lemma on yoneda **)

Lemma yonedainv {A B : C} (f : C⟦A,B⟧) : Yo^-1 (#Yo f) = f.
Proof.
  apply id_left.
Qed.

Lemma transportyo {A B : C} {f g : C⟦A,B⟧} (e : #Yo f = #Yo g) : f = g.
Proof.
  apply (pathscomp0 (!(yonedainv f))), pathsinv0
  ,(pathscomp0 (!(yonedainv g))), (!(maponpaths Yo^-1 e)).
Qed.

Lemma yonedacarac {Γ Δ : C} (f  : _ ⟦Yo Γ,Yo Δ⟧) 
: # Yo ((f :nat_trans _ _) Γ (identity Γ)) = f.
Proof.
  assert (H : (# Yo ((f : nat_trans _ _) Γ (identity Γ)) : nat_trans _ _) Γ (identity Γ)
               = (f : nat_trans _ _) Γ (identity Γ)) by apply (id_left _).
  assert (Map1 : (f : nat_trans _ _) Γ (identity Γ) = yoneda_map_1 C (pr2 C) Γ (Yo(Δ)) f) by reflexivity.
  assert (Map2 : # Yo ((f : nat_trans _ _) Γ (identity Γ)) = yoneda_map_2 C (pr2 C) Γ (Yo(Δ))
         ((f : nat_trans _ _) Γ (identity Γ))).                                      
  -  unfold yoneda_map_2; cbn; unfold yoneda_morphisms; unfold yoneda_morphisms_data; cbn.
     assert (nattrans : is_nat_trans_yoneda_morphisms_data C _ Γ Δ
         ((f :nat_trans _ _) Γ (identity Γ))
          = yoneda_map_2_ax C (pr2 C) Γ (yoneda_objects C _ Δ)
          ((f : nat_trans _ _) Γ (identity Γ))).
     --  assert (prop : isaprop(is_nat_trans (yoneda_objects C _ Γ)
         (yoneda_objects C (homset_property C) Δ)
         (yoneda_morphisms_data C _ Γ Δ
         ((f : nat_trans _ _) Γ (identity Γ))))) by (apply isaprop_is_nat_trans;exact (pr2 hset_category));
        exact (pr1 (prop _ _)).
     --  apply pair_path_in2; apply nattrans.
  -  rewrite Map2; rewrite Map1; apply yoneda_map_1_2.
Qed.

Lemma invyoneda {A B : C} (f : _⟦Yo A,Yo B⟧) : #Yo (Yo^-1 f) = f.
Proof.
  apply yonedacarac.  
Qed.

Lemma yyidentity {Γ : C} {A : Ty Γ : hSet} (B : Ty (Γ.:A) : hSet) 
: B = (@yy (pr1 C) (pr2 C) Ty (Γ.:A) B : nat_trans _ _) (Γ.:A) (identity (Γ.:A)).
Proof.
  apply pathsinv0; eapply pathscomp0.
  -  apply (toforallpaths _ (# Ty _) _ (functor_id Ty (Γ.:A))).
  -  reflexivity.
Qed.

End Yoneda.

Section qq.
(** morphism between contexts *)

Let Xk {Γ : C} (A : Ty Γ : hSet) :=
  make_Pullback _ _ _ _ _ _ (pr22 pr22 CwF Γ A).

Local Definition qq_yoneda {Γ  Δ : C} (A : Ty Γ : hSet) (f : C^op ⟦Γ,Δ⟧)
: (preShv C) ⟦Yo (Δ .: (#Ty f A)), Yo (Γ.: A) ⟧.
Proof.
  use (PullbackArrow (Xk A)).
  -  apply (#Yo (pi _) ;; #Yo f ). 
  -  apply (yy (te _)).
  -  abstract (
        clear Xk;
        assert (XT := (cwf_square_comm (te' (#Ty f A) )));
        eapply pathscomp0; try apply XT; clear XT;
        rewrite <- assoc; apply maponpaths;
        apply pathsinv0, yy_natural
     ).
Defined.

Lemma qq_yoneda_commutes_1 {Γ Δ : C} (A : Ty Γ : hSet) (f : C ⟦Δ,Γ⟧)
: (# Yo (pi (#Ty f A)) ;; # Yo f) = (qq_yoneda A f) ;; # Yo (pi A ) .
Proof.
  apply pathsinv0.
  apply (PullbackArrow_PullbackPr1 (Xk _)).
Qed.

Lemma qq_yoneda_commutes {Γ Δ : C} (A : Ty Γ : hSet) (f : C^op ⟦Γ,Δ⟧)
: (qq_yoneda A f) ;; yy (te A) = yy (te (#Ty f A)).
Proof.
  apply (PullbackArrow_PullbackPr2 (Xk A)).
Qed.


Local Definition qq_term {Γ  Δ : C} (A : Ty Γ : hSet) (f : C^op ⟦Γ,Δ⟧)
: C ⟦ Δ.:(#Ty f A) , Γ.: A⟧.
Proof.
  apply (invweq (make_weq _ (yoneda_fully_faithful _ (homset_property _) _ _ ))) ,
  (qq_yoneda A f).
Defined.

Lemma qq_yoneda_compatibility {Γ  Δ : C} (A : Ty Γ : hSet) (f : C^op ⟦Γ,Δ⟧) :
 #Yo(qq_term A f) = qq_yoneda A f.
Proof.
  apply (homotweqinvweq
  (make_weq _ (yoneda_fully_faithful _ (homset_property _) ( _ .:(#Ty f A)) (Γ.:A)))).
Qed.

Lemma qq_term_te {Γ Δ : C} (A : Ty Γ : hSet) (f : C^op ⟦Γ,Δ⟧) 
: #Tm (qq_term A f) (te A) = te (#Ty f A).
Proof.
  assert (Hyp := qq_yoneda_commutes A f).
  rewrite <- qq_yoneda_compatibility in Hyp. 
  apply (pathscomp0 (yy_natural  _ _ _ _ _)) in Hyp.
  apply (invmaponpathsweq (@yy _ (pr2 C) _ _) ).
  exact Hyp.
Qed.

Lemma qq_term_pullback {Γ  Δ :C} (A : Ty Γ : hSet) (f : C^op ⟦Γ,Δ⟧)
: f ;; pi (#Ty f A) = (qq_term A f);; pi A.
Proof.
  assert (XT := (qq_yoneda_commutes_1 A f)).
  rewrite <- qq_yoneda_compatibility in XT.
  do 2 rewrite <- functor_comp in XT.
  apply (invmaponpathsweq (make_weq _ (yoneda_fully_faithful _ (homset_property _) _ _ ))).
  cbn; cbn in XT; exact XT.
Qed.

Section Familly_Of_Types.
(** Famillies of types in a Category with famillies**)
Lemma Subproof_γ {Γ : C} {A : Ty Γ : hSet} (a : tm A)
: identity (Yo Γ) ;; yy A = yy a ;;pp.
Proof.
  apply pathsinv0, (pathscomp0(yy_comp_nat_trans Tm Ty pp Γ a)) ,pathsinv0,
  (pathscomp0(id_left _ )), ((maponpaths yy) (!(pr2 a))).
Qed.

Definition γ {Γ : C} {A : Ty Γ : hSet} (a : tm A) : (preShv C)⟦Yo Γ,Yo (Γ.:A)⟧
:= pr11((CwF_Pullback A) (Yo Γ) (identity _) (yy a) (Subproof_γ a)).

Lemma  γ_pull {Γ : C} (A : Ty Γ : hSet)
: γ (te A) ;; yy (te (#Ty (pi A) A)) = yy (te A).
Proof.
  exact (pr221((CwF_Pullback _) (Yo (Γ.:A)) (identity _) (yy _) (Subproof_γ _))).
Qed.

Lemma pull_γ {Γ : C} {A : Ty Γ : hSet} (a : tm A) : γ a ;; #Yo (pi A) = identity _.
Proof.
  apply pathsinv0, (pathscomp0(!(pr121 (CwF_Pullback _
        (Yo Γ) (identity (Yo Γ)) (yy a)
        (Subproof_γ a))))); auto.
Qed.

Lemma γNat {Γ Δ : C} {A : Ty Γ : hSet} (f : C^op ⟦Γ,Δ⟧) (a : tm A)
: (f : C⟦Δ,Γ⟧) ;; (γ a : nat_trans _ _) Γ (identity Γ) =
  (γ (reind_tm f a ) ;; #Yo (qq_term A f) : nat_trans _ _) Δ (identity Δ).
Proof.
  assert (Yoγ : #Yo ((f : C⟦Δ,Γ⟧) ;; (γ a : nat_trans _ _) Γ (identity Γ)) =
  #Yo((γ (reind_tm f a) : nat_trans _ _) Δ (identity Δ) ;; qq_term A f)).
  -  do 2 (rewrite (pr22 (yoneda C (pr2 C)) _ _ _); rewrite yonedacarac).
     refine (MorphismsIntoPullbackEqual (CwF_Pullback A)
     (#Yo f ;; γ a) (γ (reind_tm f a) ;; #Yo (qq_term A f)) _ _).
     --  rewrite <- assoc.
         eapply pathscomp0.
         *  rewrite (cancel_precomposition _ _ _ _ _ _ _
            (pr121((CwF_Pullback _) (Yo Γ) (identity (Yo Γ)) (yy(a)) (Subproof_γ a )))).
            apply id_right.
         *  rewrite qq_yoneda_compatibility.
            rewrite <- assoc.
            apply pathsinv0.
            eapply pathscomp0.
            **  rewrite (cancel_precomposition _ _ _ _ _ _ _
                (pr121 ((pr22 (Xk A))
                (Yo (_.: # Ty f A)) (# Yo (pi (#Ty f A));; # Yo f)
                (yy (te (#Ty f A))) (qq_yoneda_subproof Γ Δ A f)))).
                rewrite assoc.
                rewrite  (cancel_postcomposition _ _ _
                (pr121 ((CwF_Pullback _) (Yo Δ) (identity (Yo Δ))
                (yy(#Tm f a)) (Subproof_γ (reind_tm f a) )))).
                apply (pr1 (pr121 (preShv C)) _ (Yo Γ) (#Yo f)).
            **  reflexivity.
    --  rewrite <- assoc.
        apply (pathscomp0  (cancel_precomposition _ _ _ _ _ _ _
        (pr221((CwF_Pullback _) (Yo Γ) (identity (Yo Γ)) (yy(a)) (Subproof_γ a ))))).
        rewrite qq_yoneda_compatibility.
        rewrite <- assoc.
        apply pathsinv0.
        eapply pathscomp0.
        *  rewrite (cancel_precomposition _ _ _ _ _ _ _
           (pr221 ((pr22 (Xk A))
           (Yo (_.: # Ty f A)) (# Yo (pi (#Ty f A));; # Yo f)
           (yy (te (#Ty f A))) (qq_yoneda_subproof Γ Δ A f)))).
           apply (pr221( (pr22(pr22 CwF Δ (#Ty f A)))
           (Yo Δ) (identity (Yo Δ)) (yy(#Tm f a)) (Subproof_γ (reind_tm f a )))).
        *  apply yy_natural.
  -  apply (transportyo Yoγ).
Qed.

Lemma γPullback1 {Γ : C} (A : Ty Γ : hSet)
: γ (te A) ;; #Yo (qq_term A (pi A)) ;; yy(te A) = identity _;; yy (te A).
Proof.
  rewrite id_left.
  assert (γ (te A) ;; yy ( te (# Ty (pi A) A)) = yy( te A)) by 
  (rewrite <- (pr221 (pr22 (pr22 CwF (Γ.:A) (#Ty (pi A) A))
    (Yo (Γ.:A)) (identity _) (yy (te A))
    (Subproof_γ (te A) ))); auto) .
  rewrite (qq_yoneda_compatibility A (pi A)), <- assoc, <- X.
  refine (cancel_precomposition _ _ _ _ _ _ _ _).
  rewrite X.
  apply (qq_yoneda_commutes A (pi A)).
Qed.

Lemma  γPullback2 {Γ : C} (A : Ty Γ : hSet)
: γ (te A) ;; #Yo (qq_term A (pi A)) ;; #Yo (pi A) = identity _;;(#Yo (pi A)).
Proof.
  assert (Eq1 : #Yo (pi (#Ty (pi A) A)) ;; #Yo (pi A) = qq_yoneda A (pi A) ;; #Yo (pi A)) by (
  rewrite <- (pr121((pr22(make_Pullback (yy A) pp
    (yoneda (pr1 CwF) (homset_property (pr1 CwF))
    (Γ.:A))
    (# (yoneda (pr1 CwF) (homset_property (pr1 CwF)))
    (pi A))
    (yy (pr112 (pr22 CwF Γ A)))
    (cwf_square_comm (pr212 (pr22 CwF Γ A)))
    (CwF_Pullback A))) (Yo (_ .: (#Ty (pi A) A)))
    (#Yo (pi (#Ty (pi A) A)) ;; #Yo (pi A)) (yy (te (#Ty (pi A) A)))
    (qq_yoneda_subproof Γ (Γ.: A) A (pi A))));          
  auto).         
  rewrite (qq_yoneda_compatibility A (pi A)), <- assoc.
  assert (Eq2 : γ (te A);; #Yo (pi (#Ty (pi A) A)) = identity _) by 
  (apply pathsinv0, (pathscomp0(!(pr121 (CwF_Pullback _
        (Yo (Γ.:A)) (identity (Yo (Γ.:A))) (yy (te A))
        (Subproof_γ (te A))))));
  auto).
  apply (pathscomp0 (cancel_precomposition _ _ _ _ _ _ (γ (te A)) (!Eq1))).
  rewrite assoc.
  apply (pathscomp0 (cancel_postcomposition _ _ _ (Eq2))).
  reflexivity.
Qed.

Definition γ_qq {Γ} {A : Ty Γ: hSet} {Γ'} (f : C⟦Γ',Γ⟧) (a : tm (#Ty f A)) : C⟦Γ',Γ.: A⟧.
Proof.
  exact (Yo^-1 (γ a) ;; qq_term A f).    
Defined.

Lemma γ_pi {Γ} {A : Ty Γ: hSet} (a : tm A) : Yo^-1 (γ a) ;; pi A = identity _.
Proof.
  assert (Yoeq : #Yo(Yo^-1 (γ a) ;; pi A) = #Yo(identity Γ)).
  -  apply (pathscomp0 (pr22 Yo _ _ _  _ _ )).
     apply pathsinv0 , (pathscomp0 (pr12 Yo _)).    
     assert (simplman : identity (pr1 (yoneda C (homset_property C)) Γ) 
     = identity (Yo Γ)) by auto.
     apply (pathscomp0 simplman).
     rewrite (!(pull_γ a)).
     apply cancel_postcomposition.
     assert (simplman2 : # (pr1 (yoneda C (homset_property C))) (Yo^-1 (γ a))
     = #Yo (Yo^-1 (γ a))) by auto.
     apply pathsinv0, (pathscomp0 simplman2), invyoneda.
  -  apply (maponpaths (Yo^-1) ) in Yoeq.
     rewrite yonedainv, yonedainv in Yoeq.
     exact Yoeq.
Qed.

Lemma te_subtitution {Γ} {A : Ty Γ : hSet} (a : tm A) : #Tm (Yo^-1(γ a)) (te A) = a.
Proof.
  assert (inter : @yy _ (pr2 C) _ _ (#Tm (Yo^-1(γ a)) (te A)) = yy a). 
  -  rewrite yy_natural, invyoneda. 
     exact (pr221((CwF_Pullback _) (Yo _) (identity _) (yy _) (Subproof_γ _))).
  -  apply (maponpaths (invmap yy) ) in inter.
     do 2 rewrite homotinvweqweq in inter.
     exact inter.
Qed.

Lemma reind_id_tm' {Γ : C} {A : Ty Γ : hSet}  (a : tm A) (b : tm A)
(e : # Ty (identity Γ) A = # Ty (Yo^-1 (γ b) ;; pi A) A) 
: tm_transportf e (reind_tm (identity _) a)
= tm_transportf ((Ty_identity _) @ e) a.
Proof.
  apply subtypePath.  
  -  intros x. apply (setproperty (Ty Γ : hSet)).
  -  apply ((toforallpaths _ _ _ (pr12 Tm _ )) a).
Qed.

Lemma Ty_γ_id {Γ : C} {A : Ty Γ : hSet} (a : tm A) 
: # Ty (Yo^-1 (γ a)) (# Ty (pi A) A) = A.
Proof.
  simple refine (!(Ty_composition _ _ _) @ _).
  apply (pathscomp0 ((toforallpaths  _ _ _ (maponpaths _ (γ_pi _)) )A)).
  apply ((toforallpaths _ _ _ (pr12 Ty _ )) A).
Qed.

Definition DepTypesType {Γ : C} {A : Ty Γ : hSet} (B : Ty(Γ.:A) : hSet)
(a : tm A)
: Ty Γ : hSet := ( γ a;;yy B : nat_trans _ _) Γ (identity Γ).

Definition DepTypesElem_pr1 {Γ : C} {A : Ty Γ : hSet} {B : Ty(Γ.:A) : hSet}
(b : tm B) (a : tm A) 
: Tm Γ : hSet := (γ a;;yy b : nat_trans _ _) Γ (identity Γ).

Lemma DepTypesComp {Γ : C} { A : Ty Γ : hSet} {B : Ty(Γ.:A) : hSet}
(b : tm B) (a : tm A)
: pp_  Γ (DepTypesElem_pr1 b a) = DepTypesType B a.
Proof.
  apply pathsinv0,(pathscomp0(maponpaths _ (!(pr2 b)))),pathsinv0,
  (toforallpaths _ _ _ (pr22 pp (Γ.:A) Γ ((γ a : nat_trans _ _ ) Γ (identity Γ))) b).
Qed.

Definition DepTypesElems {Γ : C} { A : Ty Γ : hSet} {B : Ty(Γ.:A) : hSet}
(b : tm B) (a : tm A)
: tm (DepTypesType B a) := DepTypesElem_pr1 b a ,, DepTypesComp b a.

Lemma DepTypesNat {Γ Δ : C} {A : Ty Γ : hSet} (B : Ty (Γ.: A) : hSet)
(f : C^op ⟦Γ,Δ⟧) (a : tm A)
: #Ty f (DepTypesType B a) = DepTypesType (#Ty (qq_term A f) B) (reind_tm f a).
Proof.
  unfold DepTypesType, reind_tm; rewrite yy_natural, assoc.
  assert (Fucn : (# (pr1 Ty) ((γ a :nat_trans _ _) Γ (identity Γ)) ;; # (pr1 Ty) f) B =
  # Ty f (# Ty ((γ a :nat_trans _ _) Γ (identity Γ)) B)) by auto.
  apply (pathscomp0 (!Fucn)),(pathscomp0(!((toforallpaths _ _ _  
  ((pr22 Ty) _ _ _ ((γ a: nat_trans _ _) Γ (identity Γ) : C⟦Γ,Γ.:A⟧) f)) B))), 
  (pathscomp0(toforallpaths _ _ _ (maponpaths (# Ty) (γNat f a)) B)).
  reflexivity.
Qed.

Lemma DepTypesEta {Γ : C} {A : Ty Γ : hSet} (B : Ty (Γ.:A) : hSet)
: DepTypesType (#Ty (qq_term A (pi A)) B) (te A) = B.
Proof.
  assert (Natu : @γ (Γ.:A) (#Ty (pi A) A) (te A) ;; yy (# Ty (qq_term A (pi A)) B)
  = @γ (Γ.:A) (#Ty (pi A) A) (te A) ;; #Yo (qq_term A (pi A)) ;; 
  (@yy (@pr1 _ _ C) (@pr2 _ _ C) Ty (Γ .: A)) B).
  -  rewrite (cancel_precomposition _ _ _ _ (yy (#Ty (qq_term A (pi A)) B))
     (#Yo (qq_term A (pi A));; yy B) _).
     *  rewrite assoc; reflexivity.
     *  rewrite yy_natural; reflexivity.
  -  assert (Id: @γ (Γ .: A) (# Ty (@pi Γ A) A) (te A) ;; #Yo (qq_term A (pi A))
     = identity _).
     *  refine (MorphismsIntoPullbackEqual
        (pr22(make_Pullback (yy A) pp
        (yoneda (pr1 CwF) (homset_property (pr1 CwF)) (Γ.:A))
        (# (yoneda (pr1 CwF) (homset_property (pr1 CwF))) (pi A))
        (yy (te A))
        (cwf_square_comm (te' A))
        (CwF_Pullback A)))
        (γ (te A) ;; #Yo (qq_term A (pi A))) (identity _) (γPullback2 A) (γPullback1 A)).
     *  rewrite Id, (id_left _) in Natu.
        unfold DepTypesType.
        rewrite Natu; exact (!(yyidentity B)).
Qed.

Lemma DepTypesrewrite {Γ : C} {A : Ty Γ : hSet} (B : Ty (Γ.:A) : hSet)
(a b : tm A) (e : pr1 a = pr1 b)
: DepTypesType B a = DepTypesType B b.
Proof.
  destruct a as [a pa]; destruct b as [b pb].
  cbn in e; induction e.
  assert (ProofIrr : pa = pb) by apply (setproperty( Ty Γ : hSet)).
  rewrite ProofIrr.
  reflexivity.
Qed.

End Familly_Of_Types.
End qq.

(** ** Pi Type over Category with famillies *)

Section Pi_structure.

Definition CwF_PiTypeFormer : UU 
:= ∏ (Γ : C) (A : Ty Γ : hSet) (B : Ty (Γ.:A) : hSet), (Ty Γ : hSet).

Definition CwF_PiTypeNat (π : CwF_PiTypeFormer) : UU 
:= ∏ (Γ Δ : C) (f : C^op ⟦Γ,Δ⟧) (A : Ty Γ : hSet) (B : Ty(Γ.:A) : hSet),
  reind_cwf (π _ A B) f  = π _ (reind_cwf A f) (reind_cwf B (qq_term A f)).

Definition CwF_pi_form_struct : UU
:= ∑ pi : CwF_PiTypeFormer, CwF_PiTypeNat pi.

Definition pr1_PiFormer (π : CwF_pi_form_struct) : CwF_PiTypeFormer := pr1 π.
Coercion pr1_PiFormer : CwF_pi_form_struct >-> CwF_PiTypeFormer.

Lemma ppComp3 {Γ Δ : C} {A : Ty Γ : hSet} (f : C^op ⟦Γ,Δ⟧) {π : CwF_PiTypeFormer}
(nπ : CwF_PiTypeNat π) {B : Ty (Γ.: A) : hSet} (c : tm (π _ A B))
: pp_ _ (# Tm f c)  = (π Δ (# Ty f A) (# Ty (qq_term A f) B)).
Proof.
  apply pathsinv0, (pathscomp0(!(nπ _ _ f A B))),
  (pathscomp0(!(maponpaths (# Ty f) (pr2 c)))),
   pathsinv0, (toforallpaths _ _ _ (pr22 pp _ _ f) c) .
Qed.

Definition CwF_PiAbs (π : CwF_PiTypeFormer): UU
:= ∏ (Γ : C) (A : Ty Γ : hSet) (B : Ty (Γ.:A) : hSet) (b : tm B), tm (π _ A B) .

Definition CwF_PiAbsNat (π : CwF_PiTypeFormer) (nπ : CwF_PiTypeNat π) (Λ : CwF_PiAbs π) 
: UU := ∏ (Γ Δ : C) (f : C^op ⟦ Γ, Δ ⟧) (A : Ty Γ : hSet)
(B : Ty (Γ .: A) : hSet) (b : tm B), reind_tm f (Λ Γ A B b) =
tm_transportf (! (! ppComp1 f (Λ Γ A B b) @ ppComp3 f nπ (Λ Γ A B b)))
(Λ Δ (# Ty f A) (# Ty (qq_term A f) B) (reind_tm (qq_term A f) b)).

Definition CwF_Pi_intro_struct (π : CwF_pi_form_struct) : UU
:= ∑ Λ : CwF_PiAbs π, CwF_PiAbsNat π (pr2 π) Λ.

Definition CwF_PiApp (π : CwF_PiTypeFormer) : UU
:= ∏ (Γ : C) (A : Ty Γ : hSet) (B : Ty(Γ.: A) : hSet) (c : tm (π _ A B)) (a : tm A),
tm (DepTypesType B a).

Definition CwF_PiAppNat  (π : CwF_PiTypeFormer) (nπ : CwF_PiTypeNat π) (app : CwF_PiApp π) : UU
:= ∏ (Γ Δ : C) (f : C^op ⟦Γ,Δ⟧) (A : Ty Γ : hSet) (B : Ty(Γ.: A) : hSet) 
(c : tm (π _ A B)) (a : tm A), 
reind_tm f (app _ _ _ c a) = (tm_transportf  (!(DepTypesNat B f a))
(app _ (#Ty f A) (# Ty (qq_term A f) B)
 (tm_transportf (nπ _ _ f A B) (reind_tm f c)) (reind_tm f a))).

Definition CwF_Pi_app_struct (π : CwF_pi_form_struct) : UU 
:= ∑ app : CwF_PiApp π, CwF_PiAppNat π (pr2 π) app.

Definition CwF_PiAppAbs (π : CwF_PiTypeFormer) (Λ : CwF_PiAbs π) (app : CwF_PiApp π)
:= ∏ Γ ( A : Ty Γ : hSet) (B : Ty(Γ.: A) : hSet) (b : tm B) (a : tm A),
app _ _ _ (Λ _ A _ b) a = DepTypesElems b a.

Definition CwF_Pi_comp_struct (π : CwF_pi_form_struct)
(lam : CwF_Pi_intro_struct π) (app : CwF_Pi_app_struct π) : UU
:= CwF_PiAppAbs π (pr1 lam) (pr1 app).

Definition CwF_PiAbsAppComp (π : CwF_PiTypeFormer) (nπ : CwF_PiTypeNat π)
(Λ : CwF_PiAbs π) (app : CwF_PiApp π) 
: UU
:= ∏ (Γ : C) (A : Ty Γ: hSet) (B : Ty (Γ .: A) : hSet) (c : tm (π Γ A B)),
c = Λ Γ A B (tm_transportf (DepTypesEta B)
(app (Γ .: A) (# Ty (pi A) A) (# Ty (qq_term A (pi A)) B)
(tm_transportf (nπ Γ (Γ .: A) (pi A) A B) (reind_tm (pi A) c)) (te A))).

End Pi_structure.

(** ** Sigma Type over Category with famillies *)
Section Sigma_structure.

Definition CwF_SigTypeFormer : UU 
:= ∏ (Γ : C) (A : Ty Γ : hSet) (B : Ty (Γ.:A) : hSet), Ty Γ : hSet.

Definition CwF_SigTypeNat (σ : CwF_SigTypeFormer) : UU 
:= ∏ (Γ Δ : C) (f : C^op ⟦Γ,Δ⟧) (A : Ty Γ : hSet) (B : Ty(Γ.:A) : hSet),
#Ty f (σ _ A B) = σ _ (#Ty f A) (#Ty (qq_term A f) B).

Definition CwF_SigAbs (σ : CwF_SigTypeFormer) : UU 
:= ∏ (Γ : C) (A : Ty Γ : hSet) (B : Ty(Γ.:A) : hSet) (a : tm A)
(b : tm (DepTypesType B a) ), tm (σ _ A B).

Definition CwF_SigAbsNat (σ : CwF_SigTypeFormer) (nσ : CwF_SigTypeNat σ)
(pair : CwF_SigAbs σ) 
: UU := ∏ (Γ Δ : C) (f : C^op ⟦ Γ, Δ ⟧) (A : Ty Γ : hSet) (B : Ty (Γ .: A) : hSet)
(a : tm A) (b : tm (DepTypesType B a)), reind_tm f (pair Γ A B a b) =
tm_transportf (! nσ Γ Δ f A B)
(pair Δ (# Ty f A) (# Ty (qq_term A f) B) (reind_tm f a)
(tm_transportf (DepTypesNat B f a) (reind_tm f b))).

Definition CwF_SigPr1 (σ : CwF_SigTypeFormer) : UU
:= ∏ Γ (A : Ty Γ : hSet) (B : Ty(Γ.:A) : hSet) (c: tm (σ _ A B)), tm A.

Definition CwF_SigPr1Nat (σ : CwF_SigTypeFormer) (nσ : CwF_SigTypeNat σ) (p1 : CwF_SigPr1 σ) : UU 
:= ∏ (Γ Δ : C)  (f : C^op ⟦Γ,Δ⟧) (A : Ty Γ : hSet) (B : Ty(Γ.:A) : hSet) (c : tm (σ _ A B)),
reind_tm f (p1 _ _ _ c) = 
p1 _ (#Ty f A) (#Ty (qq_term A f) B) (tm_transportf (nσ _ _ f _ _) (reind_tm f c)).
 
Definition CwF_SigPr2 (σ : CwF_SigTypeFormer) (p1 : CwF_SigPr1 σ) :UU
:= ∏ Γ (A : Ty Γ : hSet) (B : Ty(Γ.:A) : hSet)
(c : tm (σ _ A B) ), tm (DepTypesType B (p1 _ _ _ c)).

Definition CwF_SigPr2Nat (σ : CwF_SigTypeFormer) (nσ : CwF_SigTypeNat σ) (p1 : CwF_SigPr1 σ)
(np1 : CwF_SigPr1Nat σ nσ p1) (p2 : CwF_SigPr2 σ p1) 
: UU := ∏ (Γ Δ : C) (f : C^op ⟦ Γ, Δ ⟧) (A : Ty Γ : hSet) (B : Ty (Γ .: A) : hSet)
(c : tm (σ Γ A B)),
reind_tm f (p2 Γ A B c) = tm_transportf (! DepTypesNat B f (p1 Γ A B c))
(tm_transportf (DepTypesrewrite (# Ty (qq_term A f) B)
(p1 Δ (# Ty f A) (# Ty (qq_term A f) B) (tm_transportf (nσ Γ Δ f A B) (reind_tm f c)))
(reind_tm f (p1 Γ A B c)) (maponpaths pr1 (! np1 Γ Δ f A B c)))
(p2 Δ (# Ty f A) (# Ty (qq_term A f) B) (tm_transportf (nσ Γ Δ f A B) (reind_tm f c)))).

Definition CwF_SigAbsPr1 (σ : CwF_SigTypeFormer) (pair : CwF_SigAbs σ) (p1 : CwF_SigPr1 σ)
: UU := ∏ Γ (A : Ty Γ : hSet) (B : Ty(Γ.:A) : hSet) (a : tm A) (b : tm (DepTypesType B a)),
p1 _ _ _ (pair _  _ _ a b) = a.

Definition CwF_SigAbsPr2 (σ : CwF_SigTypeFormer) (pair : CwF_SigAbs σ) (p1 : CwF_SigPr1 σ)
(p2 : CwF_SigPr2 σ p1) (Ap1 : CwF_SigAbsPr1 σ pair p1)
: UU := ∏ (Γ : C^op) (A : Ty Γ : hSet) (B : Ty (Γ .: A) : hSet)
(a : tm A) (b : tm (DepTypesType B a)),
b = tm_transportf
(DepTypesrewrite B (p1 Γ A B (pair Γ A B a b)) a (maponpaths pr1 (Ap1 Γ A B a b)))
(p2 Γ A B (pair Γ A B a b)).

Definition CwF_SigAbsPr (σ : CwF_SigTypeFormer) (pair : CwF_SigAbs σ)
(p1 : CwF_SigPr1 σ) (p2 : CwF_SigPr2 σ p1) : UU
:= ∏ Γ (A : Ty Γ : hSet) (B : Ty(Γ.:A) : hSet) (c : tm (σ _ A B)),
pair _ _ _ (p1 _ _ _ c) (p2 _ _ _ c ) = c.

End Sigma_structure.

Section Identity_Structure.
  (** Identity Types over a Category with famillies *)

Definition CwF_IdTypeFormer : UU 
:= ∏ (Γ : C) (A : Ty Γ : hSet) (a b : tm A), Ty Γ : hSet.

Definition CwF_IdTypeNat (id : CwF_IdTypeFormer) : UU 
:= ∏ (Γ Δ : C) (f : C^op ⟦Γ,Δ⟧) (A : Ty Γ : hSet) (a b : tm A),
#Ty f (id _ A a b)  = id _ (#Ty f A) (reind_tm f a) (reind_tm f b).

Definition CwF_IdRefl (Id : CwF_IdTypeFormer) : UU 
:= ∏ Γ (A: Ty Γ :hSet) (a :tm A), tm (Id _ _ a a).

Definition CwF_IdReflNatContext (Id : CwF_IdTypeFormer) (nid : CwF_IdTypeNat Id)
(refl : CwF_IdRefl Id) : UU
:= ∏ (Γ Δ : C) (f : C^op ⟦Γ,Δ⟧) (A : Ty Γ : hSet) (a : tm A),
reind_tm f (refl _ A a) =
tm_transportf (!(nid _ _ f _ a a)) (refl _ (#Ty f A) (reind_tm f a)).

Definition CwF_maponpathsIdForm {Id : CwF_IdTypeFormer}
{Γ} {A A'} (e_A : A = A')
{a} {a'} (e_a : a = tm_transportb e_A a')
{b} {b'} (e_b : b = tm_transportb e_A b')
: Id Γ A a b = Id Γ A' a' b'.
Proof.
  destruct e_A.
  rewrite (tm_transportbf _) in e_a, e_b;
   cbn in e_a, e_b.
  apply Auxiliary.maponpaths_12; assumption.
Qed.

Definition CwF_IdBasedFam (Id : CwF_IdTypeFormer) {Γ : C} (A : Ty Γ : hSet) (a : tm A)
: Ty (Γ.:A) : hSet := Id _ _ (reind_tm _ a) (te A).

Definition CwF_IdBasedFamNatural (Id : CwF_IdTypeFormer) (nid : CwF_IdTypeNat Id)
{Γ Δ : C} (f : C^op ⟦Γ,Δ⟧) (A : Ty Γ : hSet) (a : tm A)
: #Ty (qq_term A f) (CwF_IdBasedFam Id A a) = CwF_IdBasedFam Id _ (reind_tm f a).
Proof.
  unfold CwF_IdBasedFam.
  etrans.
  -  exact (nid _ _ (qq_term A f) _ _ _).
  -  use CwF_maponpathsIdForm.
     --  refine (!(Ty_composition _ _ A) @ _).
         apply pathsinv0, (pathscomp0 (!(Ty_composition _ _ A))).
         refine ((toforallpaths _ _ _ _) A).
         exact (maponpaths _ (qq_term_pullback _ _)).
     --  etrans. {apply pathsinv0, tm_transport_compose. }
         etrans. 2: { apply maponpaths, tm_transport_compose. }
         etrans. 2: {rewrite tm_transportbf; apply  tm_transportf_compose. }
         etrans. {eapply maponpaths. refine (maponpaths_2_reind_tm _ _). 
         apply (!(qq_term_pullback _ _)). }
         etrans. { rewrite tm_transportbf; apply (!(tm_transportf_compose _ _ _)). }
         apply tm_transportf_irrelevant.
     --  apply subtypePath; [intro x; apply (setproperty (Ty _ : hSet))|
         rewrite tm_transportbf ;apply qq_term_te].
Qed.

Definition CwF_Id_map {Id} (nid : CwF_IdTypeNat Id) {Γ} {A : Ty Γ : hSet} (a : tm A) (b : tm A) (eqab : tm (Id _ _ a b))
: C⟦Γ,_.:CwF_IdBasedFam Id A a⟧.
Proof.
  simple refine (γ_qq (Yo^-1 (γ b)) _). unfold CwF_IdBasedFam.
  simple refine (tm_transportb _ eqab).
  abstract(
  simple refine (nid  _ _ _ _ _ _ @ _);
  use CwF_maponpathsIdForm;
  [ apply Ty_γ_id
  | rewrite tm_transportbf ;
    refine (_ @ tm_transportf_irrelevant _ _ _);
    simple refine (tm_transportf_bind (!reind_compose_tm' _ _ _) _);
    [ apply (pathscomp0 (!(Ty_γ_id b))) , (!(Ty_composition _ _ _)) |
      simple refine (maponpaths_2_reind_tm _ _ @ _);
      [exact (identity _) | apply γ_pi |
      rewrite tm_transportbf; apply (pathscomp0 (reind_id_tm' _ _ _));
      apply tm_transportf_irrelevant ]]
  | apply subtypePath;
    [  intros x; apply (setproperty (Ty Γ : hSet))
     | rewrite tm_transportbf; apply te_subtitution]]).
Defined.

Definition CwF_IdBased_path_inducton {Id} (nid : CwF_IdTypeNat Id) (refl : CwF_IdRefl Id) := ∏ Γ (A : Ty Γ : hSet) (a : tm A)
(P : Ty (_ .: CwF_IdBasedFam Id A a) :  hSet)
(d : tm  (#Ty (CwF_Id_map nid a a (refl _ _ a)) P))
(b : tm A) (eqab : tm (Id _ _ a b)), 
tm (#Ty (CwF_Id_map nid a b eqab) P).

End Identity_Structure.
End Fix_Category.
