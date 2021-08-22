(**
Content :
- Some lemma on Yoneda
- Famillies of Types in CwF (DepTypes prefixe mostly)
- Pi Types in CwF (CwF_Pi prefixe)
- Sigma Types in CwF (CwF_Sig prefixe)
- Identity Types in CwF (CwF_Id prefixe)

**)

Require Import UniMath.Foundations.Sets.
Require Import TypeTheory.Auxiliary.CategoryTheoryImports.

Require Import TypeTheory.Auxiliary.Auxiliary.
Require Import TypeTheory.ALV1.RelativeUniverses.
Require Import TypeTheory.ALV1.Transport_along_Equivs.
Require Import TypeTheory.ALV1.RelUnivYonedaCompletion.
Require Import TypeTheory.ALV1.CwF_def.
Require Import TypeTheory.ALV1.CwF_SplitTypeCat_Defs.
Require Import TypeTheory.ALV1.CwF_SplitTypeCat_Maps.

Section Fix_Category.
(** * Preliminaries *)
  
(** General context for a category with famillies and some usefull notations *)  
Context {CwF : cwf}.
Definition C : category := pr1(CwF).
Definition pp : mor_total(preShv(C)) := pr1(pr2(CwF)).
Definition Ty : functor _ _ := target pp.
Definition Tm : functor _ _ := source pp.
(* extension of context *)
Definition ext {Γ : C} (A : Ty Γ : hSet) : C := pr1(pr1(pr2(pr2(CwF)) Γ A)).
Notation "Γ.: A" :=  (ext A) (at level 24).

Definition pi {Γ :C} (A : Ty Γ : hSet) : C⟦Γ.:A,Γ⟧ := pr2 (pr1 (pr2 (pr2 CwF) _ A)).
Definition te {Γ :C} (A : Ty Γ : hSet) : Tm (Γ.: A) : hSet :=
  pr1(pr1(pr2((pr2(pr2(CwF)) _ A)))).
(* proof of pp (te A) = Ty (pi A) A*)
Definition te' {Γ :C} (A : Ty Γ : hSet) := pr2 (pr1 (pr2 (pr2 (pr2 CwF) Γ A))).
(* just a simple to use pp as a nat_trans *)
Definition Nat_trans_morp {C : category} (Γ : C) (p : mor_total(preShv C)) :=
  (pr1(pr2(p)) Γ).
Notation "p __: Γ" := (Nat_trans_morp Γ p)  (at level 24).
Definition pp_ (Γ :C)  : ((Tm Γ : hSet) → (Ty Γ : hSet)) := pp __: Γ.

Section Auxiliary.

Lemma hSetProofIrr {S : hSet} {A B : S} (a b : A = B) : a = b.
Proof using.
apply setproperty.
Qed.

(** * Few usefull lemma on yoneda **)

Lemma yonedainv {A B : C} (f : C⟦A,B⟧) : Yo^-1 (#Yo f) = f.
Proof.
   cbn; unfold yoneda_morphisms_data;
   rewrite (pr1(pr1(pr2(pr1 C)))); reflexivity.
Qed.


Lemma transportyo {A B : C} {f g : C⟦A,B⟧} (e : #Yo f = #Yo g):  f = g.
Proof.
  eapply pathscomp0.
  apply (!(yonedainv f)).
  apply pathsinv0.
  eapply pathscomp0.
  apply (!(yonedainv g)).
  apply (!(maponpaths (Yo^-1) e)).
Qed.

Lemma yonedacarac {Γ Δ : C} (f  : _ ⟦Yo Γ,Yo Δ⟧) :
  # Yo ((f :nat_trans _ _) Γ (identity Γ)) = f.
Proof.
  assert ((# Yo ((f : nat_trans _ _) Γ (identity Γ)) : nat_trans _ _) Γ (identity Γ)
          = (f : nat_trans _ _) Γ (identity Γ)).
  cbn. unfold yoneda_morphisms_data. rewrite (pr1(pr1(pr2(pr1 (C)))) Γ). reflexivity.
  assert ((f : nat_trans _ _) Γ (identity Γ) = yoneda_map_1 C (pr2 C) Γ (Yo(Δ)) f).
  unfold yoneda_map_1.
  reflexivity.
  assert (# Yo ((f : nat_trans _ _) Γ (identity Γ)) = yoneda_map_2 C (pr2 C) Γ (Yo(Δ))
         ((f : nat_trans _ _) Γ (identity Γ))).                                      
  unfold yoneda_map_2. cbn. unfold yoneda_morphisms. unfold yoneda_morphisms_data.
  cbn.
  Search "nat_trans_eq".
  assert ((is_nat_trans_yoneda_morphisms_data C (homset_property C) Γ Δ
         ((f :nat_trans _ _) Γ (identity Γ)))
          = (yoneda_map_2_ax C (pr2 C) Γ (yoneda_objects C (homset_property C) Δ)
            ((f : nat_trans _ _) Γ (identity Γ)))).
  assert (isaprop(is_nat_trans (yoneda_objects C (homset_property C) Γ)
         (yoneda_objects C (homset_property C) Δ)
         (yoneda_morphisms_data C (homset_property C) Γ Δ
         ((f : nat_trans _ _) Γ (identity Γ))))).
  apply isaprop_is_nat_trans.
  exact (pr2 hset_category).
  exact (pr1 (X1 _ _)).
  apply pair_path_in2.
  refine X1.
  rewrite X1.
  rewrite X0.
  apply yoneda_map_1_2.
Qed.

Lemma yyidentity {Γ : C} {A : Ty Γ : hSet} (B : Ty (Γ.:A) : hSet) :
  B = ((@yy (pr1 C) (pr2 C) Ty (Γ.:A) B : nat_trans _ _) (Γ.:A) (identity (Γ.:A))).
Proof.
cbn.
apply pathsinv0. eapply pathscomp0.
apply (toforallpaths _ (# Ty (identity (Γ.:A))) (identity (Ty (Γ.:A)))
                     (functor_id Ty (Γ.:A))).
cbn;
reflexivity.
Qed.

(** morphism between contexts *)

Let Xk {Γ :C} (A : Ty Γ : hSet) :=
  make_Pullback _ _ _ _ _ _ ( pr2(pr2 ( (pr2 (pr2 ( CwF))) Γ A))).

Definition qq_yoneda {Γ  Δ :C} (A : Ty Γ : hSet) (f : C^op ⟦Γ,Δ⟧) :
  _ ⟦Yo (Γ.: (# Ty f A)), Yo (Γ.: A) ⟧.
Proof.
use (PullbackArrow (Xk A)).
  - apply (#Yo (pi _) ;; #Yo f ). 
  - apply (yy(te _)).
  - abstract (
        clear Xk;

        assert (XT :=(cwf_square_comm (pr2 (pr1 (pr2 (pr2 (pr2 CwF) Δ (#Ty f A) ))))));
        eapply pathscomp0; try apply XT; clear XT;
        rewrite <- assoc; apply maponpaths;
        apply pathsinv0, yy_natural
    ).
Defined.

Lemma qq_yoneda_commutes {Γ Δ: C} (A : Ty Γ : hSet) (f : C^op ⟦Γ,Δ⟧) :
  (qq_yoneda A f) ;; yy(te A) = yy(te _) .
Proof.
  apply (PullbackArrow_PullbackPr2 (Xk A)).
Qed.

Definition qq_term {Γ  Δ :C} (A : Ty Γ : hSet) (f : C^op ⟦Γ,Δ⟧) :
  _ ⟦Γ.: (# Ty f A) , Γ.: A⟧.
Proof.
  apply (invweq (make_weq _ (yoneda_fully_faithful _ (homset_property _) _ _ ))) ,
  (qq_yoneda A f).
Defined.

Definition qq_yoneda_compatibility {Γ  Δ :C} (A : Ty Γ : hSet) (f : C^op ⟦Γ,Δ⟧) :
 #Yo(qq_term A f) = qq_yoneda A f.
Proof.
  assert (XT := homotweqinvweq
     (make_weq _ (yoneda_fully_faithful _ (homset_property _) (Γ.:(#Ty f A)) (Γ.:A)))).
  apply XT.
Qed.

Lemma ppComp1 {Γ Δ : C} {A : Ty Γ : hSet} (f : C^op ⟦Γ,Δ⟧) (a : Tm Γ : hSet)
    (pa : pp_ _ a = A) :
  pp_ _ (# Tm f a ) = # Ty f A. 
Proof.
  apply pathsinv0, (pathscomp0(pathsinv0(maponpaths (# Ty f) pa))),
  pathsinv0, (toforallpaths _ _ _ ((pr2(pr2(pp))) _ _ f) a) .
Qed.


Lemma ppComp2 {Γ Δ : C} {A : Ty Γ : hSet}
      (B : Ty (Γ.: A) : hSet) (f : C^op ⟦Γ,Δ⟧) (b : Tm (Γ.:A) : hSet) (pb : pp_ _ b = B) :
  pp_ _ (# Tm (qq_term A f) b) = #  Ty (qq_term A f) B.
Proof.

  apply pathsinv0, (pathscomp0(pathsinv0(maponpaths (# Ty (qq_term A f)) pb))),
  pathsinv0, (toforallpaths _ _ _ ((pr2(pr2(pp))) _ _ ( qq_term A f)) b) .
Qed.


(*(** Preimage of a function between sets **)
Definition preimage {A : hSet} {B : hSet} (f : A -> B) (b: B) : UU
  := (∑(a : A), (f(a) =  b)) .
Notation "f @^-1: b" := (preimage f b) (at level 24).*)

(** Famillies of types in a Category with famillies**)
Lemma Pullback_commu {Γ : C} {A : Ty Γ : hSet} (a : Tm Γ : hSet) (pa : pp_ _ a = A):
  (identity (Yo Γ)) ;; (yy(A)) = (yy(a);;pp).
Proof.
  apply pathsinv0, (pathscomp0(yy_comp_nat_trans Tm Ty pp Γ (a))) ,pathsinv0,
  (pathscomp0(pr1(pr1(pr2(pr1(preShv (C))))) (Yo Γ) Ty  (yy(A)))) ,
  ((maponpaths(yy)) (pathsinv0(pa))).
Qed.

Definition γ {Γ : C} {A : Ty Γ : hSet} (a : Tm Γ : hSet) (pa : pp_ _ a = A) :=
  pr1(pr1(((pr2(pr2 ( (pr2 (pr2 ( CwF))) Γ A))) (Yo Γ) (identity (Yo Γ))
  (yy(a)) (Pullback_commu a pa )))).

Lemma  γ_pull {Γ : C} (A : Ty Γ : hSet) :
  γ (te A) (te' A) ;; yy (te (#Ty (pi A) A)) = yy(te A).
Proof.
  rewrite <- (pr2(pr2(pr1 (pr2 (pr2 (pr2 (pr2 CwF) (Γ.:A) (#Ty (pi A) A)))
                              (Yo (Γ.:A)) (identity (Yo (Γ.:A))) (yy (te A))
                              (Pullback_commu (te A) (te' A)))))).
  auto.
Qed.

Lemma γNat {Γ Δ : C} {A : Ty Γ : hSet} (f : C^op ⟦Γ,Δ⟧) (a : Tm Γ : hSet) (pa : pp_ _ a = A) :
  (f : C⟦Δ,Γ⟧) ;; (γ a pa : nat_trans _ _) Γ (identity Γ) =
  (γ (#Tm f a) (ppComp1 f a pa) ;; #Yo (qq_term A f) : nat_trans _ _) Δ (identity Δ).
Proof.
  assert (#Yo ((f : C⟦Δ,Γ⟧) ;; (γ a pa : nat_trans _ _) Γ (identity Γ)) =
     #Yo((γ (#Tm f a) (ppComp1 f a pa) : nat_trans _ _) Δ (identity Δ) ;; qq_term A f)).
rewrite (pr2 (pr2 (yoneda C (pr2 C))) _ _ _).
rewrite yonedacarac.
rewrite (pr2 (pr2 (yoneda C (pr2 C))) _ _ _).
rewrite yonedacarac.
refine (MorphismsIntoPullbackEqual (pr2 (pr2 (pr2 (pr2 CwF) Γ A)))
(#Yo f ;; γ a pa) (γ (#Tm f a) (ppComp1 f a pa) ;; #Yo (qq_term A f)) _ _).
rewrite <- assoc.
eapply pathscomp0.
rewrite (cancel_precomposition _ _ _ _ _ _ _
(pr1(pr2(pr1(((pr2(pr2 ( (pr2 (pr2 ( CwF))) Γ A)))
(Yo Γ) (identity (Yo Γ)) (yy(a)) (Pullback_commu a pa ))))))).
refine (pr2 (pr1(pr2 (pr1 (preShv(C))))) _ (Yo Γ) (#Yo f)).
rewrite qq_yoneda_compatibility.
rewrite <- assoc.
apply pathsinv0.
eapply pathscomp0.
rewrite (cancel_precomposition _ _ _ _ _ _ _
(pr1(pr2(pr1(pr2(pr2(Xk A))
(Yo (Γ.: # Ty f A)) (# Yo (pi (#Ty f A));; # Yo f)
(yy (te (#Ty f A))) (qq_yoneda_subproof Γ Δ A f)))))).
rewrite assoc.
rewrite  (cancel_postcomposition _ _ _
(pr1(pr2(pr1(((pr2(pr2((pr2 (pr2 ( CwF))) Δ (#Ty f A)))) (Yo Δ) (identity (Yo Δ))
(yy((#Tm f a))) (Pullback_commu (#Tm f a) (ppComp1 f a pa) ))))))).
refine (pr1 (pr1(pr2 (pr1 (preShv(C))))) _ (Yo Γ) (#Yo f)).
reflexivity.
rewrite <- assoc.
eapply pathscomp0.
rewrite (cancel_precomposition _ _ _ _ _ _ _
(pr2(pr2(pr1(((pr2(pr2 ( (pr2 (pr2 ( CwF))) Γ A))) (Yo Γ)
(identity (Yo Γ)) (yy(a)) (Pullback_commu a pa ))))))).
reflexivity.
rewrite qq_yoneda_compatibility.
rewrite <- assoc.
apply pathsinv0.
eapply pathscomp0.
rewrite (cancel_precomposition _ _ _ _ _ _ _ (pr2(pr2(pr1(pr2(pr2(Xk A))
(Yo (Γ.: # Ty f A)) (# Yo (pi (#Ty f A));; # Yo f) (yy (te (#Ty f A)))
(qq_yoneda_subproof Γ Δ A f)))))).
refine (pr2(pr2(pr1(((pr2(pr2 ( (pr2 (pr2 ( CwF))) Δ (#Ty f A))))
(Yo Δ) (identity (Yo Δ)) (yy((#Tm f a))) (Pullback_commu (#Tm f a) (ppComp1 f a pa))))))).
apply yy_natural.
apply (transportyo X).
Qed.

Lemma γPullback1 {Γ :C} (A : Ty Γ : hSet)
  : ( γ (te A) (te' A) ;; #Yo (qq_term A (pi A)) ;; yy( te A) =
      identity (Yo (Γ.:A));; yy (te A)).
Proof.
  rewrite (pr1(pr1(pr2(pr1(preShv C))))).
  assert (γ (te A) (te' A) ;; yy ( te (# Ty (pi A) A)) = yy( te A)).
  rewrite <- (pr2(pr2(pr1 (pr2 (pr2 (pr2 (pr2 CwF) (Γ.:A) (#Ty (pi A) A)))
                              (Yo (Γ.:A)) (identity (Yo (Γ.:A))) (yy (te A))
                              (Pullback_commu (te A) (te' A)))))).
  auto.
  rewrite (qq_yoneda_compatibility A (pi A)).
  rewrite <- assoc.
  rewrite <- X.
  refine (cancel_precomposition _ _ _ _ _ _ _ _).
  rewrite X.
  refine (qq_yoneda_commutes A (pi A)).
Qed.

Lemma  γPullback2 {Γ :C} (A : Ty Γ : hSet)
  : ( γ (te A) (te' A) ;; #Yo (qq_term A (pi A)) ;; #Yo (pi A) =
      identity (Yo (Γ.:A));;(#Yo (pi A))).
Proof.
  assert  (#Yo (pi (#Ty (pi A) A) ) ;; #Yo (pi A) =qq_yoneda A (pi A) ;; #Yo (pi A)).
  rewrite <- (pr1(pr2(pr1((pr2(pr2(make_Pullback (yy A) (pr1 (pr2 CwF))
          (yoneda (pr1 CwF) (homset_property (pr1 CwF))
          (pr1 (pr1 (pr2 (pr2 CwF) Γ A))))
          (# (yoneda (pr1 CwF) (homset_property (pr1 CwF)))
          (pr2 (pr1 (pr2 (pr2 CwF) Γ A))))
          (yy (pr1 (pr1 (pr2 (pr2 (pr2 CwF) Γ A)))))
          (cwf_square_comm (pr2 (pr1 (pr2 (pr2 (pr2 CwF) Γ A)))))
          (pr2 (pr2 (pr2 (pr2 CwF) Γ A)))))) (Yo (Γ.: (#Ty (pi A) A)))
          (#Yo (pi (#Ty (pi A) A)) ;; #Yo (pi A)) (yy (te (#Ty (pi A) A)))
          (qq_yoneda_subproof Γ (Γ.: A) A (pi A)))))).           
  auto.         
  rewrite (qq_yoneda_compatibility A (pi A)).
  rewrite <- assoc.
  assert (γ (te A) (te' A) ;; #Yo (pi (#Ty (pi A) A)) = identity _).
  apply pathsinv0.
  eapply pathscomp0.
  exact (pathsinv0(pr1(pr2(pr1 (pr2 (pr2 (pr2 (pr2 CwF) (Γ.:A) (#Ty (pi A) A)))
        (Yo (Γ.:A)) (identity (Yo (Γ.:A))) (yy (te A))
        (Pullback_commu (te A) (te' A))))))).
  auto.
  eapply pathscomp0.
  exact (cancel_precomposition _ _ _ _ _ _ (γ (te A) (te' A)) (!X)).
  rewrite assoc.
  eapply pathscomp0.
  exact (cancel_postcomposition _ _ _ (X0)).
  reflexivity.
Qed.

Definition DepTypesType {Γ : C } {A : Ty Γ : hSet} (B : Ty(Γ.:A) : hSet)
(a : Tm Γ : hSet) (pa : pp_ _ a = A) : Ty Γ :hSet :=
  (((γ a pa);;yy(B)) : nat_trans _ _) Γ (identity(Γ)).

Definition DepTypesElem {Γ : C } { A : Ty Γ :hSet}
           (b : Tm (Γ.:A) : hSet) (a : Tm Γ : hSet) (pa : pp_ _ a = A) : Tm Γ :hSet :=
  (((γ a pa);;yy(b)) : nat_trans _ _) Γ (identity (Γ)).

Lemma DepTypesComp {Γ : C } { A : Ty Γ :hSet} { B : Ty(Γ.:A) : hSet}
      (b : Tm (Γ.:A) : hSet) (pb : pp_ _ b = B) (a : Tm Γ : hSet) (pa : pp_ _ a = A)
  : pp_  Γ (DepTypesElem b a pa) = DepTypesType B a pa.
Proof.
  apply pathsinv0,  (pathscomp0((maponpaths(_))(pathsinv0(pb)))), pathsinv0,
  (toforallpaths _ _ _ (pr2(pr2(pp)) (Γ.:A) (Γ)
  (((γ a pa) : nat_trans _ _ ) Γ (identity Γ))) (b)).
Qed.

(*Definition DepTypes_compatibility {Γ : C } { A : Ty Γ :hSet} { B : Ty(Γ.:A) : hSet}
           (b : Tm (Γ.:A) : hSet) (pb : pp_ _ b = B) (a : Tm Γ : hSet) (pa : pp_ _ a = A) :
  preimage ((pp_ (Γ))) (DepTypes_application B a pa) := (DepTypes_elements b a pa) ,, (DepTypes_compatibility_data b pb a pa).*)

Definition deptype_struct : UU.
  Proof.
    use (∑ (D : ∏ Γ (a : Tm Γ : hSet), Ty Γ : hSet), _).
    use (∏ Δ Γ (f : C ⟦ Δ, Γ ⟧) (a : Tm Γ : hSet), _).
    refine (#Ty f (D Γ a) = D Δ (#Tm f a)).
  Defined.


Lemma DepTypesNat {Γ Δ : C} {A : Ty Γ : hSet}
      (B : Ty (Γ.: A) : hSet) (f : C^op ⟦Γ,Δ⟧) (a : Tm Γ : hSet)
      (pa : pp_ _ a = A) (pa' : pp_ _ (#Tm f a) = (#Ty f A)) :
  # Ty f (DepTypesType B a pa) =
  DepTypesType (# Ty (qq_term A f) B) (#Tm f a) pa'.
Proof.
  unfold DepTypesType.
  rewrite yy_natural.
  rewrite assoc.
  cbn.
  assert ((# (pr1 Ty) ((γ a pa :nat_trans _ _) Γ (identity Γ)) ;; # (pr1 Ty) f) B =
          # Ty f (# Ty ((γ a pa :nat_trans _ _) Γ (identity Γ)) B)).
  auto.
  eapply pathscomp0.
  exact (!X).
  destruct X.
  eapply pathscomp0.
  exact (! ((toforallpaths _ _ _  (pr2 (pr2 Ty) _ _ _ ((γ a pa : nat_trans _ _) Γ
        (identity Γ) : C⟦Γ,Γ.:A⟧) f)) B)).
  cbn.
  eapply pathscomp0.
  exact (toforallpaths _ _ _ (maponpaths (# Ty) (γNat f a pa)) B).
  cbn.
  assert ((ppComp1 f a pa) = pa').
  apply hSetProofIrr.
  rewrite X.
  reflexivity.
Qed.

Lemma DepTypesEta {Γ :C} {A : Ty Γ : hSet} (B : Ty (Γ.:A) : hSet)
  : DepTypesType (# Ty (qq_term A (pi A)) B) (te A) (te' A) = B.
Proof.
     assert ( (@γ (Γ.:A) (#Ty (pi A) A) (te A) (te' A) ;; yy (# Ty (qq_term A (pi A)) B))
      = (@γ (Γ.:A) (#Ty (pi A) A) (te A) (te' A) ;; #Yo (qq_term A (pi A)) ;;  yy  B)).
     - rewrite (cancel_precomposition _ _ _ _ (yy (#Ty (qq_term A (pi A)) B))
                                      (#Yo (qq_term A (pi A));; yy B) _).
       rewrite assoc.
       reflexivity.
       rewrite yy_natural.
       reflexivity.
     - 
       assert ( @γ (Γ.:A) (#Ty (pi A) A) (te A) (te' A) ;; #Yo (qq_term A (pi A))
                = identity (Yo (Γ.:A))).
       refine (MorphismsIntoPullbackEqual
        (pr2(pr2(make_Pullback (yy A) (pr1 (pr2 CwF))
        (yoneda (pr1 CwF) (homset_property (pr1 CwF))
        (pr1 (pr1 (pr2 (pr2 CwF) Γ A))))
        (# (yoneda (pr1 CwF) (homset_property (pr1 CwF)))
           (pr2 (pr1 (pr2 (pr2 CwF) Γ A))))
        (yy (pr1 (pr1 (pr2 (pr2 (pr2 CwF) Γ A)))))
        (cwf_square_comm (pr2 (pr1 (pr2 (pr2 (pr2 CwF) Γ A)))))
        (pr2 (pr2 (pr2 (pr2 CwF) Γ A))))))
        (γ (te A) (te' A);; #Yo (qq_term A (pi A))) (identity (Yo (Γ.:A))) _ _ ).
       assert (pr1(pr2(pr1(make_Pullback (yy A) (pr1 (pr2 CwF))
       (yoneda (pr1 CwF) (homset_property (pr1 CwF)) (pr1 (pr1 (pr2 (pr2 CwF) Γ A))))
       (# (yoneda (pr1 CwF) (homset_property (pr1 CwF)))
       (pr2 (pr1 (pr2 (pr2 CwF) Γ A))))
       (yy (pr1 (pr1 (pr2 (pr2 (pr2 CwF) Γ A)))))
       (cwf_square_comm (pr2 (pr1 (pr2 (pr2 (pr2 CwF) Γ A)))))
       (pr2 (pr2 (pr2 (pr2 CwF) Γ A)))))) = #Yo (pi A)).
       auto.
       rewrite X0.
       eapply pathscomp0.
       exact (γPullback2 A).
       reflexivity.
       assert (pr2(pr2(pr1(make_Pullback (yy A) (pr1 (pr2 CwF))
       (yoneda (pr1 CwF) (homset_property (pr1 CwF))
       (pr1 (pr1 (pr2 (pr2 CwF) Γ A))))
       (# (yoneda (pr1 CwF) (homset_property (pr1 CwF)))
       (pr2 (pr1 (pr2 (pr2 CwF) Γ A))))
       (yy (pr1 (pr1 (pr2 (pr2 (pr2 CwF) Γ A)))))
       (cwf_square_comm (pr2 (pr1 (pr2 (pr2 (pr2 CwF) Γ A)))))
       (pr2 (pr2 (pr2 (pr2 CwF) Γ A)))))) = yy(te A)).
       auto.
       rewrite X0.
       eapply pathscomp0.
       exact (γPullback1 A).
       reflexivity.
       rewrite X0 in X.
       rewrite (pr1(pr1(pr2(pr1(preShv C))))) in X.
       unfold DepTypesType.
       rewrite X. exact (pathsinv0(yyidentity B)).
Qed.

Lemma DepTypesrewrite {Γ : C} {A : Ty Γ : hSet} (B : Ty (Γ.:A) : hSet)
      (a b : Tm Γ : hSet) (pa : pp_ _ a = A) (pb : pp_ _ b = A) (e : a = b) :
  DepTypesType B a pa = DepTypesType B b pb.
Proof.
induction e.
assert (pa = pb).  
apply hSetProofIrr.
rewrite X.
reflexivity.
Qed.


End Auxiliary.




(** ** Pi Type over Category with famillies *)

Section Pi_structure.

Definition CwF_PiTypeFormer : UU :=
    ∏ (Γ :C) (A: Ty Γ :hSet) (B: Ty (Γ.:A) : hSet), (Ty Γ : hSet).

Definition CwF_PiTypeNat (π : CwF_PiTypeFormer) : UU :=
  ∏ (Γ Δ:C) (f : C^op ⟦Γ,Δ⟧) (A : Ty Γ : hSet) (B : Ty(Γ.:A) : hSet),
  #Ty f (π _ A B) = π _ (#Ty f A) (#Ty (qq_term A f) B).

Definition CwF_pi_form_struct : UU
  := ∑ (pi : CwF_PiTypeFormer), CwF_PiTypeNat pi.

Lemma ppComp3 {Γ Δ : C} {A: Ty Γ : hSet} (f : C^op ⟦Γ,Δ⟧) (π : CwF_PiTypeFormer)
(nπ : CwF_PiTypeNat π)
(B : Ty (Γ.: A) : hSet) (c : Tm Γ : hSet) (pc : pp_ _ c = π _ A B):
  pp_ _ (# Tm f c)  = (π Δ (# Ty f A) (# Ty (qq_term A f) B)).
Proof.
  apply pathsinv0, (pathscomp0(pathsinv0(nπ _ _ f A B))),
  (pathscomp0(pathsinv0(maponpaths (# Ty f) pc))),
   pathsinv0, (toforallpaths _ _ _ ((pr2(pr2(pp))) _ _ f) c) .
Qed.

Definition CwF_PiAbsContext : UU :=
  ∏ (Γ :C) (A: Ty Γ : hSet)  (b : Tm (Γ.:A) : hSet), (Tm Γ : hSet).

Definition CwF_PiAbsType : UU := ∏ (Γ :C) (A: Ty Γ : hSet) (B : Ty(Γ.: A) : hSet)
(π : CwF_PiTypeFormer) (Λ : CwF_PiAbsContext)
(b : Tm (Γ.:A) : hSet) (pb : pp_ _ b = B),
pp_ _ (Λ Γ A b) = π _ A B.

Definition CwF_PiAbsNat (Λ : CwF_PiAbsContext) : UU :=
  ∏ (Γ Δ:C) (f : C^op ⟦Γ,Δ⟧) (A : Ty Γ : hSet) (b : Tm (Γ.:A) : hSet),
  (# Tm f (Λ _ A  b))  = Λ Δ (#Ty f A) (#Tm (qq_term A f) b).

Definition CwF_PiAbsNatType (Λ : CwF_PiAbsContext) (tΛ : CwF_PiAbsType)
(π : CwF_PiTypeFormer) (tπ : CwF_PiTypeNat π)
{Γ Δ : C} (f : C^op ⟦Γ,Δ⟧) (A: Ty Γ : hSet) (B : Ty (Γ.:A) : hSet)
(b : Tm (Γ.:A) : hSet) (pb : pp_ _ b = B) :   
pp_ _ (# Tm f (Λ _ A  b)) = pp_ _ (Λ Δ (#Ty f A) (#Tm (qq_term A f) b)).
Proof.
  rewrite (ppComp1 f (Λ _ A b) (tΛ _ A B π Λ b pb)).
  rewrite (tΛ _ (#Ty f A) (#Ty (qq_term A f) B) π Λ
           (#Tm (qq_term A f) b) (ppComp2 _ _ _ pb)).
  apply tπ.
Qed.

Definition CwF_Pi_intro_struct : UU :=
  ∑ (Λ : CwF_PiAbsContext) (tΛ : CwF_PiAbsType), (CwF_PiAbsNat Λ).

Definition CwF_PiAppContext : UU :=
  ∏ (Γ : C) (c : Tm Γ : hSet) (a : Tm Γ : hSet),
  Tm Γ : hSet.

Definition CwF_PiAppType : UU :=
  ∏ (Γ : C) (A : Ty Γ : hSet) (B : Ty(Γ.: A) : hSet)
    (π : CwF_PiTypeFormer) (app : CwF_PiAppContext)
    (c : Tm Γ : hSet) (a : Tm Γ : hSet)
    (pc : pp_ _ c = (π _ A B)) (pa : pp_ _ a = A),
  pp_ _ (app _ c a) = DepTypesType B a pa.

Definition CwF_PiAppNat  (app : CwF_PiAppContext) : UU   :=
  ∏ (Γ Δ:C) (f : C^op ⟦Γ,Δ⟧) (c : Tm Γ : hSet) (a : Tm Γ : hSet) ,
  # Tm f (app _ c a) = app _ (#Tm f c) (#Tm f a).

Definition CwF_PiAppNatType (app : CwF_PiAppContext) (tapp : CwF_PiAppType)
           (π : CwF_PiTypeFormer) (tπ : CwF_PiTypeNat π)
{Γ Δ : C} (f : C^op ⟦Γ,Δ⟧) (A: Ty Γ : hSet) (B : Ty (Γ.:A) : hSet)
(c : Tm Γ : hSet) (pc : pp_ _ c = π _ A B) (a : Tm Γ : hSet) (pa : pp_ _ a = A) :  
pp_ _ (# Tm f (app _ c a)) = pp_ _ (app _ (#Tm f c) (#Tm f a)).
Proof.
rewrite (ppComp1 f _ (tapp _ _ _ π app c a pc pa)).
assert  (pp_ _ (#Tm f c) = π _ (#Ty f A) (#Ty (qq_term A f) B)).  
* rewrite (ppComp1 f _ pc).
  rewrite (tπ Γ Δ f A B).
  reflexivity.
*
  rewrite (tapp _ _ _ π app (#Tm f c) (# Tm f a) X (ppComp1 f _ pa) ).
  rewrite (DepTypesNat B f a pa (ppComp1 f a pa)).
  reflexivity.
Qed.

Definition CwF_Pi_app_struct : UU :=
  ∑ (app : CwF_PiAppContext) (tapp : CwF_PiAppType), (CwF_PiAppNat app).

Definition CwF_PiAppAbsContext (Λ : CwF_PiAbsContext) (app : CwF_PiAppContext):=
 ∏ Γ ( A : Ty Γ : hSet) (b :Tm (Γ.:A) : hSet) (a : Tm Γ : hSet) (pa : pp_ _ a = A),
 (app _ (Λ _ A b) a) = DepTypesElem b a pa.

Definition CwFPiAppAbsType (Λ : CwF_PiAbsContext) (app : CwF_PiAppContext)
 (tΛ : CwF_PiAbsType) (tapp : CwF_PiAppType) (π : CwF_PiTypeFormer)
  {Γ} {A : Ty Γ : hSet} (b :Tm (Γ.:A) : hSet) (a : Tm Γ : hSet) (pa : pp_ _ a = A) :
 pp_ _ (app _ (Λ _ A b) a) = pp_ _ (DepTypesElem b a pa).
Proof.
  rewrite (tapp _ A (pp_ _ (b)) π app (Λ Γ A b) a (tΛ _ A (pp_ _ (b)) π Λ b (idpath (pp_ _ (b)))) pa).
  rewrite (@DepTypesComp _ _ (pp_ _ b) b (idpath (pp_ _ b)) a pa).
  reflexivity.
Qed.

Definition CwF_Pi_comp_struct
  (π : CwF_pi_form_struct) (lam : CwF_Pi_intro_struct) (app : CwF_Pi_app_struct)
  : UU
  := (CwF_PiAppAbsContext (pr1 lam) (pr1 app)) ×
  (∏ (Γ :C) (A: Ty Γ : hSet)  (b :Tm (Γ.:A) : hSet) (a : Tm Γ : hSet) (pa : pp_ _ a = A),
    pp_ _ ((pr1 app) _ ((pr1 lam) _ A b) a) = pp_ _ (DepTypesElem b a pa)).

Definition CwF_PiAbsAppCompContext (Λ : CwF_PiAbsContext) (app : CwF_PiAppContext) :=
  ∏ Γ (A : Ty Γ : hSet) (c : Tm Γ : hSet), Λ  _ _ (app _ (#Tm (pi A) c) (te A)) = c.

Definition CwF_PiAbsAppCompType (Λ : CwF_PiAbsContext) (tΛ : CwF_PiAbsType)
           (app  : CwF_PiAppContext) (tapp : CwF_PiAppType)
           (π : CwF_PiTypeFormer) (tπ : CwF_PiTypeNat π)
           (Γ :C) (A : Ty Γ : hSet) (B: Ty (Γ.:A) : hSet)
           (c : Tm Γ : hSet) (pc : pp_ _ c = π _ A B)
: pp_ _ (Λ  _ _ (app _ (#Tm (pi A) c) (te A))) = pp_ _ c.
Proof.
  rewrite (tΛ Γ A (pp_ _ (app _ (#Tm (pi A) c) (te A))) π Λ
  (app _ (#Tm (pi A) c) (te A)) (idpath (pp_ _ (app _ (#Tm (pi A) c) (te A))))).
  rewrite pc.
  assert  ((pp_ (Γ.: A) (app (Γ.: A) (# Tm (pi A) c) (te A))) = B).
* assert (pp_ _ (#Tm (pi A) c) = π _ (#Ty (pi A) A) (#Ty (qq_term A (pi A)) B)).
  ** rewrite (ppComp1 (pi A) _ pc).
     rewrite (tπ _ (Γ.:A) (pi A) A B).
     reflexivity.
  ** rewrite (tapp _ _ _ π app (#Tm (pi A) c) (te A) X (te' A)).
     exact (DepTypesEta B).
* rewrite X.
  reflexivity.
Qed.

End Pi_structure.

(** ** Sigma Type over Category with famillies *)
Section Sigma_structure.
  
Definition CwF_SigTypeFormer : UU := ∏ (Γ :C) (A: Ty Γ :hSet)
                         (B: Ty (Γ.:A) : hSet), (Ty Γ : hSet).

Definition CwF_SigTypeNat (σ : CwF_SigTypeFormer) : UU :=
  ∏ (Γ Δ:C) (f : C^op ⟦Γ,Δ⟧) (A : Ty Γ : hSet) (B : Ty(Γ.:A) : hSet),
  ((#Ty (f))( σ _ A B)) = σ _ (#Ty f A) (#Ty (qq_term A f) B).

Definition CwF_SigAbsContext : UU :=
  ∏ (Γ :C) (a : Tm Γ : hSet) (b : Tm Γ : hSet), Tm Γ : hSet.

Definition CwF_SigAbsType : UU := 
  ∏ (Γ :C) (A: Ty Γ : hSet) (B : Ty(Γ.: A) : hSet)
  (σ : CwF_SigTypeFormer) (pair : CwF_SigAbsContext)
  (a : Tm Γ : hSet) (pa : pp_ _ a = A)
  (b : Tm Γ : hSet) (pb : pp_ _ b = DepTypesType B a pa),
  pp_ _ (pair _ a b) = σ _ A B.

Definition CwF_SigAbsNatContext (pair : CwF_SigAbsContext): UU :=
  ∏ (Γ Δ:C)
  (f : C^op ⟦Γ,Δ⟧) (a b :Tm Γ : hSet),
  (# Tm f (pair _  a b) ) = (pair _ (#Tm f a) (#Tm f b)).

Definition CwF_SigAbsNatType
  (pair : CwF_SigAbsContext) (tpair : CwF_SigAbsType)
  (σ : CwF_SigTypeFormer) (tσ : CwF_SigTypeNat σ)
  (Γ Δ:C) (f : C^op ⟦Γ,Δ⟧)
  (A: Ty Γ : hSet) (B : Ty(Γ.: A) : hSet)
  (a : Tm Γ : hSet) (pa : pp_ _ a = A)
  (b : Tm Γ : hSet) (pb : pp_ _ b = DepTypesType B a pa) :
   pp_ _ (# Tm f (pair _  a b) ) = pp_ _ (pair _ (#Tm f a) (#Tm f b)).
Proof.
eapply pathsinv0.
eapply pathscomp0.
refine (tpair _ (#Ty f A) (#Ty (qq_term A f) B) σ pair (#Tm f a)
        (ppComp1 f _ pa) (#Tm f b)  _).
rewrite (@ppComp1 _ _ (DepTypesType B a pa) f b pb).
rewrite (DepTypesNat B f a pa (ppComp1 f a pa)); reflexivity.
rewrite (ppComp1 f _ (tpair _ A B σ pair a pa b pb)).
rewrite tσ; reflexivity.
Qed.

Definition CwF_SigPr1Context : UU := ∏ Γ (c: Tm Γ : hSet), Tm Γ : hSet.

Definition CwF_SigPr1Type : UU :=
  ∏ Γ (σ : CwF_SigTypeFormer) (p1 : CwF_SigPr1Context)
    (A : Ty Γ : hSet) (B : Ty( Γ.: A) : hSet)
    (c: Tm Γ : hSet) (pc : pp_ _ c = σ _ A B) , pp_ _ (p1 _ c) = A.

Lemma ppComp5 {Γ Δ : C} {A: Ty Γ : hSet} (f : C^op ⟦Γ,Δ⟧)
      (σ : CwF_SigTypeFormer) (tσ : CwF_SigTypeNat σ)
      (B : Ty (Γ.: A) : hSet) (c: Tm Γ : hSet) (pc : pp_ _ c = σ _ A B) :
  pp_ _ (# Tm f c)  = σ Δ (# Ty f A) (# Ty (qq_term A f) B).
Proof.
  apply pathsinv0, (pathscomp0(pathsinv0(tσ _ _ f A B))),
  (pathscomp0(pathsinv0(maponpaths (# Ty f) (pc)))),
   pathsinv0, (toforallpaths _ _ _ ((pr2(pr2(pp))) _ _ f) (c)) .
Qed.

Definition CwF_SigPr1NatContext (p1 : CwF_SigPr1Context) : UU :=
    ∏ (Γ Δ : C)  (f : C^op ⟦Γ,Δ⟧) (c : Tm Γ : hSet),
    #Tm f (p1 _ c) = p1 _ (#Tm f c).

Definition CwF_SigPr1NatType (Γ Δ : C) (f : C^op ⟦Γ,Δ⟧)
           (σ : CwF_SigTypeFormer)  (tσ : CwF_SigTypeNat σ)
           (p1 : CwF_SigPr1Context) (tp1 : CwF_SigPr1Type)
           (A : Ty Γ : hSet) (B : Ty( Γ.: A) : hSet)
           (c: Tm Γ : hSet) (pc : pp_ _ c = σ _ A B): 
    pp_ _ (#Tm f (p1 _ c)) = pp_ _ (p1 _ (#Tm f c)).
Proof.
  rewrite (tp1 _ σ p1 (#Ty f A) (#Ty (qq_term A f) B) (#Tm f c)
          (ppComp5 f σ tσ B c pc)).
  eapply pathscomp0.
  refine (toforallpaths _ _ _ ((pr2(pr2(pp))) _ _ f) (p1 _ c)).
  cbn.
  assert ((pr1 (pr2 pp) Γ (p1 Γ c)) = pp_ _ (p1 _ c)).
  auto.
  rewrite X.
  rewrite (tp1 _ σ p1 A B c pc).
  auto.
Qed.

Definition CwF_SigPr2Context :UU := ∏ Γ (c: Tm Γ : hSet), Tm Γ : hSet.

Definition CwF_SigPr2Type :UU := ∏ Γ (σ : CwF_SigTypeFormer)
(A : Ty Γ : hSet) (B : Ty( Γ.: A) : hSet)
(c: Tm Γ : hSet) (pc : pp_ _ c = σ _ A B)
(p2 : CwF_SigPr2Context)
(p1 : CwF_SigPr1Context) (tp1 : CwF_SigPr1Type),
 pp_ _ (p2 _ c) = DepTypesType B (p1 _ c) (tp1 _ σ p1 A B c pc).

Definition CwF_SigPr2NatContext (p2 : CwF_SigPr2Context) : UU :=
  ∏ (Γ Δ : C) (f : C^op ⟦Γ,Δ⟧)
    (c : Tm Γ : hSet),
  # Tm  f (p2 _ c) = p2 _ (#Tm f c).

Definition CwF_SigPr2NatType
  (σ : CwF_SigTypeFormer) (tσ : CwF_SigTypeNat σ)
  (Γ Δ : C) (f : C^op ⟦Γ,Δ⟧)
  (p2 : CwF_SigPr2Context) (tp2 : CwF_SigPr2Type)
  (p1 : CwF_SigPr1Context) (tp1 : CwF_SigPr1Type) (np1: CwF_SigPr1NatContext p1)
  (A : Ty Γ : hSet) (B : Ty( Γ.: A) : hSet)         
  (c : Tm Γ : hSet) (pc : pp_ _ c = σ _ A B ) :
  pp_ _ (#Tm f (p2 _ c)) = pp_ _ (p2 _ (#Tm f c)).
Proof.
  rewrite (tp2 _ σ (#Ty f A) (#Ty (qq_term A f) B) (#Tm f c)
          (ppComp5 f σ tσ B c pc) p2 p1 tp1).
  eapply pathscomp0.
  refine (toforallpaths _ _ _ ((pr2(pr2(pp))) _ _ f) (p2 _ c)).
  assert ((pr1 (pr2 pp) Γ (p2 Γ c)) = pp_ _ (p2 _ c)).
  auto.
  assert (# ((pr1 (pr1 pp)) : functor _ _) f (pr1 (pr2 pp) Γ (p2 Γ c)) =
          (pr1 (pr2 pp) Γ ;; # ((pr1 (pr1 pp)) : functor _ _) f) (p2 Γ c)).
  cbn; reflexivity.
  rewrite <- X0.
  rewrite X.
  rewrite (tp2 _ σ  A B c pc p2 p1 tp1).
  assert (# ((pr1 (pr1 pp)) : functor _ _) f (DepTypesType B (p1 Γ c)
         (tp1 Γ σ p1 A B c pc)) =
         # Ty f (DepTypesType B (p1 Γ c) (tp1 Γ σ p1 A B c pc))).
  auto.
  rewrite X1.
  rewrite (DepTypesNat B f (p1 _ c) (tp1 _ σ p1 A B c pc)
          (ppComp1 f (p1 _ c) (tp1 _ σ p1 A B c pc))).
  assert (# Tm f (p1 Γ c) = p1 Δ (# Tm f c)).
  apply np1.
  apply (DepTypesrewrite (# Ty (qq_term A f) B) (# Tm f (p1 Γ c)) (p1 Δ (# Tm f c))
          (ppComp1 f (p1 Γ c) (tp1 Γ σ p1 A B c pc))
  (tp1 Δ σ p1 (# Ty f A) (# Ty (qq_term A f) B) (# Tm f c)
       (ppComp5 f σ tσ B c pc)) X2).
Qed. 

Definition CwF_SigAbsPr1Context (pair : CwF_SigAbsContext) (p1 : CwF_SigPr1Context )
  : UU := ∏ Γ (a : Tm Γ : hSet) (b : Tm Γ : hSet), p1 _ (pair _ a b) = a.

Definition CwF_SigAbsPr1Type (pair : CwF_SigAbsContext) (tpair : CwF_SigAbsType)
 (σ : CwF_SigTypeFormer) (p1 : CwF_SigPr1Context ) (tp1 : CwF_SigPr1Type)
 (Γ : C) (A : Ty Γ : hSet) (B : Ty(Γ.: A) : hSet)
 (a : Tm Γ : hSet) (pa : pp_ _ a = A)
 (b : Tm Γ : hSet) (pb : pp_ _ b = DepTypesType B a pa)
 : pp_ _ (p1 _ (pair _ a b)) = pp_ _ a.
Proof.
rewrite (tp1 Γ σ p1 A  B (pair _ a b) (tpair Γ A B σ pair a pa b pb)).
apply (!pa).
Qed.

Definition CwF_SigAbsPr2Context
           (pair : CwF_SigAbsContext) (p2 : CwF_SigPr2Context ):=
           ∏ Γ (a : Tm Γ : hSet) (b : Tm Γ : hSet), p2 _ (pair _ a b) = b.

Definition CwF_SigAbsPr2Type (pair : CwF_SigAbsContext) (tpair : CwF_SigAbsType)
 (p1 : CwF_SigPr1Context ) (tp1 : CwF_SigPr1Type)
 (Apr1 : CwF_SigAbsPr1Context pair p1)
 (p2 : CwF_SigPr2Context) (tp2 : CwF_SigPr2Type) (σ : CwF_SigTypeFormer)
 (Γ : C) (A : Ty Γ : hSet) (B : Ty(Γ.: A) : hSet)
 (a : Tm Γ : hSet) (pa : pp_ _ a = A)
 (b : Tm Γ : hSet) (pb : pp_ _ b = DepTypesType B a pa) :
  pp_  _ (p2 _ (pair _ a b)) = pp_ _ b.
Proof.
rewrite (tp2 Γ σ A B (pair _ a b) (tpair Γ A B σ pair a pa b pb) p2 p1 tp1).
apply pathsinv0.
eapply pathscomp0.
exact pb.
apply (DepTypesrewrite B a (p1 Γ (pair Γ a b)) pa  (tp1 Γ σ p1 A B (pair Γ a b)
      (tpair Γ A B σ pair a pa b pb)) (!(Apr1 _ a b))). 
Qed.

Definition CwF_SigAbsPrContext  (pair : CwF_SigAbsContext)
 (p1 : CwF_SigPr1Context ) (p2 : CwF_SigPr2Context ) : UU :=
  ∏ Γ (c : Tm Γ : hSet), pair _ (p1 _ c) (p2 _ c ) = c. 

Definition CwF_SigAbsPrType
 (pair : CwF_SigAbsContext) (tpair : CwF_SigAbsType)
 (p1 : CwF_SigPr1Context ) (tp1 : CwF_SigPr1Type)
 (Apr1 : CwF_SigAbsPr1Context pair p1)
 (p2 : CwF_SigPr2Context) (tp2 : CwF_SigPr2Type) (σ : CwF_SigTypeFormer)
 (Γ : C) (A : Ty Γ : hSet) (B : Ty(Γ.: A) : hSet)
 (c : Tm Γ : hSet) (pc : pp_ _ c = σ _ A B) :
  pp_ _ (pair _ (p1 _ c) (p2 _ c )) = pp_ _ c.
Proof.
  rewrite (tpair Γ A B σ pair (p1 _ c) (tp1 Γ σ p1 A B c pc) (p2 _ c)
           (tp2 Γ σ A B c pc p2 p1 tp1)).
  exact (!pc).
Qed.  

End Sigma_structure.

Section Identity_Structure.
  (** Identity Types over a Category with famillies *)
  
Definition CwF_IdTypeFormer : UU :=
  ∏ (Γ :C) (A: Ty Γ :hSet) (a b : Tm Γ : hSet) (pa : pp_ _ a = A) (pb : pp_ _ b = A), (Ty Γ : hSet).

Definition CwF_IdTypeNat (id : CwF_IdTypeFormer) : UU :=
  ∏ (Γ Δ:C) (f : C^op ⟦Γ,Δ⟧) (A : Ty Γ : hSet) (a b : Tm Γ : hSet) (pa : pp_ _ a = A) (pb : pp_ _ b = A) ,
  #Ty f (id _ A a b pa pb)  =
  id _ (#Ty f A) (#Tm f a) (#Tm f b) (ppComp1 f a pa) (ppComp1 f b pb).
  
Definition CwF_IdReflContext : UU :=
  ∏ Γ (A: Ty Γ :hSet) (a : Tm Γ : hSet) (pa : pp_ _ a = A), (Tm Γ : hSet).

Definition CwF_IdReflType : UU :=
  ∏ Γ (id : CwF_IdTypeFormer )(refl : CwF_IdReflContext)
    (A: Ty Γ :hSet) (a : Tm Γ : hSet) (pa : pp_ _ a = A),
  pp_ _ (refl _ A a pa) = (id _ A a a pa pa).

Definition CwF_IdReflNatContext (refl : CwF_IdReflContext) : UU :=
  ∏ (Γ Δ :C) (f : C^op ⟦Γ,Δ⟧) (A: Ty Γ :hSet) (a : Tm Γ : hSet) (pa : pp_ _ a = A),
  #Tm f (refl _ A a pa) = refl _ (#Ty f A) (#Tm f a) (ppComp1 f a pa).

Definition CwF_IdReflNatType {Γ Δ :C}
(f : C^op ⟦Γ,Δ⟧) (id : CwF_IdTypeFormer) (nid : CwF_IdTypeNat id)
(A: Ty Γ :hSet) (a : Tm Γ : hSet)  (pa : pp_ _ a = A)
(refl : CwF_IdReflContext) (trefl : CwF_IdReflType) :
pp_ _ (#Tm f (refl _ A a pa)) = pp_ _ (refl _ (#Ty f A) (#Tm f a) (ppComp1 f a pa)).
Proof.
rewrite (trefl Δ id refl (#Ty f A) (#Tm f a) (ppComp1 f a pa) ).
rewrite (ppComp1 f (refl Γ A a pa) (trefl _ id refl A a pa)).
rewrite (nid _ _ f A a a).
reflexivity.
Qed.

(*Definition CwF_IdBasedInduction := ∏ (Γ :C) (A: Ty Γ : hSet)
(id : CwF_IdTypeFormer) (refl : CwF_IdReflContext)
(trefl : CwF_IdReflType)                                     
(a : Tm Γ : hSet) (pa : pp_ _ a = A)
(B : Ty (Γ.:(id _ (#Ty (pi A) A) (#Tm (pi A) a) (te A))) : hSet)
(c : DepTypesType (DepTypesType B (refl _ _ (te A))
    (trefl _ id refl _ (te A) (te' A))) a pa )
(b : Tm Γ : hSet) (pb : pp_ _ a = A)                                                     
(h : Tm Γ : hSet) (ph : pp_ _ h = id _ A a b),
DepTypesType (DepTypesType B h ph) b pb.*)

End Identity_Structure.
End Fix_Category.

(*Arguments CwF_PiStructure_data  : clear implicits.
Definition CwF_PiStructure : UU := ∑ CwF, CwF_PiStructure_data CwF.

Arguments CwF_SigmaStructure_data : clear implicits.
Definition CwF_SigmaStructure := ∑ CwF, CwF_SigmaStructure_data CwF.

Definition CwF_PiSigmaStructure := ∑ CwF , (CwF_SigmaStructure_data CwF) × (CwF_PiStructure_data CwF).*)
