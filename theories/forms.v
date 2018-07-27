From mathcomp
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq div choice fintype.
From mathcomp
Require Import tuple bigop ssralg finset fingroup zmodp poly ssrnum.
From mathcomp
Require Import matrix mxalgebra vector falgebra ssrnum algC algnum.
From mathcomp
Require Import fieldext.
From mathcomp Require Import vector.

(* From mathcomp Require classfun. *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Import GRing.Theory Num.Theory.

Reserved Notation "'[ u , v ]"
  (at level 2, format "'[hv' ''[' u , '/ '  v ] ']'").
Reserved Notation "'[ u , v ]_ M"
         (at level 2, format "'[hv' ''[' u , '/ '  v ]_ M ']'").
Reserved Notation "'[ u ]_ M" (at level 2, format "''[' u ]_ M").
Reserved Notation "'[ u ]" (at level 2, format "''[' u ]").
Reserved Notation "u '``_' i"
    (at level 3, i at level 2, left associativity, format "u '``_' i").
Reserved Notation "A ^_|_"    (at level 8, format "A ^_|_").
Reserved Notation "A _|_ B" (at level 69, format "A  _|_  B").

Section extramx.

Local Notation "M ^ phi" := (map_mx phi M).
Local Notation "M ^t phi" := (map_mx phi (M ^T)) (phi at level 30, at level 30).

Lemma map_mx_comp (R S T : ringType) m n (M : 'M[R]_(m,n))
      (f : R -> S) (g : S -> T) : M ^ (g \o f) = (M ^ f) ^ g.
Proof. by apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma eq_map_mx (R S : ringType) m n (M : 'M[R]_(m,n))
      (g f : R -> S) : f =1 g -> M ^ f = M ^ g.
Proof. by move=> eq_fg; apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma map_mx_id (R : ringType) m n (M : 'M[R]_(m,n)) : M ^ id = M.
Proof. by apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma eq_map_mx_id (R : ringType) m n (M : 'M[R]_(m,n)) (f : R -> R) :
  f =1 id -> M ^ f = M.
Proof. by move=> /eq_map_mx->; rewrite map_mx_id. Qed.

End extramx.

(* TODO: to vector *)
Lemma dim_regular (F : fieldType) : \dim {:regular_vectType F} = 1%N.
Proof. by rewrite /dimv Vector.InternalTheory.mx2vsK mxrank1. Qed.


Module InvolutiveMorphism.

Section ClassDef.

Variables (R : ringType).

Record class_of (f : R -> R) : Type :=
  Class {base : rmorphism f; mixin : involutive f}.
Local Coercion base : class_of >-> rmorphism.

Structure map (phR : phant R) := Pack {apply; _ : class_of apply}.
Local Coercion apply : map >-> Funclass.

Variables (phR : phant R) (f g : R -> R) (cF : map phR).

Definition class := let: Pack _ c as cF' := cF return class_of cF' in c.

Definition clone fM of phant_id g (apply cF) & phant_id fM class :=
  @Pack phR f fM.

Definition pack (fM : involutive f) :=
  fun (phRR : phant (R -> R)) (bF : GRing.RMorphism.map phRR) fA
      of phant_id (GRing.RMorphism.class bF) fA =>
  Pack phR (Class fA fM).

Canonical additive := GRing.Additive.Pack (Phant (R -> R)) class.
Canonical rmorphism := GRing.RMorphism.Pack (Phant (R -> R)) class.

End ClassDef.

Module Exports.
Notation involutive_rmorphism f := (class_of f).
Coercion base : involutive_rmorphism >-> GRing.RMorphism.class_of.
Coercion mixin : involutive_rmorphism >-> involutive.
Coercion apply : map >-> Funclass.
Notation InvolutiveRMorphism fM := (pack (Phant _) fM id).
Notation "{ 'involutive_rmorphism' fRS }" := (map (Phant fRS))
  (at level 0, format "{ 'involutive_rmorphism'  fRS }") : ring_scope.
Notation "[ 'involutive_rmorphism' 'of' f 'as' g ]" := (@clone _ _ f g _ _ idfun id)
  (at level 0, format "[ 'involutive_rmorphism'  'of'  f  'as'  g ]") : form_scope.
Notation "[ 'involutive_rmorphism' 'of' f ]" := (@clone _ _ f f _ _ id id)
  (at level 0, format "[ 'involutive_rmorphism'  'of'  f ]") : form_scope.
Coercion additive : map >-> GRing.Additive.map.
Canonical additive.
Coercion rmorphism : map >-> GRing.RMorphism.map.
Canonical rmorphism.
End Exports.

End InvolutiveMorphism.
Include InvolutiveMorphism.Exports.

Section InvolutiveTheory.

Variable (R : ringType).

Lemma idfunK : involutive (@idfun R). Proof. by []. Qed.
Canonical idfun_involutive := InvolutiveRMorphism idfunK.

Variable (f : {involutive_rmorphism R}).
Lemma rmorphK : involutive f. Proof. by case: f => [? []]. Qed.

End InvolutiveTheory.

(** Contents *)

Structure revop X Y Z (f : Y -> X -> Z) := RevOp {
  fun_of_revop :> X -> Y -> Z;
  _ : forall x, f x =1 fun_of_revop^~ x
}.
Notation "[ 'revop' revop 'of' op ]" :=
  (@RevOp _ _ _ revop op (fun _ _ => erefl))
  (at level 0, format "[ 'revop'  revop  'of'  op ]") : form_scope.

(* Fact applyr_key : unit. Proof. exact. Qed. *)
Definition applyr_head U U' V t (f : U -> U' -> V) u v := let: tt := t in f v u.
Notation applyr := (@applyr_head _ _ _ tt).

Module Bilinear.

Section ClassDef.

Variables (R : ringType) (U U' : lmodType R) (V : zmodType) (s s' : R -> V -> V).
Implicit Type phUU'V : phant (U -> U' -> V).

Local Coercion GRing.Scale.op : GRing.Scale.law >-> Funclass.
Definition axiom (f : U -> U' -> V) (s_law : GRing.Scale.law s) (eqs : s = s_law)
                                    (s'_law : GRing.Scale.law s') (eqs' : s' = s'_law) :=
  ((forall u', GRing.Linear.axiom (f^~ u') eqs)
  * (forall u, GRing.Linear.axiom (f u) eqs'))%type.

Record class_of (f : U -> U' -> V) : Prop := Class {
  basel : forall u', GRing.Linear.class_of s (f^~ u');
  baser : forall u, GRing.Linear.class_of s' (f u)
}.

Lemma class_of_axiom f s_law s'_law Ds Ds' :
   @axiom f s_law Ds s'_law Ds' -> class_of f.
Proof.
by pose coa := GRing.Linear.class_of_axiom; move=> [/(_ _) /coa ? /(_ _) /coa].
Qed.

Structure map phUU'V := Pack {apply; _ : class_of apply}.
Local Coercion apply : map >-> Funclass.

Definition class (phUU'V : _)  (cF : map phUU'V) :=
   let: Pack _ c as cF' := cF return class_of cF' in c.

Canonical additiver phU'V phUU'V (u : U) cF := GRing.Additive.Pack phU'V
  (baser (@class phUU'V cF) u).
Canonical linearr phU'V  phUU'V (u : U) cF := GRing.Linear.Pack phU'V
  (baser (@class phUU'V cF) u).

Canonical additivel phUV phUU'V (u' : U') (cF : map _) :=
  @GRing.Additive.Pack _ _ phUV (applyr cF u') (basel (@class phUU'V cF) u').
Canonical linearl phUV phUU'V  (u' : U') (cF : map _) :=
  @GRing.Linear.Pack _ _ _ _ phUV (applyr cF u') (basel (@class phUU'V cF) u').

Definition pack (phUV : phant (U -> V)) (phU'V : phant (U' -> V))
           (revf : U' -> U -> V) (rf : revop revf) f (g : U -> U' -> V) of (g = fun_of_revop rf) :=
  fun (bFl : U' -> GRing.Linear.map s phUV) flc of (forall u', revf u' = bFl u') &
      (forall u', phant_id (GRing.Linear.class (bFl u')) (flc u')) =>
  fun (bFr : U -> GRing.Linear.map s' phU'V) frc of (forall u, g u = bFr u) &
      (forall u, phant_id (GRing.Linear.class (bFr u)) (frc u)) =>
  @Pack (Phant _) f (Class flc frc).

End ClassDef.

Module Exports.
Notation bilinear_for s s' f := (axiom f (erefl s) (erefl s')).
Notation bilinear f := (bilinear_for *:%R *:%R f).
Notation biscalar f := (bilinear_for *%R *%R f).
Notation bilmorphism_for s s' f := (class_of s s' f).
Notation bilmorphism f := (bilmorphism_for *:%R *:%R f).
Coercion class_of_axiom : axiom >-> bilmorphism_for.
Coercion baser : bilmorphism_for >-> Funclass.
Coercion apply : map >-> Funclass.
Notation "{ 'bilinear' fUV | s & s' }" := (map s s' (Phant fUV))
  (at level 0, format "{ 'bilinear'  fUV  |  s  &  s' }") : ring_scope.
Notation "{ 'bilinear' fUV | s }" := (map s.1 s.2 (Phant fUV))
  (at level 0, format "{ 'bilinear'  fUV  |  s }") : ring_scope.
Notation "{ 'bilinear' fUV }" := {bilinear fUV | *:%R & *:%R}
  (at level 0, format "{ 'bilinear'  fUV }") : ring_scope.
Notation "{ 'biscalar' U }" := {bilinear U -> U -> _ | *%R & *%R}
  (at level 0, format "{ 'biscalar'  U }") : ring_scope.
Notation "[ 'bilinear' 'of' f 'as' g ]" :=
  (@pack  _ _ _ _ _ _ _ _ _ _ f g erefl _ _
         (fun=> erefl) (fun=> idfun) _ _ (fun=> erefl) (fun=> idfun)).
Notation "[ 'bilinear' 'of' f ]" :=  [bilinear of f as f]
  (at level 0, format "[ 'bilinear'  'of'  f ]") : form_scope.
Canonical additiver.
Canonical linearr.
Canonical additivel.
Canonical linearl.
Notation biapplyr := (@applyr_head _ _ _ _ tt).
End Exports.

End Bilinear.
Include Bilinear.Exports.

Section BilinearTheory.

Variable R : ringType.

Section GenericProperties.

Variables (U U' : lmodType R) (V : zmodType) (s : R -> V -> V) (s' : R -> V -> V).
Variable f : {bilinear U -> U' -> V | s & s'}.

Lemma linear0r z : f z 0 = 0. Proof. by rewrite linear0. Qed.
Lemma linearNr z : {morph f z : x / - x}. Proof. exact: raddfN. Qed.
Lemma linearDr z : {morph f z : x y / x + y}. Proof. exact: raddfD. Qed.
Lemma linearBr z : {morph f z : x y / x - y}. Proof. exact: raddfB. Qed.
Lemma linearMnr z n : {morph f z : x / x *+ n}. Proof. exact: raddfMn. Qed.
Lemma linearMNnr z n : {morph f z : x / x *- n}. Proof. exact: raddfMNn. Qed.
Lemma linear_sumr z I r (P : pred I) E :
  f z (\sum_(i <- r | P i) E i) = \sum_(i <- r | P i) f z (E i).
Proof. exact: raddf_sum. Qed.

Lemma linearZr_LR z : scalable_for s' (f z). Proof. exact: linearZ_LR. Qed.
Lemma linearPr z a : {morph f z : u v / a *: u + v >-> s' a u + v}.
Proof. exact: linearP. Qed.

Lemma applyrE x : applyr f x =1 f^~ x. Proof. by []. Qed.

Lemma linear0l z : f 0 z = 0. Proof. by rewrite -applyrE raddf0. Qed.
Lemma linearNl z : {morph f^~ z : x / - x}.
Proof. by move=> ?; rewrite -applyrE raddfN. Qed.
Lemma linearDl z : {morph f^~ z : x y / x + y}.
Proof. by move=> ??; rewrite -applyrE raddfD. Qed.
Lemma linearBl z : {morph f^~ z : x y / x - y}.
Proof. by move=> ??; rewrite -applyrE raddfB. Qed.
Lemma linearMnl z n : {morph f^~ z : x / x *+ n}.
Proof. by move=> ?; rewrite -applyrE raddfMn. Qed.
Lemma linearMNnl z n : {morph f^~ z : x / x *- n}.
Proof. by move=> ?; rewrite -applyrE raddfMNn. Qed.
Lemma linear_suml z I r (P : pred I) E :
  f (\sum_(i <- r | P i) E i) z = \sum_(i <- r | P i) f (E i) z.
Proof. by rewrite -applyrE raddf_sum. Qed.

Lemma linearZl_LR z : scalable_for s (f^~ z).
Proof. by move=> ??; rewrite -applyrE linearZ_LR. Qed.
Lemma linearPl z a : {morph f^~ z : u v / a *: u + v >-> s a u + v}.
Proof. by move=> ??; rewrite -applyrE linearP. Qed.

End GenericProperties.

(* Section BidirectionalLinearZ. *)

(* Variables (U : lmodType R) (V : zmodType) (s : R -> V -> V). *)
(* Variables (S : ringType) (h : S -> V -> V) (h_law : GRing.Scale.law h). *)

(* Lemma linearZ l z c a (h_c := GRing.Scale.op h_law c) (f : GRing.Linear.map_for U s a h_c) u : *)
(*   f z (a *: u) = h_c (GRing.Linear.wrap (f z) u). *)
(* Proof. by rewrite linearZ_LR; case: f => f /= ->. Qed. *)

(* End BidirectionalLinearZ. *)

End BilinearTheory.

Canonical rev_mulmx (R : ringType) m n p := [revop mulmxr of @mulmx R m n p].
Canonical mulmx_bilinear (R : comRingType) m n p := [bilinear of @mulmx R m n p].

Module Hermitian.

Section ClassDef.

Variables (R : ringType) (U : lmodType R) (eps : bool) (theta : R -> R).
Implicit Types phU : phant U.

Local Coercion GRing.Scale.op : GRing.Scale.law >-> Funclass.
Definition axiom (f : U -> U -> R) :=
  forall x y : U, f x y = (-1) ^+ eps * theta (f y x).

Record class_of (f : U -> U -> R) : Prop := Class {
  base : Bilinear.class_of ( *%R) (theta \; *%R) f;
  mixin : axiom f
}.

Structure map phU := Pack {apply; _ : class_of apply}.
Local Coercion apply : map >-> Funclass.

Variables (phU : phant U) (cF : map phU).

Definition class := let: Pack _ c as cF' := cF return class_of cF' in c.

Canonical additiver (u : U) := Additive (base class u).
Canonical linearr (u : U) := Linear (base class u).
Canonical additivel (u' : U) := @GRing.Additive.Pack _ _ (Phant (U -> R))
  (applyr cF u') (Bilinear.basel (base class) u').
Canonical linearl (u' : U) := @GRing.Linear.Pack _ _ _ _ (Phant (U -> R))
  (applyr cF u') (Bilinear.basel (base class) u').
Canonical bilinear := @Bilinear.Pack _ _ _ _ _ _ (Phant (U -> U -> R)) cF (base class).

Definition clone (f g : U -> U -> R) :=
 fun fM of phant_id g (apply cF) & phant_id fM class => @Pack phU f fM.

Definition pack f fM :=
  fun b s s' (phUUR : phant (U -> U -> R)) (bF : Bilinear.map s s' phUUR)
      of phant_id (Bilinear.class bF) b =>
  @Pack phU f (Class b fM).

End ClassDef.

Module Exports.
Notation "{ 'hermitian' U 'for' eps & theta }" := (map eps theta (Phant U))
  (at level 0, format "{ 'hermitian'  U  'for'  eps  &  theta }") : ring_scope.
Coercion base : class_of >-> bilmorphism_for.
Coercion apply : map >-> Funclass.
Notation "[ 'hermitian' 'of' f 'as' g ]" := (@clone _ _ _ _ _ _ f g _ idfun idfun)
  (at level 0, format "[ 'hermitian'  'of'  f  'as'  g ]") : form_scope.
Notation "[ 'hermitian' 'of' f ]" := (@clone _ _ _ _ _ _ f f _ idfun idfun)
  (at level 0, format "[ 'hermitian'  'of'  f ]") : form_scope.
Notation hermitian_for := Hermitian.axiom.
Notation Hermitian fM := (pack (Phant _) fM idfun).
Canonical additiver.
Canonical linearr.
Canonical additivel.
Canonical linearl.
Canonical bilinear.
Notation hermapplyr := (@applyr_head _ _ _ _ tt).
End Exports.

End Hermitian.
Include Hermitian.Exports.

Module Dot.

Section ClassDef.

Variables (R : numDomainType) (U : lmodType R) (theta : R -> R).
Implicit Types phU : phant U.

Local Coercion GRing.Scale.op : GRing.Scale.law >-> Funclass.
Definition axiom (f : U -> U -> R) := forall u, u != 0 -> 0 < f u u.

Record class_of (f : U -> U -> R) : Prop := Class {
  base : Hermitian.class_of false theta f;
  mixin : axiom f
}.

Structure map phU := Pack {apply; _ : class_of apply}.
Local Coercion apply : map >-> Funclass.

Variables (phU : phant U) (cF : map phU).

Definition class := let: Pack _ c as cF' := cF return class_of cF' in c.

Canonical additiver (u : U) := Additive (base class u).
Canonical linearr (u : U) := Linear (base class u).
Canonical additivel (u' : U) := @GRing.Additive.Pack _ _ (Phant (U -> R))
  (applyr cF u') (Bilinear.basel (base class) u').
Canonical linearl (u' : U) := @GRing.Linear.Pack _ _ _ _ (Phant (U -> R))
  (applyr cF u') (Bilinear.basel (base class) u').
Canonical bilinear := @Bilinear.Pack _ _ _ _ _ _ (Phant (U -> U -> R)) cF (base class).
Canonical hermitian := @Hermitian.Pack _ _ _ _ (Phant U) cF (base class).

Definition clone (f g : U -> U -> R) :=
 fun fM of phant_id g (apply cF) & phant_id fM class => @Pack phU f fM.


Definition pack f fM :=
  fun b s s' (bF : Hermitian.map s s' phU) of phant_id (Hermitian.class bF) b =>
  @Pack phU f (Class b fM).

End ClassDef.

Module Exports.
Notation "{ 'dot' U 'for' theta }" := (map theta (Phant U))
  (at level 0, format "{ 'dot'  U  'for'  theta }") : ring_scope.
Coercion base : class_of >-> Hermitian.class_of.
Coercion apply : map >-> Funclass.
Notation "[ 'dot' 'of' f 'as' g ]" := (@clone _ _ _ _ _ f g _ idfun idfun)
  (at level 0, format "[ 'dot'  'of'  f  'as'  g ]") : form_scope.
Notation "[ 'dot' 'of' f ]" := (@clone _ _ _ _ _ f f _ idfun idfun)
  (at level 0, format "[ 'dot'  'of'  f ]") : form_scope.
Notation Dot fM := (pack fM idfun).
Notation is_dot := Dot.axiom.
Canonical additiver.
Canonical linearr.
Canonical additivel.
Canonical linearl.
Canonical bilinear.
Canonical hermitian.
End Exports.

End Dot.
Include Dot.Exports.

Definition symmetric_map (R : ringType) (U : lmodType R) (phU : phant U) :=
  Eval simpl in Hermitian.map false idfun phU.
Notation "{ 'symmetric' U }" := (symmetric_map (Phant U))
  (at level 0, format "{ 'symmetric'  U }") : ring_scope.

Definition skew_symmetric_map (R : ringType) (U : lmodType R) (phU : phant U) :=
  Eval simpl in Hermitian.map true idfun phU.
Notation "{ 'skew_symmetric' U }" := (skew_symmetric_map (Phant U))
  (at level 0, format "{ 'skew_symmetric'  U }") : ring_scope.

Definition hermitian_sym_map (R : ringType) (U : lmodType R)
  theta (phU : phant U) :=
  Eval simpl in Hermitian.map false theta phU.
Notation "{ 'hermitian_sym' U 'for' theta }" := (hermitian_sym_map (Phant U))
  (at level 0, format "{ 'hermitian_sym'  U  'for'  theta }") : ring_scope.

Definition is_skew (R : ringType) (eps : bool) (theta : R -> R)
  (U : lmodType R) (form : {hermitian U for eps & theta}) :=
  (eps = true) /\ (theta =1 id).
Definition is_sym (R : ringType) (eps : bool) (theta : R -> R)
  (U : lmodType R) (form : {hermitian U for eps & theta}) :=
  (eps = false) /\ (theta =1 id).
Definition is_hermsym  (R : ringType) (eps : bool) (theta : R -> R)
  (U : lmodType R) (form : {hermitian U for eps & theta}) :=
  (eps = false).

Section HermitianModuleTheory.

Variables (R : ringType) (eps : bool) (theta : {rmorphism R -> R}).
Variable (U : lmodType R) (form : {hermitian U for eps & theta}).

Local Notation "''[' u , v ]" := (form u%R v%R) : ring_scope.
Local Notation "''[' u ]" := '[u, u]%R : ring_scope.

Lemma hermC u v : '[u, v] = (-1) ^+ eps * theta '[v, u].
Proof. by case: form => [? []]. Qed.

Lemma hnormN u : '[- u] = '[u].
Proof. by rewrite linearNl raddfN opprK. Qed.

Lemma hnorm_sign n u : '[(-1) ^+ n *: u] = '[u].
Proof. by rewrite -signr_odd scaler_sign; case: (odd n); rewrite ?hnormN. Qed.

Lemma hnormD u v :
  let d := '[u, v] in '[u + v] = '[u] + '[v] + (d + (-1) ^+ eps * theta d).
Proof. by rewrite /= addrAC -hermC linearDl /= !linearD !addrA. Qed.

Lemma hnormB u v :
  let d := '[u, v] in '[u - v] = '[u] + '[v] - (d + (-1) ^+ eps * theta d).
Proof. by rewrite /= hnormD hnormN linearN rmorphN /= mulrN -opprD. Qed.

Lemma hnormDd u v : '[u, v] = 0 -> '[u + v] = '[u] + '[v].
Proof. by move=> ouv; rewrite hnormD ouv rmorph0 mulr0 !addr0. Qed.

Lemma hnormBd u v : '[u, v] = 0 -> '[u - v] = '[u] + '[v].
Proof. by move=> ouv; rewrite hnormDd ?hnormN // linearN /= ouv oppr0. Qed.

Local Notation "u _|_ v" := ('[u, v] == 0) : ring_scope.

Definition ortho_rec S1 S2 :=
  all [pred u | all [pred v | u _|_ v] S2] S1.

Fixpoint pair_ortho_rec S :=
  if S is v :: S' then ortho_rec [:: v] S' && pair_ortho_rec S' else true.

(* We exclude 0 from pairwise orthogonal sets. *)
Definition pairwise_orthogonal S := (0 \notin S) && pair_ortho_rec S.

Definition orthonormal S := all [pred v | '[v] == 1] S && pair_ortho_rec S.

Definition isometry tau := forall u v, '[tau u, tau v] = '[u, v].

Definition isometry_from_to mD tau mR :=
   prop_in2 mD (inPhantom (isometry tau))
  /\ prop_in1 mD (inPhantom (forall u, in_mem (tau u) mR)).

Definition orthogonal S1 S2 := nosimpl (@ortho_rec S1 S2).

Lemma orthogonal_cons u us vs :
  orthogonal (u :: us) vs = orthogonal [:: u] vs && orthogonal us vs.
Proof. by rewrite /orthogonal /= andbT. Qed.

End HermitianModuleTheory.

Hint Extern 0 (Hermitian.map _ _ _) =>
  match goal with form : Hermitian.map _ _ _ |- _ => exact form end : core.
(* in order to use thetaK *)

Notation "{ 'in' D , 'isometry' tau , 'to' R }" :=
    (isometry_from_to (mem D) tau (mem R))
  (at level 0, format "{ 'in'  D ,  'isometry'  tau ,  'to'  R }")
     : type_scope.

Section HermitianVectTheory.

Variables (R : fieldType) (eps : bool) (theta : {rmorphism R -> R}).
Variable (U : lmodType R) (form : {hermitian U for eps & theta}).

Local Notation "''[' u , v ]" := (form u%R v%R) : ring_scope.
Local Notation "''[' u ]" := '[u, u]%R : ring_scope.

Lemma herm_eq0C u v : ('[u, v] == 0) = ('[v, u] == 0).
Proof. by rewrite hermC mulf_eq0 signr_eq0 /= fmorph_eq0. Qed.

End HermitianVectTheory.

Section HermitianFinVectTheory.

Variables (F : fieldType) (eps : bool) (theta : {rmorphism F -> F}).
Variable (vT : vectType F) (form : {hermitian vT for eps & theta}).
Let n := \dim {:vT}.
Implicit Types (u v : vT) (U V : {vspace vT}).

Local Notation "''[' u , v ]" := (form u%R v%R) : ring_scope.
Local Notation "''[' u ]" := '[u, u]%R : ring_scope.

Let alpha v := (linfun (applyr form v : vT -> F^o)).

Definition rad V := (\bigcap_(i < \dim V) lker (alpha (vbasis V)`_i))%VS.

Local Notation "U _|_ V" := (U <= rad V)%VS : vspace_scope.

Lemma mem_radPn V u : reflect (exists2 v, v \in V & '[u, v] != 0) (u \notin rad V).
Proof.
apply: (iffP idP) => [u_radV|[v /coord_vbasis-> uvNortho]]; last first.
  apply/subv_bigcapP => uP; rewrite linear_sum big1 ?eqxx //= in uvNortho.
  move=> i _; have := uP i isT.
  by rewrite -memvE memv_ker lfunE linearZ => /eqP/=->; rewrite mulr0.
suff /existsP [i ui_neq0] : [exists i : 'I_(\dim V), '[u, (vbasis V)`_i] != 0].
  by exists (vbasis V)`_i => //; rewrite vbasis_mem ?mem_nth ?size_tuple.
apply: contraNT u_radV; rewrite negb_exists => /forallP ui_eq0.
by apply/subv_bigcapP => i _; rewrite -memvE memv_ker lfunE /= -[_ == _]negbK.
Qed.

Lemma mem_radP V u : reflect {in V, forall v, '[u, v] = 0} (u \in rad V).
Proof.
apply: (iffP idP) => [/mem_radPn orthoNu v vV|/(_ _ _)/eqP ortho_u].
  by apply/eqP/negP=> /negP Northo_uv; apply: orthoNu; exists v.
by apply/mem_radPn => -[v /ortho_u->].
Qed.

Lemma rad1E u : rad <[u]> = lker (alpha u).
Proof.
apply/eqP; rewrite eqEsubv; apply/andP.
split; apply/subvP=> v; rewrite memv_ker lfunE /=.
   by move=> /mem_radP-> //; rewrite ?memv_line.
move=> vu_eq0; apply/mem_radP => w /vlineP[k->].
by apply/eqP; rewrite linearZ mulf_eq0 vu_eq0 orbT.
Qed.

Lemma orthoP U V : reflect {in U & V, forall u v, '[u, v] = 0} (U _|_ V)%VS.
Proof.
apply: (iffP subvP); first by move=> /(_ _ _)/mem_radP; move=> H ????; apply: H.
by move=> H ??; apply/mem_radP=> ??; apply: H.
Qed.

Lemma ortho_sym U V : (U _|_ V)%VS = (V _|_ U)%VS.
Proof. by apply/orthoP/orthoP => eq0 ????; apply/eqP; rewrite herm_eq0C eq0. Qed.

Lemma mem_rad1 v u : (u \in rad <[v]>) = ('[u, v] == 0).
Proof. by rewrite rad1E memv_ker lfunE. Qed.

Lemma ortho11 u v : (<[u]> _|_ <[v]>)%VS = ('[u, v] == 0).
Proof. exact: mem_rad1. Qed.

Lemma mem_rad1_sym v u : (u \in rad <[v]>) = (v \in rad <[u]>).
Proof. exact: ortho_sym. Qed.

Lemma rad0 : rad 0 = fullv.
Proof.
apply/eqP; rewrite eqEsubv subvf.
by apply/subvP => x _; rewrite mem_rad1 linear0.
Qed.

Lemma mem_rad_sym V u : (u \in rad V) = (V <= rad <[u]>)%VS.
Proof. exact: ortho_sym. Qed.

Lemma leq_dim_rad1 u V : ((\dim V).-1 <= \dim (V :&: rad <[u]>))%N.
Proof.
rewrite -(limg_ker_dim (alpha u) V) -rad1E.
have := dimvS (subvf (alpha u @: V)); rewrite dim_regular addnC.
by case: (\dim _) => [|[]] // _; rewrite leq_pred.
Qed.

Lemma dim_img_form_eq1 u V : u \notin rad V -> \dim (alpha u @: V)%VS = 1%N.
Proof.
move=> /mem_radPn [v vV Northo_uv]; apply/eqP; rewrite eqn_leq /=.
rewrite -[1%N as X in (_ <= X)%N](dim_regular F) dimvS ?subvf//=.
have := @dimvS _ _ <['[v, u] : F^o]> (alpha u @: V).
rewrite -memvE dim_vline herm_eq0C Northo_uv; apply.
by apply/memv_imgP; exists v; rewrite ?memvf// !lfunE /=.
Qed.

Lemma eq_dim_rad1 u V : u \notin rad V -> (\dim V).-1 = \dim (V :&: rad <[u]>).
Proof.
rewrite -(limg_ker_dim (alpha u) V) => /dim_img_form_eq1->.
by rewrite -rad1E addn1.
Qed.

Lemma dim_img_form_eq0 u V : u \in rad V -> \dim (alpha u @: V)%VS = 0%N.
Proof. by move=> uV; apply/eqP; rewrite dimv_eq0 -lkerE -rad1E ortho_sym. Qed.

Lemma neq_dim_rad1 u V : (\dim V > 0)%N ->
  u \in rad V -> ((\dim V).-1 < \dim (V :&: rad <[u]>))%N.
Proof.
move=> V_gt0; rewrite -(limg_ker_dim (alpha u) V) -rad1E => u_in.
rewrite dim_img_form_eq0 // addn0 (capv_idPl _) 1?ortho_sym //.
by case: (\dim _) V_gt0.
Qed.

Lemma leqif_dim_rad1 u V : (\dim V > 0)%N ->
   ((\dim V).-1 <= \dim (V :&: rad <[u]>) ?= iff (u \notin rad V))%N.
Proof.
move=> Vr_gt0; apply/leqifP.
by case: (boolP (u \in _)) => /= [/neq_dim_rad1->|/eq_dim_rad1->].
Qed.

Lemma leqif_dim_rad1_full u : (n > 0)%N ->
   ((\dim {:vT}).-1 <= \dim (rad <[u]>) ?= iff (u \notin rad fullv))%N.
Proof.
by move=> n_gt0; have := @leqif_dim_rad1 u fullv; rewrite capfv; apply.
Qed.

(* Link between rad and orthogonality of sequences *)
Lemma orthogonal1P u v : reflect ('[u, v] = 0) (orthogonal form [:: u] [:: v]).
Proof. by rewrite /orthogonal /= !andbT; apply: eqP. Qed.

Lemma orthogonalP us vs :
  reflect {in us & vs, forall u v, '[u, v] = 0} (orthogonal form us vs).
Proof.
apply: (iffP allP) => ousvs u => [v /ousvs/allP opus /opus/eqP // | /ousvs opus].
by apply/allP=> v /= /opus->.
Qed.

Lemma orthogonalE us vs : (orthogonal form us vs) = (<<us>> _|_ <<vs>>)%VS.
Proof.
apply/orthogonalP/orthoP => uvsP u v; last first.
  by move=> uus vvs; rewrite uvsP // memv_span.
rewrite -[us]in_tupleE -[vs]in_tupleE => /coord_span-> /coord_span->.
rewrite linear_sum big1 //= => i _; rewrite linear_suml big1 //= => j _.
by rewrite linearZ /= linearZl_LR/= uvsP ?mulr0// mem_nth.
Qed.

Lemma orthoE U V : (U _|_ V)%VS = orthogonal form (vbasis U) (vbasis V).
Proof. by rewrite orthogonalE !(span_basis (vbasisP _)). Qed.

Definition nondegenerate := rad fullv == 0%VS.
Definition is_symplectic := [/\ nondegenerate, is_skew form &
                                2 \in [char F] -> forall u, '[u, u] = 0].
Definition is_orthogonal := [/\ nondegenerate, is_sym form &
                                2 \in [char F] -> forall u, '[u, u] = 0].
Definition is_unitary := nondegenerate /\ (is_hermsym form).

End HermitianFinVectTheory.

Section DotVectTheory.

Variables (C : numClosedFieldType).
Variable (U : lmodType C) (form : {dot U for conjC}).

Local Notation "''[' u , v ]" := (form u%R v%R) : ring_scope.
Local Notation "''[' u ]" := '[u, u]%R : ring_scope.

Let neq0_dnorm_gt0 u : u != 0 -> 0 < '[u].
Proof. by case: form => [?[?]] /=; apply. Qed.

Lemma dnorm_geiff0 u : 0 <= '[u] ?= iff (u == 0).
Proof.
by apply/lerifP; have [->|uN0] := altP eqP; rewrite ?linear0 ?neq0_dnorm_gt0.
Qed.

Lemma dnorm_ge0 u : 0 <= '[u]. Proof. by rewrite dnorm_geiff0. Qed.

Lemma dnorm_eq0 u : ('[u] == 0) = (u == 0).
Proof. by rewrite -dnorm_geiff0 eq_sym. Qed.

Lemma dnorm_gt0 u : (0 < '[u]) = (u != 0).
Proof. by rewrite ltr_def dnorm_eq0 dnorm_ge0 andbT. Qed.

Lemma sqrt_dnorm_ge0 u : 0 <= sqrtC '[u].
Proof. by rewrite sqrtC_ge0 dnorm_ge0. Qed.

Lemma sqrt_dnorm_eq0 u : (sqrtC '[u] == 0) = (u == 0).
Proof. by rewrite sqrtC_eq0 dnorm_eq0. Qed.

Lemma sqrt_dnorm_gt0 u : (sqrtC '[u] > 0) = (u != 0).
Proof. by rewrite sqrtC_gt0 dnorm_gt0. Qed.

Lemma dnormZ a u : '[a *: u]= `|a| ^+ 2 * '[u].
Proof. by rewrite linearZl_LR linearZ mulrA normCK. Qed.

Lemma dnormD u v : let d := '[u, v] in '[u + v] = '[u] + '[v] + (d + d^*).
Proof. by rewrite hnormD mul1r. Qed.

Lemma dnormB u v : let d := '[u, v] in '[u - v] = '[u] + '[v] - (d + d^*).
Proof. by rewrite hnormB mul1r. Qed.

End DotVectTheory.

Section DotFinVectTheory.

Variables (C : numClosedFieldType).
Variable (U : vectType C) (form : {dot U for conjC}).

Local Notation "''[' u , v ]" := (form u%R v%R) : ring_scope.
Local Notation "''[' u ]" := '[u, u]%R : ring_scope.

Theorem CauchySchwarz (u v : U) :
  `|'[u, v]| ^+ 2 <= '[u] * '[v] ?= iff ~~ free [:: u; v].
Proof.
rewrite free_cons span_seq1 seq1_free -negb_or negbK orbC.
have [-> | nz_v] /= := altP (v =P 0).
  by apply/lerifP; rewrite /= !linear0 normCK mul0r mulr0.
without loss ou: u / '[u, v] = 0.
  move=> IHo; pose a := '[u, v] / '[v]; pose u1 := u - a *: v.
  have ou: '[u1, v] = 0.
    by rewrite linearBl /= linearZl_LR /= divfK ?dnorm_eq0 ?subrr.
  rewrite (canRL (subrK _) (erefl u1)) rpredDr ?rpredZ ?memv_line //.
  rewrite linearDl /= ou add0r linearZl_LR /= normrM (ger0_norm (dnorm_ge0 _ _)).
  rewrite exprMn mulrA -dnormZ hnormDd/=; last by rewrite linearZ/= ou mulr0.
  by have:= IHo _ ou; rewrite mulrDl -lerif_subLR subrr ou normCK mul0r.
rewrite ou normCK mul0r; split; first by rewrite mulr_ge0 ?dnorm_ge0.
rewrite eq_sym mulf_eq0 orbC dnorm_eq0 (negPf nz_v) /=.
apply/idP/idP=> [|/vlineP[a {2}->]]; last by rewrite linearZ/= ou mulr0.
by rewrite dnorm_eq0 => /eqP->; apply: rpred0.
Qed.

Lemma CauchySchwarz_sqrt u v :
  `|'[u, v]| <= sqrtC '[u] * sqrtC '[v] ?= iff ~~ free [:: u; v].
Proof.
rewrite -(sqrCK (normr_ge0 _)) -sqrtCM ?qualifE ?dnorm_ge0 //.
rewrite (mono_in_lerif (@ler_sqrtC _)) 1?rpredM ?qualifE;
by rewrite ?normr_ge0 ?dnorm_ge0 //; apply: CauchySchwarz.
Qed.

Lemma triangle_lerif u v :
  sqrtC '[u + v] <= sqrtC '[u] + sqrtC '[v]
           ?= iff ~~ free [:: u; v] && (0 <= coord [tuple v] 0 u).
Proof.
rewrite -(mono_in_lerif ler_sqr) ?rpredD ?qualifE ?sqrtC_ge0 ?dnorm_ge0 //.
rewrite andbC sqrrD !sqrtCK addrAC dnormD (mono_lerif (ler_add2l _))/=.
rewrite -mulr_natr -[_ + _](divfK (negbT (pnatr_eq0 C 2))) -/('Re _).
rewrite (mono_lerif (ler_pmul2r _)) ?ltr0n //.
have:= lerif_trans (lerif_Re_Creal '[u, v]) (CauchySchwarz_sqrt u v).
congr (_ <= _ ?= iff _); apply: andb_id2r.
rewrite free_cons span_seq1 seq1_free -negb_or negbK orbC.
have [-> | nz_v] := altP (v =P 0); first by rewrite linear0 coord0.
case/vlineP=> [x ->]; rewrite linearZl_LR linearZ pmulr_lge0 ?dnorm_gt0 //=.
by rewrite (coord_free 0) ?seq1_free // eqxx mulr1.
Qed.

End DotFinVectTheory.

Local Notation "u '``_' i" := (u (GRing.zero (Zp_zmodType O)) i) : ring_scope.
Local Notation "''e_' i" := (delta_mx 0 i)
 (format "''e_' i", at level 3) : ring_scope.

Local Notation "M ^ phi" := (map_mx phi M).
Local Notation "M ^t phi" := (map_mx phi (M ^T)) (phi at level 30, at level 30).

Section MatrixForms.

Variables (R : fieldType) (n : nat).
Implicit Types (a b : R) (u v : 'rV[R]_n) (N P Q : 'M[R]_n).

Section Def.
Variable (theta : R -> R).

Definition form_of_matrix M u v := (u *m M *m (v ^t theta)) 0 0.
Definition matrix_of_form (form : 'rV[R]_n -> 'rV[R]_n -> R) : 'M[R]_n :=
  \matrix_(i, j) form 'e_i 'e_j.

Implicit Type form : {bilinear 'rV[R]_n -> 'rV[R]_n -> R | *%R & theta \; *%R}.

Lemma matrix_of_formE form i j : matrix_of_form form i j = form 'e_i 'e_j.
Proof. by rewrite mxE. Qed.
End Def.

Section FormOfMatrix.
Variables (M : 'M[R]_n).
Variables (theta : {rmorphism R -> R}).

Local Notation "''[' u , v ]" := (form_of_matrix theta M u%R v%R) : ring_scope.
Local Notation "''[' u ]" := '[u, u]%R : ring_scope.

Lemma form_of_matrix_is_linear u :
  linear_for (theta \; *%R) (form_of_matrix theta M u).
Proof.
rewrite /form_of_matrix => k v w.
by rewrite linearD map_mxD linearZ map_mxZ !mulmxDr -scalemxAr !mxE.
Qed.
Canonical form_of_matrix_additive u := Additive (form_of_matrix_is_linear u).
Canonical form_of_matrix_linear u := Linear (form_of_matrix_is_linear u).

Definition form_of_matrixr u := (form_of_matrix theta M)^~u.
Lemma form_of_matrixr_is_linear u : linear_for *%R (form_of_matrixr u).
Proof.
rewrite /form_of_matrixr /form_of_matrix => k v w.
by rewrite !mulmxDl -!scalemxAl !mxE.
Qed.
Canonical form_of_matrixr_additive u := Additive (form_of_matrixr_is_linear u).
Canonical form_of_matrixr_linear u := Linear (form_of_matrixr_is_linear u).
Canonical form_of_matrixr_rev :=
  [revop form_of_matrixr of form_of_matrix theta M].
Canonical form_of_matrix_is_bilinear := [bilinear of form_of_matrix theta M].

Lemma formee i j : '['e_i, 'e_j] = M i j.
Proof.
rewrite /form_of_matrix -rowE -map_trmx map_delta_mx -[M in LHS]trmxK.
by rewrite -tr_col -trmx_mul -rowE !mxE.
Qed.

Lemma form_of_matrixK : matrix_of_form (form_of_matrix theta M) = M.
Proof. by apply/matrixP => i j; rewrite !mxE formee. Qed.

Lemma form0_eq0 : M = 0 -> forall u v, '[u, v] = 0.
Proof. by rewrite /form_of_matrix => -> u v; rewrite mulmx0 mul0mx mxE. Qed.

End FormOfMatrix.

Section MatrixOfForm.
Variable (theta : {rmorphism R -> R}).
Variable (form : {bilinear 'rV[R]_n -> 'rV[R]_n -> R | *%R & theta \; *%R}).

Lemma matrix_of_formK : form_of_matrix theta (matrix_of_form form) =2 form.
Proof.
set f := (X in X =2 _); have f_eq i j : f 'e_i 'e_j = form 'e_i 'e_j.
  by rewrite /f formee mxE.
move=> u v; rewrite [u]row_sum_delta [v]row_sum_delta /f.
rewrite !linear_sum/=; apply: eq_bigr => j _.
rewrite !linear_suml/=; apply: eq_bigr => i _.
by rewrite !linearZ/= !linearZl_LR/= -f_eq.
Qed.

End MatrixOfForm.

Section HermitianMx.
Variable (eps : bool).

Section HermitianMxDef.
Variable (theta : R -> R).

Definition hermitian_mx_pred :=
  [qualify M : 'M_n | M == ((-1) ^+ eps) *: M ^t theta].
Fact hermitian_mx_key : pred_key hermitian_mx_pred. Proof. by []. Qed.
Canonical hermitian_mx_keyed := KeyedQualifier hermitian_mx_key.

Structure hermitian_mx := HermitianMx {
  mx_of_hermitian :> 'M[R]_n;
  _ : mx_of_hermitian \is hermitian_mx_pred
}.

Lemma hermitian_mxE (M : hermitian_mx) :
  M = ((-1) ^+ eps) *: M ^t theta :> 'M__.
Proof. by apply/eqP; case: M. Qed.

Lemma trmx_hermitian (M : hermitian_mx) :
  M^T = ((-1) ^+ eps) *: M ^ theta :> 'M__.
Proof. by rewrite {1}hermitian_mxE linearZ /= map_trmx trmxK. Qed.

End HermitianMxDef.

Section HermitianMxTheory.
Variables (theta : {involutive_rmorphism R}) (M : hermitian_mx theta).

Lemma maptrmx_hermitian : M^t theta = (-1) ^+ eps *: (M : 'M__).
Proof.
rewrite trmx_hermitian map_mxZ rmorph_sign -map_mx_comp.
by rewrite (eq_map_mx_id _ (rmorphK _)).
Qed.

Lemma form_of_matrix_is_hermitian :
  hermitian_for eps theta (form_of_matrix theta M).
Proof.
move=> /= u v; rewrite {1}hermitian_mxE /form_of_matrix -scalemxAr.
rewrite -scalemxAl -!mulmxA -map_mxM -trmx_mul mxE; congr (_ * _).
transitivity (theta (((u *m (v *m M) ^t theta) ^t theta) 0 0)).
  by rewrite !mxE rmorphK.
congr (theta (_ 0 0)); rewrite !(trmx_mul, map_mxM, map_trmx, trmxK).
by rewrite -!map_mx_comp !(eq_map_mx_id _ (rmorphK _)) mulmxA.
Qed.

Canonical form_of_matrix_hermitian := Hermitian form_of_matrix_is_hermitian.

Local Notation "''[' u , v ]" := (form_of_matrix theta M u%R v%R) : ring_scope.
Local Notation "''[' u ]" := '[u, u]%R : ring_scope.

Definition orthomx m (B : 'M_(m,n)) := (kermx (M *m (B ^t theta))).
Local Notation "B ^_|_" := (orthomx B) : ring_scope.
Local Notation "A _|_ B" := (A%MS <= B^_|_)%MS : ring_scope.

Lemma orthomxE u v : (u _|_ v) = ('[u, v] == 0).
Proof.
by rewrite (sameP sub_kermxP eqP) mulmxA [_ *m _^t _]mx11_scalar fmorph_eq0.
Qed.

Lemma hermimx_eq0P {u v} : reflect ('[u, v] = 0) (u _|_ v).
Proof. by rewrite orthomxE; apply/eqP. Qed.

Lemma orthomxP p q (A : 'M_(p, n)) (B :'M_(q, n)) :
  reflect (forall (u v : 'rV_n), (u <= A)%MS -> (v <= B)%MS -> u _|_ v)
          (A _|_ B).
Proof.
apply: (iffP idP) => AnB.
  move=> u v uA vB; rewrite (submx_trans uA) // (submx_trans AnB) //.
  apply/sub_kermxP; have /submxP [w ->] := vB.
  rewrite trmx_mul map_mxM !mulmxA -[kermx _ *m _ *m _]mulmxA.
  by rewrite [kermx _ *m _](sub_kermxP _) // mul0mx.
apply/rV_subP => u /AnB /(_ _) /sub_kermxP uMv; apply/sub_kermxP.
suff: forall m (v : 'rV[R]_m),
  (forall i, v *m 'e_i ^t theta = 0 :> 'M_1) -> v = 0.
  apply => i; rewrite !mulmxA -!mulmxA -map_mxM -trmx_mul uMv //.
  by apply/submxP; exists 'e_i.
move=> /= m v Hv; apply: (can_inj (@trmxK _ _ _)).
rewrite trmx0; apply/row_matrixP=> i; rewrite row0 rowE.
apply: (can_inj (@trmxK _ _ _)); rewrite trmx0 trmx_mul trmxK.
by rewrite -(map_delta_mx theta) map_trmx Hv.
Qed.

Lemma orthomxC p q (A : 'M_(p, n)) (B :'M_(q, n)) : (A _|_ B) = (B _|_ A).
Proof.
gen have nC : p q A B / A _|_ B -> B _|_ A; last by apply/idP/idP; apply/nC.
move=> AnB; apply/orthomxP => u v ? ?; rewrite orthomxE.
rewrite hermC mulf_eq0 ?fmorph_eq0 ?signr_eq0 /=.
by rewrite -orthomxE (orthomxP _ _ AnB).
Qed.

Lemma orthomx_ortho_mx p (A : 'M_(p, n)) : ((A^_|_) _|_ A).
Proof. by []. Qed.

Lemma orthomx_mx_ortho p (A : 'M_(p, n)) : (A _|_ (A^_|_)).
Proof. by rewrite orthomxC. Qed.

Lemma rank_orthomx u : (\rank (u ^_|_) >= n.-1)%N.
Proof.
rewrite mxrank_ker -subn1 leq_sub2l //.
by rewrite (leq_trans (mxrankM_maxr  _ _)) // rank_leq_col.
Qed.

Definition radmx := 1%:M^_|_.

Lemma radmx_ker : radmx = kermx M.
Proof. by rewrite /radmx /orthomx trmx1 map_mx1 mulmx1. Qed.

End HermitianMxTheory.
End HermitianMx.

(* Notation "eps_theta .-sesqui" := (sesqui _ eps_theta) *)
(*   (at level 2, format "eps_theta .-sesqui") : ring_scope. *)

(* Notation symmetric := (false, [rmorphism of idfun]).-sesqui. *)
(* Notation skew := (true, [rmorphism of idfun]).-sesqui. *)
(* Notation hermitian := (false, @conjC _).-sesqui. *)

End MatrixForms.

Section TEST_classfun.
From mathcomp Require Import classfun.

Canonical rev_cfdot (gT : finGroupType) (B : {set gT}) :=
  @RevOp _ _ _ (@cfdotr_head gT B tt)
  (@cfdot gT B) (fun _ _ => erefl).

Section Cfdot.
Variables (gT : finGroupType) (G : {group gT}).
Lemma cfdot_is_linear xi : linear_for (@conjC _ \; *%R) (cfdot xi : 'CF(G) -> algC^o).
Proof.
move=> /= a phi psi; rewrite cfdotC -cfdotrE linearD linearZ /=.
by rewrite !['[_, xi]]cfdotC rmorphD rmorphM !conjCK.
Qed.
Canonical cfdot_additive xi := Additive (cfdot_is_linear xi).
Canonical cfdot_linear xi := Linear (cfdot_is_linear xi).
Canonical cfdot_bilinear := [bilinear of @cfdot gT G].

Lemma cfdotC_subproof (phi psi : 'CF(G)) : '[phi, psi] = (-1) ^+ false * ('[psi, phi])^*.
Proof. by rewrite mul1r cfdotC. Qed.

Definition cfdot_is_hermitian : hermitian_for false conjC (@cfdot gT G).
Proof. by move=> *; rewrite mul1r cfdotC. Qed.
Canonical cfdot_hermsym := Hermitian cfdot_is_hermitian.

Definition cfdot_is_dot : is_dot (@cfdot gT G).
Proof. by move=> phi phi_neq0; rewrite cfnorm_gt0. Qed.
Canonical cfdot_dot := Dot cfdot_is_dot.

Section examples.

Lemma cfdot0l P (xi xi1 xi2 : 'CF(G)) : P '[xi1 + xi2, xi].
Proof. rewrite linearDl /=. Abort.

Lemma cfCauchySchwarz (phi psi : 'CF(G)) :
  `|'[phi, psi]| ^+ 2 <= '[phi] * '[psi] ?= iff ~~ free (phi :: psi).
Proof.
exact: CauchySchwarz.
Abort.

End examples.
End Cfdot.

End TEST_classfun.

(* Section ClassificationForm. *)

(* Variables (F : fieldType) (L : fieldExtType) (theat : 'Aut()) *)

(* Notation "''[' u , v ]_ M" := (form M%R u%R v%R) : ring_scope. *)
(* Notation "''[' u ]_ M" := (form M%R u%R u%R) : ring_scope. *)

(* Hypothesis (thetaK : involutive theta). *)

(* Lemma sesqui_test M : (forall u v, '[v, u]_M = 0 -> '[u, v]_M = 0) -> *)
(*                       {eps | eps^+2 = 1 & M \is (eps,theta).-sesqui}. *)
(* Proof. *)
(* pose  *)

(*                       [/\ forall u, '[u] = 0, theta =1 id & eps = -1] *)
(*                       \/ ((exists u, '[u] != 0) /\ (eps = 1)). *)
(* Proof. *)
(* move=> M_neq0 form_eq0. *)
(* have [] := boolP [forall i : 'I_n, '['e_i] == 0]; last first. *)
(*   rewrite negb_forall => /existsP [i ei_neq0]. *)
(*   right; split; first by exists ('e_i). *)
(*   apply/eqP; *)

(*  contraT *)

(* suff [f_eq0|] : (forall u, '[u] = 0) \/ (exists u, '[u] != 0). *)
(*   left; split=> //. *)

(* have [] := boolP [forall i : 'I_n, '['e_i] == 0]. *)

(* suff /eqP : eps ^+ 2 = 1. *)
(*   rewrite -subr_eq0 subr_sqr_1 mulf_eq0. *)
(*   move => /orP[]; rewrite addr_eq0 ?opprK=> /eqP eps_eq. *)
(*     right; split=> //. *)

(* have [] := boolP [forall i : 'I_n, '['e_i] == 0]. *)

(* have := sesquiC u u. *)

(* rewrite !linearZ /= -[eps *: _ *m _]/(mulmxr _ _) linearZ /= mxE; congr (_ * _). *)
(* have : u = map_mx theta (map_mx theta u). *)
(*   apply/rowP=> i; rewrite !mxE. *)
(* rewrite -[in LHS]mulmxA -map_mxM. *)
(* rewrite  *)
(*  !mxE rmorph_sum; apply: eq_bigr => /= i _; rewrite !mxE. *)
(* rewrite !rmorphM thetaK rmorph_sum. *)

(* Hypothesis (M_sesqui : M \is (eps, theta).-sesqui). *)

(* rewrite -[a *: u *m _]/(mulmxr _ _). *)
(* rewrite linearZ. *)

(* Variables (R : fieldType) (n : nat). *)

(* Local Notation "A _|_ B" := (A%MS <= kermx B%MS^T)%MS. *)

(* Lemma orthomx_sym k m (A : 'M[R]_(k,n)) (B : 'M[R]_(m,n)) : *)
(*   A _|_ B = B _|_ A. *)
(* Proof. *)
(* rewrite !(sameP sub_kermxP eqP) -{1}[A]trmxK -trmx_mul. *)
(* by rewrite -{1}trmx0 (inj_eq (@trmx_inj _ _ _)). *)
(* Qed. *)

(* Lemma orthomxNm k m (A : 'M[R]_(k,n)) (B : 'M[R]_(m,n)) : (- A) _|_ B = A _|_ B. *)
(* Proof. by rewrite eqmx_opp. Qed. *)

(* Lemma orthomxmN k m (A : 'M[R]_(k,n)) (B : 'M[R]_(m,n)) : A _|_ (- B) = A _|_ B. *)
(* Proof. by rewrite ![A _|_ _]orthomx_sym orthomxNm. Qed. *)

(* Lemma orthomxDm k m p (A : 'M[R]_(k,n)) (B : 'M[R]_(m,n)) (C : 'M[R]_(p,n)) : *)
(*   (A + B _|_ C) = (A _|_ C) && (B _|_ C). *)
(* Proof. by rewrite addsmxE !(sameP sub_kermxP eqP) mul_col_mx col_mx_eq0. Qed. *)

(* Lemma orthomxmD  k m p (A : 'M[R]_(k,n)) (B : 'M[R]_(m,n)) (C : 'M[R]_(p,n)) : *)
(*   (A _|_ B + C) = (A _|_ B) && (A _|_ C). *)
(* Proof. by rewrite ![A _|_ _]orthomx_sym orthomxDm. Qed. *)

(* Definition dot (u v : 'rV[R]_n) : R := (u *m v^T) 0 0. *)

(* Notation "''[' u , v ]" := (dot u v) : ring_scope. *)
(* Notation "''[' u ]" := '[u, u]%MS : ring_scope. *)

(* Lemma dotmulE (u v : 'rV[R]_n) : '[u, v] = \sum_k u``_k * v``_k. *)
(* Proof. by rewrite [LHS]mxE; apply: eq_bigr=> i; rewrite mxE. Qed. *)

(* Lemma orthomxvv (u v : 'rV[R]_n) : (u _|_ v) = ('[u, v] == 0). *)
(* Proof. by rewrite (sameP sub_kermxP eqP) [_ *m _^T]mx11_scalar fmorph_eq0. Qed. *)

(* End Orthomx. *)

(* Local Notation "''[' u , v ]" := (form u v) : ring_scope. *)
(* Local Notation "''[' u ]" := '[u%R, u%R] : ring_scope. *)
(* Local Notation "A _|_ B" := (A%MS <= kermx B%MS^T)%MS. *)

