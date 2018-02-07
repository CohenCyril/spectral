From mathcomp
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq div choice fintype.
From mathcomp
Require Import bigop ssralg finset fingroup zmodp poly polydiv ssrnum.
From mathcomp
Require Import matrix mxalgebra vector falgebra complex algC algnum.
From mathcomp
Require Import complex fieldext mxpoly.
From mathcomp Require Import vector.
 (* finmap multiset. *)

Require Import forms.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Local Notation stable V f := (V%MS *m f%R <= V%MS)%MS.
Section Stability.

Variable (F : fieldType).
Variable (n' : nat). Let n := n'.+1.
Implicit Types (f g : 'M[F]_n).

Lemma comm_stable (f g : 'M[F]_n) : GRing.comm f g -> stable f g.
Proof. by move=> comm_fg; rewrite [_ *m _]comm_fg mulmx_sub. Qed.

Lemma comm_stable_ker (f g : 'M[F]_n) : GRing.comm f g ->
                                        stable (kermx f) g.
Proof.
move=> comm_fg; apply/sub_kermxP.
by rewrite -mulmxA -[g *m _]comm_fg mulmxA mulmx_ker mul0mx.
Qed.

Lemma commrC (f : 'M[F]_n) (a : F) : GRing.comm f a%:M.
Proof. by rewrite /GRing.comm [_ * _]mul_mx_scalar [_ * _]mul_scalar_mx. Qed.

Lemma commr_poly (R : ringType) (a b : R) (p : {poly R}) :
      GRing.comm a b -> comm_coef p a -> GRing.comm a p.[b].
Proof.
move=> comm_ab. elim/poly_ind: p => [|p c]; rewrite !hornerE.
  move=> _; exact: commr0.
rewrite !hornerE_comm => comm_apb comm_coef_pXca.
apply/commrD; last first.
  by have := comm_coef_pXca 0%N; rewrite coefD coefMX add0r coefC eqxx.
apply/commrM => //; apply/comm_apb => i.
by have := comm_coef_pXca i.+1; rewrite coefD coefMX coefC /= addr0.
Qed.

Lemma commr_mxpoly (f g : 'M[F]_n) (p : {poly F}) : GRing.comm f g ->
  GRing.comm f (horner_mx g p).
Proof.
move=> comm_fg; apply: commr_poly => // i.
by rewrite coef_map /=; apply/commr_sym/commrC.
Qed.

Lemma comm_stable_eigenspace (f g : 'M[F]_n) a : GRing.comm f g ->
  stable (eigenspace f a) g.
Proof.
move=> comm_fg; rewrite comm_stable_ker //.
by apply/commr_sym/commrD=> //; apply/commrN/commrC.
Qed.

Definition geneigenspace g a := kermx ((g - a%:M) ^+ n).

Lemma comm_stable_geneigenspace (f g : 'M[F]_n) a : GRing.comm f g ->
  stable (geneigenspace f a) g.
Proof.
move=> comm_fg; rewrite comm_stable_ker //.
by apply/commr_sym/commrX/commrD=> //; apply/commrN/commrC.
Qed.

End Stability.

Section Spectral.

Variable (C : numClosedFieldType).
Set Default Proof Using "C".

Local Notation "M ^ phi" := (map_mx phi M).
Local Notation "M ^t*" := (map_mx conjC (M ^T)) (at level 30).

Lemma trmxCK m n (M : 'M[C]_(m, n)) : M^t*^t* = M.
Proof. by apply/matrixP=> i j; rewrite !mxE conjCK. Qed.

Definition unitary {m n} := [qualify M : 'M[C]_(m, n) | M *m M ^t* == 1%:M].
Fact unitary_key m n : pred_key (@unitary m n). Proof. by []. Qed.
Canonical unitary_keyed m n := KeyedQualifier (unitary_key m n).

Definition normalmx {n} := [qualify M : 'M[C]_n | M *m M ^t* == M ^t* *m M].
Fact normalmx_key n : pred_key (@normalmx n). Proof. by []. Qed.
Canonical normalmx_keyed n := KeyedQualifier (normalmx_key n).

Lemma normalmxP {n} {M: 'M[C]_n} :
  reflect (M *m M ^t* = M ^t* *m M) (M \is normalmx).
Proof. exact: eqP. Qed.

Local Notation "B ^_|_" := (ortho (@conjC _) 1%:M B) : ring_scope.
Local Notation "A _|_ B" := (A%MS <= B^_|_)%MS : ring_scope.

Local Notation "''[' u , v ]" := (form (@conjC _) 1%:M u%R v%R) : ring_scope.
Local Notation "''[' u ]" := '[u, u]%R : ring_scope.

Fact form1_sesqui n : (1%:M : 'M[C]_n) \is hermitian.
Proof.
by rewrite qualifE /= expr0 scale1r tr_scalar_mx map_scalar_mx conjC1.
Qed.
Let form1_sesqui_hint := form1_sesqui.

Lemma normal1E m n p (A : 'M[C]_(m, n)) (B : 'M_(p, n)) :
  A _|_ B = (A *m B^t* == 0).
Proof. by apply/sub_kermxP/eqP; rewrite !mul1mx. Qed.

Lemma normal1P {m n p : nat} {A : 'M[C]_(m, n)} {B : 'M_(p, n)} :
  reflect (A *m B^t* = 0) (A _|_ B).
Proof. by rewrite normal1E; apply: eqP. Qed.

Lemma form1_ge0 n (u : 'rV[C]_n) : '[u] >= 0.
Proof.
by rewrite /form mulmx1 mxE sumr_ge0 => // i _; rewrite !mxE mul_conjC_ge0.
Qed.
Hint Resolve form1_ge0.

Lemma form1_eq0 n (u : 'rV[C]_n) : ('[u] == 0) = (u == 0).
Proof.
apply/idP/eqP; last by move->; rewrite form0r.
rewrite /form mulmx1 mxE psumr_eq0 /=; last first.
  by move=> i _; rewrite !mxE mul_conjC_ge0.
move=> all_eq0;  apply/rowP=> i; rewrite mxE.
have /allP /(_ i) := all_eq0; rewrite mem_index_enum.
by rewrite !mxE mul_conjC_eq0 => /(_ _) /eqP->.
Qed.

Lemma form1_gt0 n (u : 'rV[C]_n) : ('[u] > 0) = (u != 0).
Proof. by rewrite ltr_def form1_ge0 form1_eq0 andbT. Qed.

Lemma normalmx_disj n p q (A : 'M[C]_(p, n)) (B :'M_(q, n)) :
  A _|_ B -> (A :&: B = 0)%MS.
Proof.
move=> nAB; apply/eqP/rowV0Pn => [[v]]; rewrite sub_capmx => /andP [vA vB].
by apply/negP; rewrite negbK -form1_eq0 -normalE (normalP _ _ _ _ nAB).
Qed.

Lemma normalmx_ortho_disj n p (A : 'M[C]_(p, n)) : (A :&: A^_|_ = 0)%MS.
Proof.
by apply/normalmx_disj/(@normal_mx_ortho _ _ false)=> //; apply/conjCK.
Qed.

Lemma rank_ortho p n (A : 'M[C]_(p, n)) : \rank A^_|_ = (n - \rank A)%N.
Proof. by rewrite mxrank_ker mul1mx mxrank_map mxrank_tr. Qed.

Lemma add_rank_ortho p n (A : 'M[C]_(p, n)) : (\rank A + \rank A^_|_)%N = n.
Proof. by rewrite rank_ortho subnKC ?rank_leq_col. Qed.

Lemma addsmx_ortho p n (A : 'M[C]_(p, n)) : (A + A^_|_ :=: 1%:M)%MS.
Proof.
apply/eqmxP/andP; rewrite submx1; split=> //.
rewrite -mxrank_leqif_sup ?submx1 ?mxrank1 ?(mxdirectP _) /= ?add_rank_ortho //.
by rewrite mxdirect_addsE /= ?mxdirectE ?normalmx_ortho_disj !eqxx.
Qed.

Definition normalC n :=
  (@normalC _ _ _ _ _ (@conjCK _) (form1_sesqui n)).

Definition normal_mx_ortho n :=
  (@normal_mx_ortho _ _ _ _ _ (@conjCK _) (form1_sesqui n)).

Lemma normalZl p m n a (A : 'M[C]_(p, n)) (B : 'M[C]_(m, n)) : a != 0 ->
  a *: A _|_ B = A _|_ B.
Proof. by move=> a_neq0; rewrite eqmx_scale. Qed.

Lemma normalZr p m n a (A : 'M[C]_(p, n)) (B : 'M[C]_(m, n)) : a != 0 ->
  A _|_ (a *: B) = A _|_ B.
Proof. by move=> a_neq0; rewrite normalC normalZl // normalC. Qed.

Lemma eqmx_ortho p m n (A : 'M[C]_(p, n)) (B : 'M[C]_(m, n)) :
  (A :=: B)%MS -> (A^_|_ :=: B^_|_)%MS.
Proof.
move=> eqAB; apply/eqmxP.
by rewrite normalC -eqAB normal_mx_ortho normalC eqAB normal_mx_ortho.
Qed.

Lemma genmx_ortho p n (A : 'M[C]_(p, n)) : (<<A>>^_|_ :=: A^_|_)%MS.
Proof. exact: (eqmx_ortho (genmxE _)). Qed.

Lemma ortho_id p n (A : 'M[C]_(p, n)) : (A^_|_^_|_ :=: A)%MS.
Proof.
apply/eqmx_sym/eqmxP.
by rewrite -mxrank_leqif_eq 1?normalC // !rank_ortho subKn // ?rank_leq_col.
Qed.

Lemma submx_ortho (p m n : nat) (U : 'M[C]_(p, n)) (V : 'M_(m, n)) :
  (U^_|_ <= V^_|_)%MS = (V <= U)%MS.
Proof. by rewrite normalC ortho_id. Qed.

Definition proj_ortho p n (U : 'M[C]_(p, n)) := proj_mx <<U>>%MS U^_|_%MS.

Let sub_adds_genmx_ortho (p m n : nat) (U : 'M[C]_(p, n))  (W : 'M_(m, n)) :
  (W <= <<U>> + U^_|_)%MS.
Proof.
by rewrite !(adds_eqmx (genmxE _) (eqmx_refl _)) addsmx_ortho submx1.
Qed.

Let cap_genmx_ortho (p n : nat) (U : 'M[C]_(p, n)) : (<<U>> :&: U^_|_)%MS = 0.
Proof.
apply/eqmx0P; rewrite !(cap_eqmx (genmxE _) (eqmx_refl _)).
by rewrite normalmx_ortho_disj; apply/eqmx0P.
Qed.

Lemma proj_ortho_sub (p m n : nat) (U : 'M_(p, n)) (W : 'M_(m, n)) :
   (W *m proj_ortho U <= U)%MS.
Proof. by rewrite (submx_trans (proj_mx_sub _ _ _)) // genmxE. Qed.

Lemma proj_ortho_compl_sub (p m n : nat) (U : 'M_(p, n)) (W : 'M_(m, n)) :
  (W - W *m proj_ortho U <= U^_|_)%MS.
Proof. by rewrite proj_mx_compl_sub // addsmx_ortho submx1. Qed.

Lemma proj_ortho_id (p m n : nat) (U : 'M_(p, n)) (W : 'M_(m, n)) :
   (W <= U)%MS -> W *m proj_ortho U = W.
Proof. by move=> WU; rewrite proj_mx_id ?genmxE. Qed.

Lemma proj_ortho_0 (p m n : nat) (U : 'M_(p, n)) (W : 'M_(m, n)) :
    (W <= U^_|_)%MS -> W *m proj_ortho U = 0.
Proof. by move=> WUo; rewrite proj_mx_0. Qed.

Lemma add_proj_ortho (p m n : nat) (U : 'M_(p, n)) (W : 'M_(m, n)) :
  W *m proj_ortho U + W *m proj_ortho U^_|_ = W.
Proof.
rewrite -[W in LHS](@add_proj_mx _ _ _ <<U>>%MS U^_|_ W) //.
rewrite !mulmxDl proj_ortho_id ?proj_ortho_sub //.
rewrite proj_ortho_0 ?proj_mx_sub // addr0.
rewrite proj_ortho_0 ?ortho_id ?proj_ortho_sub // add0r.
by rewrite proj_ortho_id ?proj_mx_sub // add_proj_mx.
Qed.

Lemma proj_ortho_proj (m n : nat) (U : 'M_(m, n)) :
   let P := proj_ortho U in P *m P = P.
Proof. by rewrite /= proj_mx_proj. Qed.

Lemma proj_orthoE (p n : nat) (U : 'M_(p, n)) : (proj_ortho U :=: U)%MS.
Proof.
apply/eqmxP/andP; split; first by rewrite -proj_ortho_proj proj_ortho_sub.
by rewrite -[X in (X <= _)%MS](proj_ortho_id (submx_refl U)) mulmx_sub.
Qed.

Lemma normal_proj_mx_ortho (p p' m m' n : nat)
  (A : 'M_(p, n)) (A' : 'M_(p', n))
  (W : 'M_(m, n)) (W' : 'M_(m', n)) :
  A _|_ A' -> W *m proj_ortho A _|_ W' *m proj_ortho A'.
Proof.
rewrite normalC=> An.
rewrite mulmx_sub // normalC (eqmx_ortho (proj_orthoE _)).
by rewrite (submx_trans _ An) // proj_ortho_sub.
Qed.

CoInductive unsplit_spec m n (i : 'I_(m + n)) : 'I_m + 'I_n -> bool -> Type :=
  | UnsplitLo (j : 'I_m) of i = lshift _ j : unsplit_spec i (inl _ j) true
  | UnsplitHi (k : 'I_n) of i = rshift _ k : unsplit_spec i (inr _ k) false.

Lemma unsplitP m n (i : 'I_(m + n)) : unsplit_spec i (split i) (i < m)%N.
Proof. by case: splitP=> j eq_j; constructor; apply/val_inj. Qed.

Lemma unitaryP  {m} {n} {M : 'M[C]_(m, n)} :
  reflect (M *m M^t* = 1%:M) (M \is unitary).
Proof. by apply: (iffP eqP). Qed.

Lemma mxrank_unitary m n (M : 'M[C]_(m, n)) : M \is unitary -> \rank M = m.
Proof.
rewrite qualifE => /eqP /(congr1 mxrank); rewrite mxrank1 => rkM.
apply/eqP; rewrite eqn_leq rank_leq_row /= -[X in (X <= _)%N]rkM.
by rewrite mxrankM_maxl.
Qed.

Lemma row_unitaryP {m n} {M : 'M[C]_(m, n)} :
  reflect (forall i j, '[row i M, row j M] = (i == j)%:R) (M \is unitary).
Proof.
apply: (iffP eqP).
  move=> Mo i j; have /matrixP /(_ i j) := Mo; rewrite !mxE => <-.
  by rewrite /form mulmx1 !mxE; apply: eq_bigr => /= k _; rewrite !mxE.
move=> Mo; apply/matrixP=> i j; rewrite !mxE.
have := Mo i j; rewrite /form mulmx1 !mxE => <-.
by apply: eq_bigr => /= k _; rewrite !mxE.
Qed.

Lemma mul_unitary m n p (A : 'M[C]_(m, n)) (B : 'M[C]_(n, p)) :
  A \is unitary -> B \is unitary -> A *m B \is unitary.
Proof.
move=> Aunitary Bunitary; apply/unitaryP; rewrite trmx_mul map_mxM.
by rewrite mulmxA -[A *m _ *m _]mulmxA !(unitaryP _, mulmx1).
Qed.

Lemma unitary_unit n (M : 'M[C]_n) : M \is unitary -> M \in unitmx.
Proof. by move=> /unitaryP /mulmx1_unit []. Qed.

Lemma inv_unitary n (M : 'M[C]_n) : M \is unitary -> invmx M = M^t*.
Proof.
move=> Munitary; apply: (@row_full_inj _ _ _ _ M).
  by rewrite row_full_unit unitary_unit.
by rewrite mulmxV ?unitary_unit ?(unitaryP _).
Qed.

Lemma row_id m n (M : 'rV[C]_n) : row m M = M.
Proof. by apply/matrixP=> i j; rewrite !mxE; rewrite !ord1. Qed.

Lemma row_usubmx m n p (M : 'M[C]_(m + n, p)) i :
  row i (usubmx M) = row (lshift n i) M.
Proof. by apply/rowP=> j; rewrite !mxE; congr (M _ _); apply/val_inj. Qed.

Lemma row_dsubmx m n p (M : 'M[C]_(m + n, p)) i :
  row i (dsubmx M) = row (rshift m i) M.
Proof. by apply/rowP=> j; rewrite !mxE; congr (M _ _); apply/val_inj. Qed.

Lemma col_lsubmx m n p (M : 'M[C]_(m, n + p)) i :
  col i (lsubmx M) = col (lshift p i) M.
Proof. by apply/colP=> j; rewrite !mxE; congr (M _ _); apply/val_inj. Qed.

Lemma col_rsubmx m n p (M : 'M[C]_(m, n + p)) i :
  col i (rsubmx M) = col (rshift n i) M.
Proof. by apply/colP=> j; rewrite !mxE; congr (M _ _); apply/val_inj. Qed.

Lemma schmidt_subproof m n (A : 'M[C]_(m, n)) : (m <= n)%N ->
  exists2 B : 'M_(m, n), B \is unitary & [forall i : 'I_m,
   (row i A <= (\sum_(k < m | (k <= i)%N) <<row k B>>))%MS
   && ('[row i A, row i B] >= 0) ].
Proof.
elim: m A => [|m IHm].
  exists (pid_mx n); first by rewrite qualifE !thinmx0.
  by apply/forallP=> -[].
rewrite -addn1 => A leq_Sm_n.
have lemSm: (m <= m + 1)%N by rewrite addn1.
have ltmSm: (m < m + 1)%N by rewrite addn1.
have lemn : (m <= n)%N by rewrite ltnW // -addn1.
have [B Bortho] := IHm (usubmx A) lemn.
move=> /forallP /= subAB.
have [v /and4P [vBn v_neq0 dAv_ge0 dAsub]] :
  exists v, [&& B _|_ v, v != 0, '[dsubmx A, v] >= 0 & (dsubmx A <= B + v)%MS].
  have := add_proj_ortho B (dsubmx A).
  set BoSn := (_ *m proj_ortho _^_|_) => pBE.
  have [BoSn_eq0|BoSn_neq0] := eqVneq BoSn 0.
    rewrite BoSn_eq0 addr0 in pBE.
    have /rowV0Pn [v vBn v_neq0] : B^_|_ != 0.
      rewrite -mxrank_eq0 rank_ortho -lt0n subn_gt0.
      by rewrite mxrank_unitary // -addn1.
    rewrite normalC in vBn.
    exists v; rewrite vBn v_neq0 -pBE (form_eq0P conjC _ _) ?lerr //=.
      rewrite (submx_trans (proj_ortho_sub _ _)) //.
      by rewrite -{1}[B]addr0 addmx_sub_adds ?sub0mx.
    by rewrite (submx_trans _ vBn) // proj_ortho_sub.
  pose c := (sqrtC '[BoSn])^-1; have c_gt0 : c > 0.
    by rewrite invr_gt0 sqrtC_gt0 ltr_def ?form1_eq0 ?form1_ge0 BoSn_neq0.
  exists BoSn; apply/and4P; split => //.
  - by rewrite normalC ?proj_ortho_sub // /gtr_eqF.
  - rewrite -pBE formDl // [X in X + '[_]](form_eq0P _ _ _) ?add0r //.
    by rewrite normal_proj_mx_ortho // normalC.
  - by rewrite -pBE addmx_sub_adds // proj_ortho_sub.
wlog nv_eq1 : v vBn v_neq0 dAv_ge0 dAsub / '[v] = 1.
  pose c := (sqrtC '[v])^-1.
  have c_gt0 : c > 0 by rewrite invr_gt0 sqrtC_gt0 ?form1_gt0.
  have [c_ge0 c_eq0F] := (ltrW c_gt0, gtr_eqF c_gt0).
  move=> /(_ (c *: v)); apply.
  - by rewrite normalZr ?c_eq0F.
  - by rewrite scaler_eq0 c_eq0F.
  - by rewrite formZr mulr_ge0 // conjC_ge0.
  - by rewrite (submx_trans dAsub) // addsmxS // eqmx_scale // c_eq0F.
  - rewrite formZ -normCK normfV ger0_norm ?sqrtC_ge0 ?form1_ge0 //.
    by rewrite exprVn rootCK ?mulVf // form1_eq0.
exists (col_mx B v).
  apply/row_unitaryP => i j.
  case: (unsplitP i) => {i} i ->; case: (unsplitP j) => {j} j ->;
  rewrite ?(rowKu, rowKd, row_id, ord1) -?val_eqE /= ?(row_unitaryP _) //= ?addn0.
  - by rewrite ltn_eqF // (form_eq0P _ _ _) // (submx_trans _ vBn) // row_sub.
  - rewrite gtn_eqF // (form_eq0P _ _ _) //.
    by rewrite normalC (submx_trans _ vBn) // row_sub.
  - by rewrite eqxx.
apply/forallP => i; case: (unsplitP i) => j -> /=.
  have /andP [sABj dot_gt0] := subAB j.
  rewrite rowKu -row_usubmx (submx_trans sABj) //=.
  rewrite (eq_rect _ (submx _) (submx_refl _)) //.
  rewrite [in RHS](reindex (lshift 1)) /=.
    by apply: eq_bigr=> k k_le; rewrite rowKu.
  exists (fun k => insubd j k) => k; rewrite inE /= => le_kj;
  by apply/val_inj; rewrite /= insubdK // -topredE /= (leq_ltn_trans le_kj).
rewrite rowKd -row_dsubmx !row_id ord1 ?dAv_ge0 ?andbT {j} addn0.
rewrite (bigD1 (rshift _ ord0)) /= ?addn0 ?rowKd ?row_id // addsmxC.
rewrite (submx_trans dAsub) // addsmxS ?genmxE //.
apply/row_subP => j; apply/(sumsmx_sup (lshift _ j)) => //=.
  by rewrite ltnW ?ltn_ord //= -val_eqE /= addn0 ltn_eqF.
by rewrite rowKu genmxE.
Qed.

Definition schmidt m n (A : 'M[C]_(m, n)) :=
  if (m <= n)%N =P true is ReflectT le_mn
  then projT1 (sig2_eqW (schmidt_subproof A (le_mn)))
  else A.

Lemma schmidt_unitary m n (A : 'M[C]_(m, n)) : (m <= n)%N ->
  schmidt A \is unitary.
Proof. by rewrite /schmidt; case: eqP => // ?; case: sig2_eqW. Qed.
Hint Resolve schmidt_unitary.

Lemma row_schmidt_sub m n (A : 'M[C]_(m, n)) i :
  (row i A <= (\sum_(k < m | (k <= i)%N) <<row k (schmidt A)>>))%MS.
Proof.
rewrite /schmidt; case: eqP => // ?.
   by case: sig2_eqW => ? ? /= /forallP /(_ i) /andP[].
by apply/(sumsmx_sup i) => //; rewrite genmxE.
Qed.

Lemma form1_row_schmidt m n (A : 'M[C]_(m, n)) i :
  '[row i A, row i (schmidt A)] >= 0.
Proof.
rewrite /schmidt; case: eqP => // ?.
by case: sig2_eqW => ? ? /= /forallP /(_ i) /andP[].
Qed.

Lemma schmidt_sub m n (A : 'M[C]_(m, n)) : (A <= schmidt A)%MS.
Proof.
apply/row_subP => i; rewrite (submx_trans (row_schmidt_sub _ _)) //.
by apply/sumsmx_subP => /= j le_ji; rewrite genmxE row_sub.
Qed.
Hint Resolve schmidt_sub.

Lemma eqmx_schmidt_full m n (A : 'M[C]_(m, n)) :
  row_full A -> (schmidt A :=: A)%MS.
Proof.
move=> Afull; apply/eqmx_sym/eqmxP; rewrite -mxrank_leqif_eq //.
by rewrite eqn_leq mxrankS //= (@leq_trans n) ?rank_leq_col ?col_leq_rank.
Qed.

Lemma eqmx_schmidt_free m n (A : 'M[C]_(m, n)) :
  row_free A -> (schmidt A :=: A)%MS.
Proof.
move=> Afree; apply/eqmx_sym/eqmxP; rewrite -mxrank_leqif_eq //.
by rewrite eqn_leq mxrankS //= (@leq_trans m) ?rank_leq_row // ?row_leq_rank.
Qed.

Definition schmidt_complete m n (V : 'M[C]_(m, n)) :=
  col_mx (schmidt (row_base V)) (schmidt (row_base V^_|_)).

Lemma schmidt_complete_unitary m n (V : 'M[C]_(m, n)) :
  schmidt_complete V \is unitary.
Proof.
apply/unitaryP; rewrite tr_col_mx map_row_mx mul_col_row.
rewrite !(unitaryP _) ?schmidt_unitary ?rank_leq_col //.
move=> [:nsV]; rewrite !(normal1P _) -?scalar_mx_block //;
  [abstract: nsV|]; last by rewrite normalC.
by do 2!rewrite eqmx_schmidt_free ?eq_row_base ?row_base_free // normalC.
Qed.

Lemma eigenvectorP {n} {A : 'M[C]_n} {v : 'rV_n} :
  reflect (exists a, (v <= eigenspace A a)%MS) (stable v A).
Proof. by apply: (iffP sub_rVP) => -[a] /eigenspaceP; exists a. Qed.

Lemma stable_restrict m n (A : 'M[C]_n) (V : 'M_n) (W : 'M_(m, \rank V)):
  stable V A -> stable W (restrict V A) = stable (W *m row_base V) A.
Proof.
move=> A_stabV; rewrite mulmxA -[in RHS]mulmxA.
rewrite -(submxMfree _ W (row_base_free V)) mulmxKpV //.
by rewrite mulmx_sub ?stable_row_base.
Qed.

Lemma eigenvalue_closed n (A : 'M[C]_n) : (n > 0)%N ->
   exists a, eigenvalue A a.
Proof.
move=> n_gt0; have /closed_rootP [a rAa] : size (char_poly A) != 1%N.
  by rewrite size_char_poly; case: (n) n_gt0.
by exists a; rewrite eigenvalue_root_char.
Qed.

Lemma common_eigenvector n (As : seq 'M[C]_n) :
  (n > 0)%N -> {in As &, forall A B, A *m B = B *m A} ->
  exists2 v : 'rV_n, v != 0 & all (fun A => stable v A) As.
Proof.
move: (size As) {-2}As (erefl (size As)) => sAs {As}.
elim: sAs n => [|k IHk] n As.
  move=> /eqP; rewrite size_eq0 => /eqP -> n_gt0 _.
  exists (const_mx 1); last by apply/allP.
  by apply/eqP=> /rowP /(_ (Ordinal n_gt0)) /eqP; rewrite !mxE oner_eq0.
case: As => [|A As] //= [sAs] n_gt0 As_comm.
have [a a_eigen] := eigenvalue_closed A n_gt0.
have [] := IHk _ [seq restrict (eigenspace A a) B | B <- As].
- by rewrite size_map.
- by rewrite lt0n mxrank_eq0.
- move=> _ _ /= /mapP /= [B B_in ->] /mapP /= [B' B'_in ->].
  case: n => [//|n] in A As sAs n_gt0 As_comm a_eigen B B_in B' B'_in *.
  rewrite -!restrictM ?inE /= ?comm_stable_eigenspace //
     /GRing.comm -?[_ * _]/(_ *m _);
  by rewrite As_comm //= ?mem_head ?in_cons ?B_in ?B'_in ?orbT.
case: n => [//|n] in A As sAs n_gt0 As_comm a_eigen *.
move=> v vN0 /allP /= vP.
exists (v *m (row_base (eigenspace A a))).
  by rewrite mul_mx_rowfree_eq0 ?row_base_free.
apply/andP; split.
  by apply/eigenvectorP; exists a; rewrite mulmx_sub // eq_row_base.
apply/allP => B B_in; rewrite -stable_restrict ?vP //.
  by apply/mapP; exists B => //.
rewrite comm_stable_eigenspace // /GRing.comm.
by rewrite [_ * _]As_comm ?mem_head // ?in_cons ?B_in ?orbT.
Qed.

Lemma common_eigenvector2 n (A B : 'M[C]_n) : (n > 0)%N -> A *m B = B *m A ->
  exists2 v : 'rV_n, v != 0 & (stable v A) && (stable v B).
Proof.
move=> n_gt0 AB_comm; have [] := @common_eigenvector _ [:: A; B] n_gt0.
  by move=> A' B'; rewrite !inE => /orP [] /eqP-> /orP [] /eqP->.
by move=> v v_neq0 /allP vP; exists v; rewrite ?vP ?(mem_head, in_cons, orbT).
Qed.

Definition triangular m n (A : 'M[C]_(m, n)) :=
  [forall i : 'I_m , forall j : 'I_n, (i < j)%N ==> (A i j == 0)].

Lemma triangularP {m n : nat} {A : 'M[C]_(m, n)} :
  reflect (forall i j, (val i < val j)%N -> A i j = 0) (triangular A).
Proof. by apply: (iffP 'forall_'forall_implyP) => /= /(_ _ _ _) /eqP. Qed.

Lemma mulmxtVK (m1 m2 n : nat) (A : 'M[C]_(m1, n)) (B : 'M[C]_(n, m2)) :
  B \is unitary ->  A *m B *m B^t* = A.
Proof. by move=> B_unitary; rewrite -mulmxA (unitaryP _) ?mulmx1. Qed.

Lemma mulmxKtV (m1 m2 n : nat) (A : 'M[C]_(m1, n)) (B : 'M[C]_(m2, n)) :
  B \is unitary -> m2 = n -> A *m B^t* *m B = A.
Proof.
move=> B_unitary m2E; case: _ / (esym m2E) in B B_unitary *.
by rewrite -inv_unitary // mulmxKV //; apply: unitary_unit.
Qed.

Lemma cotrigonalization n (As : seq 'M[C]_n) :
  {in As &, forall A B, A *m B = B *m A} ->
  exists2 P : 'M[C]_n, P \is unitary &
    all (fun A => triangular (P *m A *m invmx P)) As.
Proof.
elim: n {-2}n (leqnn n) As => [|N IHN] n.
  rewrite leqn0 => /eqP n_eq0.
  exists 1%:M; first by rewrite qualifE mul1mx trmx1 map_mx1.
  apply/allP => ? ?; apply/triangularP => i j.
  by suff: False by []; move: i; rewrite n_eq0 => -[].
rewrite leq_eqVlt => /predU1P [n_eqSN|/IHN//].
have /andP [n_gt0 n_small] : (n > 0)%N && (n - 1 <= N)%N.
  by rewrite n_eqSN /= subn1.
move=> As As_comm;
have [v vN0 /allP /= vP] := common_eigenvector n_gt0 As_comm.
suff: exists2 P : 'M[C]_(\rank v + \rank v^_|_, n), P \is unitary &
  all (fun A => triangular (P *m A *m (P^t*))) As.
  rewrite add_rank_ortho // => -[P P_unitary].
  by rewrite -inv_unitary //; exists P.
pose S := schmidt_complete v.
pose r A := S *m A *m S^t*.
have vSvo X : stable v X ->
  schmidt (row_base v) *m X *m schmidt (row_base v^_|_) ^t* = 0.
  move=> /eigenvectorP [a v_in].
  rewrite (eigenspaceP (_ : (_ <= _ a))%MS); last first.
    by rewrite eqmx_schmidt_free ?row_base_free ?eq_row_base.
  rewrite -scalemxAl (normal1P _) ?scaler0 //.
  by do 2!rewrite eqmx_schmidt_free ?row_base_free ?eq_row_base // normalC.
have drrE X : drsubmx (r X) =
  schmidt (row_base v^_|_) *m X *m schmidt (row_base v^_|_) ^t*.
  by rewrite /r mul_col_mx tr_col_mx map_row_mx mul_col_row block_mxKdr.
have vSv X a : (v <= eigenspace X a)%MS ->
  schmidt (row_base v) *m X *m schmidt (row_base v) ^t* = a%:M.
  move=> vXa; rewrite (eigenspaceP (_ : (_ <= _ a)%MS)); last first.
    by rewrite eqmx_schmidt_free ?row_base_free ?eq_row_base.
  by rewrite -scalemxAl (unitaryP _) ?scalemx1 ?schmidt_unitary ?rank_leq_col.
have [] := IHN _ _ [seq drsubmx (r A) | A <- As].
- by rewrite rank_ortho rank_rV vN0.
- move=> _ _ /mapP[/= A A_in ->] /mapP[/= B B_in ->].
  have : (r A) *m (r B) = (r B) *m (r A).
    rewrite /r !mulmxA !mulmxKtV // ?schmidt_complete_unitary //;
    rewrite ?add_rank_ortho // -![S *m _ *m _]mulmxA.
    by rewrite As_comm.
  rewrite -[r A in X in X -> _]submxK -[r B  in X in X -> _]submxK.
  rewrite 2!mulmx_block => /eq_block_mx [_ _ _].
  suff urr_eq0 X : X \in As -> ursubmx (r X) = 0.
    by rewrite !urr_eq0 ?mulmx0 ?add0r.
  rewrite /r /S ![schmidt_complete _ *m _]mul_col_mx.
  rewrite !tr_col_mx !map_row_mx !mul_col_row !block_mxKur.
  by move=> X_in; rewrite vSvo // vP.
move=> P' P'_unitary /allP /= P'P.
exists ((block_mx 1%:M 0 0 P') *m S).
  rewrite mul_unitary ?schmidt_complete_unitary //.
  apply/unitaryP; rewrite tr_block_mx map_block_mx mulmx_block.
  rewrite !trmx0 !map_mx0 !tr_scalar_mx !map_scalar_mx ?conjC1.
  rewrite !(mulmx1, mul1mx, mulmx0, mul0mx, addr0, add0r).
  by rewrite (unitaryP _) -?scalar_mx_block //.
apply/allP => /= A A_in.
rewrite trmx_mul map_mxM tr_block_mx map_block_mx.
rewrite !trmx0 !map_mx0 !tr_scalar_mx !map_scalar_mx ?conjC1.
rewrite mulmxA -[_ *m S *m _]mulmxA -[_ *m _ *m S^t*]mulmxA.
rewrite /S ![schmidt_complete _ *m _]mul_col_mx.
rewrite !tr_col_mx !map_row_mx !mul_col_row !mulmx_block.
rewrite !(mulmx1, mul1mx, mulmx0, mul0mx, addr0, add0r).
apply/triangularP => /= i j lt_ij; rewrite mxE.
case: splitP => //= i' i_eq; rewrite !mxE;
case: splitP => //= j' j_eq.
- have /vP /eigenvectorP [a v_in] := A_in.
  by rewrite (vSv _ _ v_in) mxE -val_eqE ltn_eqF //= -i_eq -j_eq.
- by rewrite vSvo ?mul0mx ?mxE // vP //.
- move: lt_ij; rewrite i_eq j_eq ltnNge -ltnS (leq_trans (ltn_ord j')) //.
  by rewrite -addnS leq_addr.
- set A' := _ *m A *m _; rewrite -inv_unitary //.
  have -> // := (triangularP (P'P A' _)); last first.
    by move: lt_ij; rewrite i_eq j_eq ltn_add2l.
  by apply/mapP; exists A; rewrite //= drrE.
Qed.

Theorem Schur n (A : 'M[C]_n) : (n > 0)%N ->
  exists2 P : 'M[C]_n, P \is unitary &
    [forall i : 'I_n, forall j : 'I_n, (i < j)%N ==>
      ((P *m A *m invmx P) i j == 0)].
Proof.
case: n => [//|n] in A * => _; have [] := @cotrigonalization _ [:: A].
  by move=> ? ? /=; rewrite !in_cons !orbF => /eqP-> /eqP->.
by move=> P P_unitary /=; rewrite andbT=> A_trigo; exists P.
Qed.

Lemma cotrigonalization2 n (A B : 'M[C]_n) : A *m B = B *m A ->
  exists2 P : 'M[C]_n, P \is unitary &
    triangular (P *m A *m invmx P) && triangular (P *m B *m invmx P).
Proof.
move=> AB_comm; have [] := @cotrigonalization _ [:: A; B].
  by move=> ??; rewrite !inE => /orP[]/eqP->/orP[]/eqP->.
move=> P Punitary /allP /= PP; exists P => //.
by rewrite !PP ?(mem_head, in_cons, orbT).
Qed.

Theorem normal_spectral_subproof {n} {A : 'M[C]_n} : reflect
  (exists2 sp : 'M_n * 'rV_n, sp.1 \is unitary &
                              A = invmx sp.1 *m diag_mx sp.2 *m sp.1)
  (A \is normalmx).
Proof.
apply: (iffP normalmxP); last first.
  move=> [[/= P D] P_unitary ->].
  rewrite !trmx_mul !map_mxM !mulmxA inv_unitary //.
  rewrite !trmxCK ![_ *m P *m _]mulmxtVK //.
  by rewrite -[X in X *m P]mulmxA tr_diag_mx map_diag_mx diag_mxC mulmxA.
move=> /cotrigonalization2 [P Punitary /andP[]].
set D := _ *m A *m _ => Dtriangular Dtc_triangular.
exists (P, \row_i D i i) => //=.
have Punit : P \in unitmx by rewrite unitary_unit.
apply: (@row_full_inj _ _ _ _ P); rewrite ?row_full_unit //.
apply: (@row_free_inj _ _ _ _ (invmx P)); rewrite ?row_free_unit ?unitmx_inv //.
rewrite !mulmxA mulmxV // mul1mx mulmxK //.
apply/matrixP=> i j; rewrite [D]lock ![in RHS]mxE -lock -val_eqE.
have [lt_ij|lt_ji|/val_inj<-//] := ltngtP; rewrite mulr0n.
  by rewrite (triangularP _).
suff : D^t* j i = 0 by rewrite !mxE => /eqP; rewrite conjC_eq0 => /eqP.
rewrite !trmx_mul !map_mxM inv_unitary // trmxCK -(@inv_unitary  _ P) //.
by rewrite mulmxA (triangularP _).
Qed.

Definition spectralmx n (A : 'M[C]_n) : 'M[C]_n :=
  if @normal_spectral_subproof _ A is ReflectT P
  then (projT1 (sig2_eqW P)).1 else 1%:M.

Definition spectral_diag n (A : 'M[C]_n) : 'rV_n :=
  if @normal_spectral_subproof _ A is ReflectT P
  then (projT1 (sig2_eqW P)).2 else 0.

Lemma spectral_unitary n (A : 'M[C]_n) : spectralmx A \is unitary.
Proof.
rewrite /spectralmx; case: normal_spectral_subproof; last first.
  by move=> _; apply/unitaryP; rewrite trmx1 map_mx1 mulmx1.
by move=> ?; case: sig2_eqW.
Qed.

Lemma spectral_unit  n (A : 'M[C]_n) : spectralmx A \in unitmx.
Proof. exact/unitary_unit/spectral_unitary. Qed.

Theorem normal_spectralP {n} {A : 'M[C]_n}
  (P := spectralmx A) (sp := spectral_diag A) :
  reflect (A = invmx P *m diag_mx sp *m P) (A \is normalmx).
Proof.
rewrite /P /sp /spectralmx /spectral_diag.
case: normal_spectral_subproof.
  by move=> Psp; case: sig2_eqW => //=; constructor.
move=> /normal_spectral_subproof Ann; constructor; apply/eqP.
apply: contra Ann; rewrite invmx1 mul1mx mulmx1 => /eqP->.
suff -> : diag_mx 0 = 0 by rewrite qualifE trmx0 map_mx0.
by move=> ??; apply/matrixP=> i j; rewrite !mxE mul0rn.
Qed.

Section mxOver.
Context {m n : nat}.

Definition mxOver (S : pred_class) :=
  [qualify a M : 'M[C]_(m, n) | [forall i, [forall j, M i j \in S]]].

Fact mxOver_key S : pred_key (mxOver S). Proof. by []. Qed.
Canonical mxOver_keyed S := KeyedQualifier (mxOver_key S).

Lemma mxOverP {S : pred_class} {M : 'M[C]__} :
  reflect (forall i j, M i j \in S) (M \is a mxOver S).
Proof. exact/'forall_forallP. Qed.

Lemma mxOverS (S1 S2 : pred_class) :
  {subset S1 <= S2} -> {subset mxOver S1 <= mxOver S2}.
Proof. by move=> sS12 M /mxOverP S1M; apply/mxOverP=> i j; apply/sS12/S1M. Qed.

Lemma mxOver0 S : 0 \in S -> 0 \is a mxOver S.
Proof. by move=> S0; apply/mxOverP=>??; rewrite mxE. Qed.

Section mxOverAdd.

Variables (S : predPredType C) (addS : addrPred S) (kS : keyed_pred addS).

Lemma mxOver_constmx c : (m > 0)%N -> (n > 0)%N ->
  (const_mx c \is a mxOver kS) = (c \in kS).
Proof.
move=> m_gt0 n_gt0; apply/mxOverP/idP; last first.
   by move=> cij i j; rewrite mxE.
by move=> /(_ (Ordinal m_gt0) (Ordinal n_gt0)); rewrite mxE.
Qed.

Fact mxOver_addr_closed : addr_closed (mxOver kS).
Proof.
split=> [|p q Sp Sq]; first by rewrite mxOver0 // ?rpred0.
by apply/mxOverP=> i j; rewrite mxE rpredD // !(mxOverP _).
Qed.
Canonical mxOver_addrPred := AddrPred mxOver_addr_closed.

End mxOverAdd.

Fact mxOverNr S (addS : zmodPred S) (kS : keyed_pred addS) :
  oppr_closed (mxOver kS).
Proof. by move=> M /mxOverP SM; apply/mxOverP=> i j; rewrite mxE rpredN. Qed.
Canonical mxOver_opprPred S addS kS := OpprPred (@mxOverNr S addS kS).
Canonical mxOver_zmodPred S addS kS := ZmodPred (@mxOverNr S addS kS).

End mxOver.

Section mxOverRing.

Variables (S : predPredType C) (ringS : subringPred S) (kS : keyed_pred ringS).

Lemma mxOverMmx m n p :
  {in mxOver kS & mxOver kS,
      forall u : 'M[C]_(m, n), forall v : 'M[C]_(n, p),
        u *m v \is a mxOver kS}.
Proof.
move=> M N /mxOverP MS /mxOverP NS; apply/mxOverP=> i j.
by rewrite !mxE rpred_sum // => k _; rewrite rpredM.
Qed.

End mxOverRing.

Lemma mxOver_scalarmx n (S : predPredType C) c :
  (n > 0)%N -> 0 \in S -> (c%:M \is a @mxOver n n S) = (c \in S).
Proof.
move=> n_gt0 S0; apply/mxOverP/idP; last first.
   by move=> cij i j; rewrite mxE; case: eqP => // _; rewrite mulr0n.
by move=> /(_ (Ordinal n_gt0) (Ordinal n_gt0)); rewrite mxE eqxx.
Qed.

Lemma hermitian_normalmx n (A : 'M[C]_n) : A \is hermitian -> A \is normalmx.
Proof.
move=> Ahermi; apply/normalmxP.
by rewrite {1 4}[A](sesquiP false conjC _ _) // !linearZ /= -!scalemxAl.
Qed.

Lemma real_similar n (A B P : 'M[C]_n) : P \in unitmx ->
  invmx P *m A *m P = B ->
  A \is a mxOver Num.real -> B \is a mxOver Num.real ->
  let Q a := P ^ (@Re _) + a *: P ^ (@Im _) in
  exists2 a, (a \is Num.real) && (Q a \in unitmx) &
  invmx (Q a) *m A *m Q a = B.
Proof.
move=> Punit /(congr1 (mulmx P)); rewrite !mulmxA mulmxV ?mul1mx //.
set Pr := P ^ (@Re _); set Pi := P ^ (@Im _); move: Punit.
have -> : P = Pr + 'i *: Pi by apply/matrixP=> i j; rewrite !mxE -Crect.
have Pr_real : Pr \is a mxOver Num.real.
  by apply/mxOverP=> i j; rewrite !mxE Creal_Re.
have Pi_real : Pi \is a mxOver Num.real.
  by apply/mxOverP=> i j; rewrite !mxE Creal_Im.
move: Pr Pi Pr_real Pi_real => Pr Pi Pr_real Pi_real Punit eq_AP_PB Areal Breal.
pose p := \det (Pr ^ polyC + 'X *: Pi ^ polyC).
have p_neq0 : p != 0.
  move: Punit; rewrite unitmxE unitfE /p; apply: contraNneq.
  move=> /(congr1 (horner^~ 'i)); rewrite -/(horner_eval _ _) -det_map_mx.
  rewrite map_mxD map_mxZ -!map_mx_comp !(eq_map_mx _ (fun=> hornerC _ _)).
  by rewrite !map_mx_id /= /horner_eval hornerX horner0 => ->.
have rs_uniq : uniq [seq (i%:R : C) | i <- iota 0 (size p)].
  by rewrite map_inj_uniq ?iota_uniq //; apply: mulrIn; rewrite oner_eq0.
have := contraNN (fun x => max_poly_roots p_neq0 x rs_uniq).
rewrite size_map size_iota ltnn => /(_ isT) /allPn[a a_in rootNpa].
have a_real : a \is Num.real by move: a_in => /mapP [i _ ->]; rewrite realn.
move=> [: Pa_unit]; exists a.
   rewrite a_real /=; abstract: Pa_unit.
   move: rootNpa; rewrite unitmxE unitfE /root /p -/(horner_eval _ _).
   rewrite -det_map_mx map_mxD map_mxZ -!map_mx_comp.
   rewrite !(eq_map_mx _ (fun=> hornerC _ _)).
   by rewrite !map_mx_id /= /horner_eval hornerX.
apply: (can_inj (mulKmx Pa_unit)); rewrite !mulmxA mulmxV // mul1mx.
rewrite !mulmxDl !mulmxDr -!scalemxAr -!scalemxAl in eq_AP_PB *.
have /(congr1 (fun X => X ^ (@Im _))) := eq_AP_PB.
have /(congr1 (fun X => X ^ (@Re _))) := eq_AP_PB.
have Remx_rect : {in mxOver Num.real &, forall X Y,
                      (X + 'i *: Y) ^ (@Re _) = X}.
  move=> /= r s X Y Xreal Yreal; apply/matrixP=> i j; rewrite !mxE.
  by rewrite Re_rect // (mxOverP _ _).
have Immx_rect : {in mxOver Num.real &, forall X Y,
                      (X + 'i *: Y) ^ (@Im _) = Y}.
  move=> /= r s X Y Xreal Yreal; apply/matrixP=> i j; rewrite !mxE.
  by rewrite Im_rect // (mxOverP _ _).
by rewrite !(Remx_rect, Immx_rect) ?mxOverMmx //= => -> ->.
Qed.

Lemma hermitian_spectral n (A : 'M[C]_n) : A \is hermitian ->
  spectral_diag A \is a mxOver Num.real.
Proof.
move=> Ahermi; have /hermitian_normalmx /normal_spectralP A_eq := Ahermi.
have /(congr1 (fun X => X^t*)) := A_eq.
rewrite inv_unitary ?spectral_unitary //.
rewrite !trmx_mul !map_mxM map_trmx trmxK -map_mx_comp.
rewrite tr_diag_mx map_diag_mx (eq_map_mx _ (@conjCK _)) map_mx_id.
rewrite -[in RHS]inv_unitary ?spectral_unitary //.
have := sesquiP _ _ _ Ahermi; rewrite expr0 scale1r => <-; rewrite {1}A_eq.
rewrite mulmxA; move=> /(congr1 (mulmx^~ (invmx (spectralmx A)))).
rewrite !mulmxK ?spectral_unit //.
move=> /(congr1 (mulmx (spectralmx A))); rewrite !mulKVmx ?spectral_unit //.
move=> eq_A_conjA; apply/mxOverP => i j; rewrite ord1 {i}.
have /matrixP /(_ j j) := eq_A_conjA; rewrite !mxE eqxx !mulr1n.
by move=> /esym /CrealP.
Qed.

End Spectral.
