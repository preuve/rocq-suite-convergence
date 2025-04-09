Require Nat.
Require Import Rbase Lra Lia.
Import Rfunctions.         (* Rabs *)
Require Import Rseries.    (* Un_cv *)
Open Scope R_scope.

(** Une suite réelle n'est rien d'autre qu'une fonction de nat vers R.
    La définition de la convergence d'une suite vers une limite l (finie)
    par Weierstrass a fait entrer l'analyse dans son ère moderne.
    Dans cette bibliothèque, cette propriété se note Un_cv.
*)

Print Un_cv.

(** Voici une définition possible de "suite bornée" : *)
Definition bounded (Un : nat -> R) :=
  exists m, forall n, Rabs (Un n) <= m.

Fixpoint running_max (Un : nat -> R) (n : nat) :=
  match n with
    0%nat => (Un 0%nat)
  | S n => Rmax (running_max Un n) (Un (S n))
  end.

Lemma bound_aux_r x y z : x <= y -> x <= Rmax y z.
Proof. intros. 
  destruct (Rtotal_order y z).
  rewrite <- Rmax_l. exact H.
  destruct H0.
  rewrite <- H0. rewrite <- Rmax_r. exact H.
  rewrite <- Rmax_l. exact H.
Qed.

Lemma bound_aux_l x y z : x <= z -> x <= Rmax y z.
Proof. intros. 
  destruct (Rtotal_order y z).
  rewrite <- Rmax_r. exact H.
  destruct H0.
  rewrite H0. rewrite <- Rmax_l. exact H.
  rewrite <- Rmax_r. exact H.
Qed.

Lemma Un_le_running_max (Un : nat -> R) (n : nat) :
  forall i, (i <= n)%nat -> Un i <= (running_max Un n).
Proof.
  induction n.
  + intros.
    apply Nat.le_0_r in H.
    rewrite H.
    simpl.
    apply Rle_refl.
  + intros.
    specialize (IHn i).
    assert (le_succ_dec : forall a b (H : (a <= S b)%nat),
      (a <= b)%nat \/ (a = S b)%nat) by lia.
    apply le_succ_dec in H.
    destruct H.
    - apply IHn in H as H1.
      simpl.
      apply bound_aux_r. exact (IHn H).
    - rewrite H.
      simpl.
      apply bound_aux_l. reflexivity.
Qed.

Lemma Rle_opp_contravar x y : x <= y -> -y <= -x.
Proof.
  intros.
  apply (Rplus_le_compat_r (-x + -y)) in H.
  rewrite <- Rplus_assoc, Rplus_opp_r, Rplus_0_l, Rplus_comm
    , Rplus_assoc, Rplus_opp_l, Rplus_0_r in H. exact H.
Qed.


Lemma absolutize a b c : a <= b -> b <= c -> Rabs b <= Rmax (Rabs a) (Rabs c).
Proof.
  intros.
  unfold Rabs.
  destruct (Rcase_abs a).
  destruct (Rcase_abs c).
  destruct (Rcase_abs b).
  apply bound_aux_r.
  apply Rle_opp_contravar. exact H.
  exfalso. lra.
  destruct (Rcase_abs b).
  apply bound_aux_r.
  apply Rle_opp_contravar. exact H.
  apply bound_aux_l. exact H0.
  destruct (Rcase_abs c).
  destruct (Rcase_abs b).
  exfalso. lra.
  exfalso. lra.
  destruct (Rcase_abs b).
  exfalso. lra.
  apply bound_aux_l. exact H0.
Qed.


(** Le suites convergentes sont bornées. *)
Theorem CV_impl_bounded (Un : nat -> R) (l : R) :
  Un_cv Un l -> bounded Un.
Proof.
  unfold Un_cv.
  unfold Rdist.
  unfold bounded.
  intro Hconv.
  (* On pose ε = 1 *)
  specialize (Hconv 1 Rlt_0_1).
  destruct Hconv as [N HN].

  (* On s'intéresse aux u_n pour n >= N *)
  set (M1 := Rabs l + 1).

  (* On prend le max des |u_0| à |u_(N-1)| *)
  set (max_init := running_max Un (N-1)).
  set (min_init := running_max (fun n => - Un n) (N - 1)).
  set (m_init := Rmax (Rabs min_init) (Rabs max_init)).
  set (M := Rmax M1 m_init).
  exists M.
  intros n.

  destruct (le_lt_dec N n) as [Hge | Hlt].
  - 
    
    specialize (HN n Hge).
    replace (Un n) with ((Un n - l) + l) by lra.
    apply Rle_trans with (Rabs (Un n - l) + Rabs l). apply Rabs_triang.
    unfold M. unfold M1.
    assert (Rabs l + 1 <= Rmax (Rabs l + 1) m_init).
    apply bound_aux_r, Rle_refl.
    assert (Rabs (Un n - l) + (Rabs l + 1) 
      < 1 + Rmax (Rabs l + 1) m_init).
    apply (Rplus_lt_le_compat _ _ _ _ HN H).
    apply Rlt_le in H0.
    lra.
  - (* Cas n < N : borné car max_init et -min_init bornent tous ces termes *)
    assert (lt_le_excl : forall x y, (x < y)%nat -> (x <= y - 1)%nat) by lia.
    
    assert ( Un n <= max_init).
    { apply lt_le_excl in Hlt.
      apply (Un_le_running_max Un (N-1) n Hlt).
    }
  assert (- Un n <= min_init).
  { apply lt_le_excl in Hlt.
    apply (Un_le_running_max  (fun n => - Un n) (N-1) n Hlt).
  }
  apply Rle_opp_contravar in H0.
  rewrite Ropp_involutive in H0.

  assert( Rabs (Un n) <= m_init).
  { unfold m_init.
    replace (Rabs min_init) with (Rabs (-min_init)).
    apply (absolutize _ _ _ H0 H).
    rewrite Rabs_Ropp. reflexivity.
  }
  apply (bound_aux_l _ M1 _ ) in H1.
  unfold M. exact H1.
Qed.

