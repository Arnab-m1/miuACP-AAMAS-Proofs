(* muACP.v - start *)

From Coq Require Import ZArith List Bool Lia.
Import ListNotations.
Open Scope Z_scope.
(* Needed for NoDup, incl *)
Local Notation In := List.In.

(* --- Basic types --- *)
Definition agent := nat.

Inductive verb := VPing | VTell | VAsk | VObserve.

Record resources := mk_res {
  mem : Z;
  bw : Z;
  cpu : Z;
  energy : Z
}.

Definition res_nonneg (r: resources) : Prop :=
  mem r >= 0 /\ bw r >= 0 /\ cpu r >= 0 /\ energy r >= 0.

(* Option and payload model *)
Record opt := mk_opt { opt_type : Z; opt_len : Z; opt_val : list Z }.
Definition payload := list Z.

Record message := mk_msg { hdr: Z; mv: verb; mopts: list opt; mpl : payload }.

Record agent_state := mk_ast { kb: list Z; hist: list message; acc: option (Z * Z); res: resources }.

Record system_state := mk_sys { state_of : agent -> agent_state; net : list message }.

(* Equality decisions for records/lists/messages (for List.remove) *)

Definition verb_eq_dec (x y: verb) : {x = y} + {x <> y}.
decide equality.
Defined.

Fixpoint list_eq_dec {A: Type} (eq_dec: forall x y: A, {x=y}+{x<>y})
         (l1 l2: list A) : {l1 = l2} + {l1 <> l2}.
Proof.
  revert l2.
  induction l1 as [|x xs IH]; intros [|y ys].
  - left; reflexivity.
  - right; discriminate.
  - right; discriminate.
  - destruct (eq_dec x y).
    + destruct (IH ys) as [Heq | Hneq].
      * left. subst. reflexivity.
      * right. intros H. inversion H. apply Hneq. assumption.
    + right. intros H. inversion H. apply n. assumption.
Defined.

Definition opt_eq_dec (x y: opt) : {x = y} + {x <> y}.
Proof.
  destruct x as [t1 l1 v1], y as [t2 l2 v2].
  destruct (Z.eq_dec t1 t2).
  - destruct (Z.eq_dec l1 l2).
    + destruct (list_eq_dec Z.eq_dec v1 v2).
      * left. now subst.
      * right. intros H; inversion H; contradiction.
    + right. intros H; inversion H; contradiction.
  - right. intros H; inversion H; contradiction.
Defined.

Definition message_eq_dec (x y: message) : {x = y} + {x <> y}.
Proof.
  destruct x as [h1 v1 o1 p1], y as [h2 v2 o2 p2].
  destruct (Z.eq_dec h1 h2).
  - destruct (verb_eq_dec v1 v2).
    + destruct (list_eq_dec opt_eq_dec o1 o2).
      * destruct (list_eq_dec Z.eq_dec p1 p2).
        { left. now subst. }
        { right. intros H; inversion H; contradiction. }
      * right. intros H; inversion H; contradiction.
    + right. intros H; inversion H; contradiction.
  - right. intros H; inversion H; contradiction.
Defined.

(* Resource consumption function *)
(* rho_nonneg is axiomatized: rho abstracts resource costs. If rho becomes
   concrete, replace the axiom with a lemma proof. *)
Parameter rho : agent -> verb -> list opt -> payload -> resources.

Axiom rho_nonneg : forall a v o p,
  res_nonneg (rho a v o p).

(* Helper accessors *)
Definition res_of (a: agent) (s: system_state) : resources := res (state_of s a).
Definition acc_of (a: agent) (s: system_state) : option (Z * Z) := acc (state_of s a).

(* --- Resource arithmetic helpers --- *)
Definition res_ge (r1 r2: resources) : Prop :=
  mem r1 >= mem r2 /\ bw r1 >= bw r2 /\ cpu r1 >= cpu r2 /\ energy r1 >= energy r2.

Definition res_sub (r d: resources) : resources :=
  mk_res (mem r - mem d)
         (bw r - bw d)
         (cpu r - cpu d)
         (energy r - energy d).

Lemma res_sub_nonneg:
  forall r d,
    res_nonneg r -> res_nonneg d -> res_ge r d -> res_nonneg (res_sub r d).
Proof.
  intros r d [Hrmem [Hrbw [Hrcpu Hreng]]] [Hdmem [Hdbw [Hdcpu Hdeng]]] [Gm [Gb [Gc Ge]]];
  unfold res_sub, res_nonneg in *; simpl in *; repeat split; lia.
Qed.

(* --- Transition relation --- *)
Inductive step : system_state -> system_state -> Prop :=
| StepSend :
    forall s a msg s',
      (* feasibility: sender has non-negative resources and sufficient mem to send on all fields *)
      res_nonneg (res_of a s) ->
      mem (res_of a s) >= mem (rho a (mv msg) (mopts msg) (mpl msg)) ->
      bw (res_of a s) >= bw (rho a (mv msg) (mopts msg) (mpl msg)) ->
      cpu (res_of a s) >= cpu (rho a (mv msg) (mopts msg) (mpl msg)) ->
      energy (res_of a s) >= energy (rho a (mv msg) (mopts msg) (mpl msg)) ->
      (* update: append msg to network; sender's resources decrease and history appends *)
      let st := state_of s a in
      let newst := mk_ast (kb st) (hist st ++ [msg]) (acc st) (res_sub (res st) (rho a (mv msg) (mopts msg) (mpl msg))) in
      s' = mk_sys (fun x => if Nat.eqb x a then newst else state_of s x) (msg :: net s) ->
      step s s'
| StepRecv :
    forall s a msg s' new_kb,
      In msg (net s) ->
      (* receiver has enough resources on all fields *)
      mem (res_of a s) >= mem (rho a (mv msg) (mopts msg) (mpl msg)) ->
      bw (res_of a s) >= bw (rho a (mv msg) (mopts msg) (mpl msg)) ->
      cpu (res_of a s) >= cpu (rho a (mv msg) (mopts msg) (mpl msg)) ->
      energy (res_of a s) >= energy (rho a (mv msg) (mopts msg) (mpl msg)) ->
      (* update receiver state: kb and resource subtracted *)
      let st := state_of s a in
      let newst := mk_ast (new_kb :: kb st) (hist st ++ [msg]) (acc st)
                          (res_sub (res st) (rho a (mv msg) (mopts msg) (mpl msg))) in
      s' = mk_sys (fun x => if Nat.eqb x a then newst else state_of s x)
                  (remove message_eq_dec msg (net s)) ->
      step s s'.

(* Multi-step / execution relation *)
Inductive multi_step : system_state -> system_state -> Prop :=
| ms_refl : forall s, multi_step s s
| ms_step : forall s s' s'',
    step s s' -> multi_step s' s'' -> multi_step s s''.

(* initial_ok, reachable, exec definition placeholders *)
Definition exec := multi_step.

(* Invariant lemmas *)
Theorem step_preserves_res_nonneg :
  forall s s',
    (forall a, res_nonneg (res_of a s)) ->
    step s s' ->
    (forall a, res_nonneg (res_of a s')).
Proof.
  intros s s' Hinv Hst.
  inversion Hst; subst; clear Hst.
  - (* StepSend *)
    intros a0. simpl. unfold res_of. simpl.
    destruct (Nat.eqb a0 a) eqn:Ha.
    + apply Nat.eqb_eq in Ha; subst a0.
      specialize (Hinv a). unfold res_of in Hinv. simpl in Hinv.
      assert (Hge: res_ge (res (state_of s a)) (rho a (mv msg) (mopts msg) (mpl msg))) by (repeat split; assumption).
      eapply res_sub_nonneg; eauto using rho_nonneg.
    + apply Hinv.
  - (* StepRecv *)
    intros a0. simpl.
    unfold res_of. simpl.
    destruct (Nat.eqb a0 a) eqn:Ha.
    + apply Nat.eqb_eq in Ha; subst a0.
      specialize (Hinv a). unfold res_of in Hinv. simpl in Hinv.
      assert (Hge: res_ge (res (state_of s a)) (rho a (mv msg) (mopts msg) (mpl msg))) by (repeat split; assumption).
      eapply res_sub_nonneg; eauto using rho_nonneg.
    + apply Hinv.
Qed.

Theorem multi_step_preserves_res_nonneg :
  forall s s',
    (forall a, res_nonneg (res_of a s)) ->
    multi_step s s' ->
    forall a, res_nonneg (res_of a s').
Proof.
  intros s s' Hinit Hms.
  induction Hms; auto.
  apply IHHms.
  eapply step_preserves_res_nonneg; eauto.
Qed.

Definition initial_ok (s: system_state) : Prop := forall a, res_nonneg (res_of a s).

Theorem resource_boundedness :
  forall (s0 s: system_state),
    initial_ok s0 -> exec s0 s -> forall a, res_nonneg (res_of a s).
Proof.
  intros s0 s Hinit Hexec.
  unfold exec in Hexec.
  eapply multi_step_preserves_res_nonneg; eauto.
Qed.

(* Tiny example to exercise StepSend and StepRecv under sufficient resource premises *)
Example tiny_exec_example:
  forall (st0: agent_state) (msg: message),
    (* initial system where every agent has the same state st0 *)
    let sys0 := mk_sys (fun _ => st0) [] in
    (* choose two agents a (sender) and b (receiver) *)
    let a := 0%nat in
    let b := 1%nat in
    (* assume sender and receiver have sufficient resources for msg *)
    res_nonneg (res_of a sys0) ->
    mem (res_of a sys0) >= mem (rho a (mv msg) (mopts msg) (mpl msg)) ->
    bw (res_of a sys0) >= bw (rho a (mv msg) (mopts msg) (mpl msg)) ->
    cpu (res_of a sys0) >= cpu (rho a (mv msg) (mopts msg) (mpl msg)) ->
    energy (res_of a sys0) >= energy (rho a (mv msg) (mopts msg) (mpl msg)) ->
    res_nonneg (res_of b sys0) ->
    mem (res_of b sys0) >= mem (rho b (mv msg) (mopts msg) (mpl msg)) ->
    bw (res_of b sys0) >= bw (rho b (mv msg) (mopts msg) (mpl msg)) ->
    cpu (res_of b sys0) >= cpu (rho b (mv msg) (mopts msg) (mpl msg)) ->
    energy (res_of b sys0) >= energy (rho b (mv msg) (mopts msg) (mpl msg)) ->
    exists s1 s2, step sys0 s1 /\ step s1 s2.
Proof.
  intros st0 msg sys0 a b Hna Hma Hba Hca Hea Hnb Hmb Hbb Hcb Heb.
  eexists _, _. split;
  [ eapply StepSend with (a:=a) (msg:=msg); eauto; reflexivity
  | eapply StepRecv with (a:=b) (msg:=msg) (new_kb:=0%Z); simpl; eauto; reflexivity ].
Qed.



(* ========================= *)
(* Paxos safety formalization *)
(* ========================= *)

(* Simple encodings for ballots and values *)
Definition ballot := Z.
Definition value := Z.

(* Accepted predicate from agent state *)
Definition accepted (st: system_state) (a: agent) (b: ballot) (v: value) : Prop :=
  acc_of a st = Some (b, v).

(* Finite universe of acceptors *)
Parameter Acceptors : list agent.
Hypothesis Acceptors_NoDup : NoDup Acceptors.

(* Number of acceptors; used to define majority *)
Definition n_acceptors : nat := length Acceptors.

(* Majority via doubling to avoid divisions *)
Definition majority (Q: list agent) : Prop := (2 * length Q > n_acceptors)%nat.

(* Chosen value: a value supported by a majority of acceptors *)
Definition chosen (st: system_state) (v: value) : Prop :=
  exists Q, majority Q /\ NoDup Q /\ incl Q Acceptors /\ forall a, In a Q -> exists b, accepted st a b v.

(* Quorum intersection assumption over lengths (abstracting from set universe) *)
Axiom quorum_intersect :
  forall (Q1 Q2: list agent),
    NoDup Acceptors ->
    NoDup Q1 -> NoDup Q2 ->
    incl Q1 Acceptors -> incl Q2 Acceptors ->
    majority Q1 -> majority Q2 ->
    exists a, In a Q1 /\ In a Q2.

(* Cross-reachable uniqueness: an acceptor cannot report two different values across reachable states. *)
Definition reachable (sys st: system_state) := multi_step sys st.

(* --- Acceptor uniqueness across reachable states --- *)
Lemma acc_preserved_step :
  forall s s' u, step s s' -> acc_of u s' = acc_of u s.
Proof.
  intros s s' u Hst. inversion Hst; subst; simpl; auto.
  all: unfold acc_of; simpl; destruct (Nat.eqb u a) eqn:Heq; [apply Nat.eqb_eq in Heq; subst u; reflexivity|reflexivity].
Qed.

Lemma acc_preserved_multi :
  forall s s' a, multi_step s s' -> acc_of a s' = acc_of a s.
Proof.
  intros s s' a Hms. induction Hms; simpl; auto.
  pose proof (acc_preserved_step s s' a H) as Hstep.
  rewrite <- Hstep. apply IHHms.
Qed.

Theorem acceptor_value_unique_across_reachable :
  forall sys st1 st2 a b1 v1 b2 v2,
    reachable sys st1 -> reachable sys st2 ->
    accepted st1 a b1 v1 -> accepted st2 a b2 v2 -> v1 = v2.
Proof.
  intros sys st1 st2 a b1 v1 b2 v2 Hr1 Hr2 H1 H2.
  unfold accepted, reachable in *.
  pose proof (acc_preserved_multi _ _ a Hr1) as Hpr1.
  pose proof (acc_preserved_multi _ _ a Hr2) as Hpr2.
  rewrite Hpr1 in H1. rewrite Hpr2 in H2.
  congruence.
Qed.

(* Main Paxos-style safety theorem *)
Theorem paxos_safety_muACP :
  forall sys st1 st2 v1 v2,
    reachable sys st1 ->
    reachable sys st2 ->
    chosen st1 v1 ->
    chosen st2 v2 ->
    v1 = v2.
Proof.
  intros sys st1 st2 v1 v2 Hr1 Hr2 [Q1 [Hmaj1 [Hnd1 [Hinc1 Hq1]]]] [Q2 [Hmaj2 [Hnd2 [Hinc2 Hq2]]]].
  destruct (quorum_intersect Q1 Q2 Acceptors_NoDup Hnd1 Hnd2 Hinc1 Hinc2 Hmaj1 Hmaj2) as [a [Ha1 Ha2]].
  destruct (Hq1 a Ha1) as [b1 Hacc1].
  destruct (Hq2 a Ha2) as [b2 Hacc2].
  apply (acceptor_value_unique_across_reachable sys st1 st2 a b1 v1 b2 v2); assumption.
Qed.

