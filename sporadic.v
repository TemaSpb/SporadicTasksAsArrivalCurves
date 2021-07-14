Require Export prosa.model.task.arrival.sporadic.
Require Export prosa.model.task.arrival.curves.
Require Export prosa.model.task.arrival.periodic.

From Coq Require Import Basics Setoid Morphisms.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat.

(** This construction allows us to "rewrite" inequalities with ≤. *)

Inductive leb a b := Leb of (a ==> b).

Lemma leb_eq a b : leb a b <-> (a -> b).
Proof. move: a b => [|] [|]; firstorder. Qed.

Instance : PreOrder leb.
Proof. split => [[|]|[|][|][|][?][?]]; try exact: Leb. Qed.

Instance : Proper (leb ==> leb ==> leb) andb.
Proof. move => [|] [|] [A] c d [B]; exact: Leb. Qed.

Instance : Proper (leb ==> leb ==> leb) orb.
Proof. move => [|] [|] [A] [|] d [B]; exact: Leb. Qed.

Instance : Proper (leb ==> impl) is_true.
Proof. move => a b []. exact: implyP. Qed.

Instance : Proper (le --> le ++> leb) leq.
Proof. move => n m /leP ? n' m' /leP ?. apply/leb_eq => ?. eauto using leq_trans. Qed.

Instance : Proper (le ==> le ==> le) addn.
Proof. move => n m /leP ? n' m' /leP ?. apply/leP. exact: leq_add. Qed.

Instance : Proper (le ++> le --> le) subn.
Proof. move => n m /leP ? n' m' /leP ?. apply/leP. exact: leq_sub. Qed.

Instance : Proper (le ==> le) S.
Proof. move => n m /leP ?. apply/leP. by rewrite ltnS. Qed.

Instance : RewriteRelation le.
Defined.

Definition leqRW {m n} : m <= n -> le m n := leP.
 
Section SporadicTasksAsArrivalCurves.
 
Context {Task : TaskType} `{SporadicModel Task}.
  
Context {Job : JobType} `{JobTask Job Task} `{JobArrival Job}.
  
Variable arr_seq : arrival_sequence Job.
Hypothesis H_consistent_arrivals: consistent_arrival_times arr_seq.
Hypothesis H_uniq_arr_seq: arrival_sequence_uniq arr_seq.
  
Definition max_arrivals_for_min_inter_arrival_time (tsk: Task) (Δ: duration) :=
  div_ceil Δ (task_min_inter_arrival_time tsk).

Global Instance sporadic_as_arrival : MaxArrivals Task :=
  {
    max_arrivals := max_arrivals_for_min_inter_arrival_time
  }.

  (* TODO: add this to [util.div_mod]*)
  Lemma div_ceil0:
    forall b, div_ceil 0 b = 0.
  Proof.
    intros b; unfold div_ceil.
    rewrite div.dvdn0.
    apply div.div0n.
  Qed.

   Lemma leq_div_ceil2r:
    forall (d : nat) (m n : nat),
      m <= n -> div_ceil m d <= div_ceil n d.
  Proof.
    move => d m n LEQ.
    rewrite /div_ceil.
    have LEQd: m %/ d <= n %/ d by apply leq_div2r.
    destruct (d %| m) eqn:Mm; destruct (d %| n) eqn:Mn => //; first by ssrlia.
    rewrite ltn_divRL //.
    apply ltn_leq_trans with m => //.
    move: (leq_trunc_div m d) => LEQm.
    destruct (ltngtP (m %/ d * d) m) => //.
    move: e => /eqP EQ; rewrite -dvdn_eq in EQ.
    by rewrite EQ in Mm.
  Qed.

  Remark valid_period_is_valid_inter_arrival_time:
    forall tsk, valid_task_min_inter_arrival_time tsk -> valid_arrival_curve (max_arrivals tsk).
  Proof.
    intros tsk VALID_TIME.
    split.
    { rewrite /max_arrivals /sporadic_as_arrival /max_arrivals_for_min_inter_arrival_time.
      by rewrite div_ceil0.
    }
    {
      unfold monotone.
      rewrite /max_arrivals /sporadic_as_arrival /max_arrivals_for_min_inter_arrival_time.
      intros x y LEQ.
      by rewrite leq_div_ceil2r.
    }
  Qed.

  Definition time_before_job_and_prev (j: Job) :=
    job_arrival j - job_arrival (prev_job arr_seq j).

  Definition job_has_prev (j: Job) :=
    j != prev_job arr_seq j.

  Definition specifc_task_and_has_prev (tsk: Task) (j: Job) :=
    (job_task j == tsk) && (job_has_prev j).


  Remark periodic_task_respects_sporadic_task_model:
    forall tsk, valid_task_min_inter_arrival_time tsk ->
           respects_sporadic_task_model arr_seq tsk ->
           respects_max_arrivals arr_seq tsk (max_arrivals tsk).
  Proof.
    intros tsk VALID_TIME RESPECTS_SPORADIC x y z.
    rewrite /max_arrivals /sporadic_as_arrival /max_arrivals_for_min_inter_arrival_time.
    move: VALID_TIME.
    unfold valid_task_min_inter_arrival_time.
    move:  RESPECTS_SPORADIC.
    unfold respects_sporadic_task_model.
    move: (task_min_inter_arrival_time tsk) => c.
    intros  RESPECTS_SPORADIC VALID_TIME.
    move: (arrivals_between arr_seq x y) => A.

    have EX: exists k, y = x + k.
    { exists (y - x). ssrlia. }
    move: EX => [k EQ]; subst y; clear z.
    replace (x + k - x) with k; last by ssrlia.
 
    have EX: exists l, k <= l.
    { exists k; by done. }
    move: EX => [l LE]. move: k LE.
    induction l; intros k LE.

    { move: LE; rewrite leqn0 => /eqP EQ0; subst k.
      rewrite addn0 div_ceil0.
      unfold number_of_task_arrivals, task_arrivals_between, arrivals_between.
      rewrite big_geq; by ssrlia. }
    { destruct (leqP c k) as [LE2 | LT]; first last.
      { clear IHl LE.
        destruct (posnP k) as [Z|POS].
        { subst k.
          unfold number_of_task_arrivals, task_arrivals_between, arrivals_between.
          rewrite big_geq; by ssrlia. }
        { (* Hard, probably. *)
          (* At most one job can arrive in an interval of length [c]. *)
          (* if [0 < k < c], then [div_ceil k c = 1] and 
             [number_of_task_arrivals arr_seq tsk x (x + k) <= 1]. *)
          unfold div_ceil.
          have FALSE_dvdn: c %| k = false.
          { unfold dvdn. rewrite modn_small; last by exact.
            rewrite eqn0Ngt.
            apply negbF; by exact. }
          rewrite FALSE_dvdn divn_small; last by exact.
          have CONTR: number_of_task_arrivals arr_seq tsk x (x + k) > 1 -> false.
          { unfold respects_sporadic_task_model in RESPECTS_SPORADIC.
            intros.
            apply exists_two in H2; first last.
            { apply filter_uniq.
              apply arrivals_uniq; by auto. }
            move: H2 => [a [b [ABNOQ [A_IN_TAB B_IN_TAB]]]].
            specialize (RESPECTS_SPORADIC a b).
            unfold task_arrivals_between in A_IN_TAB.
            have rr: forall j n m, (j \in task_arrivals_between arr_seq tsk n m) -> (j \in arrivals_between arr_seq n m).
            { admit.}
            apply rr in A_IN_TAB.
            apply rr in B_IN_TAB.
            
            feed_n 6  RESPECTS_SPORADIC => //; try by auto.
            - by apply in_arrivals_implies_arrived in A_IN_TAB.
            - by apply in_arrivals_implies_arrived in B_IN_TAB.
            - admit.
            - admit.
            - admit.
              
            apply in_arrivals_implies_arrived_between in A_IN_TAB; last by auto.
            apply in_arrivals_implies_arrived_between in B_IN_TAB; last by auto.
            unfold  arrived_between in A_IN_TAB.
            unfold  arrived_between in B_IN_TAB.
            admit. (* c? *)
          }
          apply contra_not_leq in CONTR; by auto.
        }
      }
      { specialize (IHl (k - c)).
        feed IHl; first by ssrlia.

        rewrite (num_arrivals_of_task_cat _ _ (x + (k - c))); last by ssrlia.

        rewrite (leqRW IHl).

        have LE3: number_of_task_arrivals arr_seq tsk (x + (k - c)) (x + k) <= 1.
        { (* Hard, probably. *)
          (* At most one job can arrive in an interval of length [c]. *)
          admit.
        }

        rewrite (leqRW LE3) addn1.
        unfold div_ceil.
        destruct (c %| k - c) eqn:EQ.
        { destruct (c %| k) eqn:EQ1.
          { rewrite divnBr; last by auto. { 
             rewrite ltn_psubCl. {
              {
                admit.
                (**rewrite divnn.
                move: (k %/ c) => L.
                simpl. **)
              }
            
             }
             {rewrite divn_gt0; by auto.
            }
            admit.}}
          auto.
          }
        (* Shouldn't be too hard. *)
        admit.
        
        
      }
    } 
  Admitted.


End SporadicTasksAsArrivalCurves.
