Require Export prosa.model.task.arrival.sporadic.
Require Export prosa.model.task.arrival.curves.
Require Export prosa.model.task.arrival.periodic.
Require Export prosa.util.setoid.
 
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
      by rewrite div_ceil0. }
    { unfold monotone.
      rewrite /max_arrivals /sporadic_as_arrival /max_arrivals_for_min_inter_arrival_time.
      intros x y LEQ.
      by rewrite leq_div_ceil2r. }
  Qed.

  
  Lemma max_one_job_can_arrive_in_one_sporadic_min_inter_arrival_time:
    forall tsk x y k, k - y <= task_min_inter_arrival_time tsk ->
                      respects_sporadic_task_model arr_seq tsk ->
                      number_of_task_arrivals arr_seq tsk (x + y) (x + k) <= 1.
  Proof.
    intros tsk x y k l_yk RESPECTS_SPORADIC.
    rewrite leqNgt; apply /negP; intros CONTR.
    apply exists_two in CONTR; last by apply filter_uniq, arrivals_uniq.
    move: CONTR => [j1 [j2 [J1J2NOQ [J1_IN_TAB J2_IN_TAB]]]].
    have tab_implies_ab: forall j t1 t2,
        (j \in task_arrivals_between arr_seq tsk t1 t2) ->
        (j \in arrivals_between arr_seq t1 t2)
        by intros; rewrite mem_filter in H2; move: H2 => /andP [/eqP].
    apply tab_implies_ab in J1_IN_TAB as J1_IN_AB.
    apply tab_implies_ab in J2_IN_TAB as J2_IN_AB.
    destruct (leqP (job_arrival j1) (job_arrival j2)).
    { specialize (RESPECTS_SPORADIC j1 j2).
      feed_n 6 RESPECTS_SPORADIC => //; try by auto.
      { by apply in_arrivals_implies_arrived in J1_IN_AB. }
      { by apply in_arrivals_implies_arrived in J2_IN_AB. }
      { by rewrite mem_filter in J1_IN_TAB; move: J1_IN_TAB => /andP [/eqP]. }
      { by rewrite mem_filter in J2_IN_TAB; move: J2_IN_TAB => /andP [/eqP]. }
      apply in_arrivals_implies_arrived_between in J1_IN_AB, J2_IN_AB; try by auto.
      unfold  arrived_between in J1_IN_AB, J2_IN_AB.
      by have _ : job_arrival j2 < x + y; ssrlia.
    }
    { specialize (RESPECTS_SPORADIC j2 j1).
      feed_n 6 RESPECTS_SPORADIC => //; try by auto.
      { by apply in_arrivals_implies_arrived in J2_IN_AB. }
      { by apply in_arrivals_implies_arrived in J1_IN_AB. }
      { by rewrite mem_filter in J2_IN_TAB; move: J2_IN_TAB => /andP [/eqP]. }
      { by rewrite mem_filter in J1_IN_TAB; move: J1_IN_TAB => /andP [/eqP]. }
      apply in_arrivals_implies_arrived_between in J1_IN_AB, J2_IN_AB; try by auto.
      by unfold arrived_between in J1_IN_AB, J2_IN_AB; ssrlia.
    }
  Qed.
  
  Lemma div_ceil_gt0:
    forall a b,
      a > 0 -> b > 0 ->
      div_ceil a b > 0.
  Proof.
    intros a b POSa POSb.
    unfold div_ceil.
    destruct (b %| a) eqn:EQ; last by done.
    by rewrite divn_gt0 //; apply dvdn_leq.
  Qed.


  Lemma leq_div_ceil_add1:
    forall Δ T,
      T > 0 -> T <= Δ ->
      div_ceil (Δ - T) T + 1 <= div_ceil Δ T.
  Proof.
    intros * POS LE; rewrite addn1 /div_ceil.
    have lkc: (Δ - T) %/ T < Δ %/ T.
    { rewrite divnBr; last by auto.
      rewrite divnn POS.
      rewrite ltn_psubCl //; try ssrlia.
      by rewrite divn_gt0.
    }
    destruct (T %| Δ) eqn:EQ1.
    { have divck:  (T %| Δ) ->  (T %| (Δ - T)); first by auto.
      apply divck in EQ1 as EQ2.
      rewrite EQ2.
      apply lkc. }
    destruct (T %| Δ - T) eqn:EQ, (T %| Δ) eqn:EQ3; by auto.
  Qed.

  
  Remark periodic_task_respects_sporadic_task_model:
    forall tsk, valid_task_min_inter_arrival_time tsk ->
           respects_sporadic_task_model arr_seq tsk ->
           respects_max_arrivals arr_seq tsk (max_arrivals tsk).
  Proof.    
    intros tsk VALID_TIME RESPECTS_SPORADIC x y leq_xy.
    have EX: exists k, y = x + k; first (by exists (y - x); ssrlia).
    move: EX => [k EQ]; subst y; clear leq_xy.
    replace (x + k - x) with k; last by ssrlia.
    have EX: exists l, k <= l; first (by exists k).
    move: EX => [l LE]; move: k LE.
    induction l; intros k LE.
    { move: LE; rewrite leqn0 => /eqP EQ0; subst k.
      rewrite /max_arrivals /sporadic_as_arrival /max_arrivals_for_min_inter_arrival_time
              /number_of_task_arrivals /task_arrivals_between /arrivals_between.
      by rewrite addn0 div_ceil0 big_geq. }
    { have MAX_ONE_JOB := max_one_job_can_arrive_in_one_sporadic_min_inter_arrival_time tsk.
      rewrite /valid_task_min_inter_arrival_time in VALID_TIME.
      set T := task_min_inter_arrival_time tsk.
      destruct (leqP T k) as [LE2 | LT]; first last.
      { clear IHl LE.
        destruct (posnP k) as [Z|POS].
        { subst k.
          by rewrite /number_of_task_arrivals /task_arrivals_between /arrivals_between
                     big_geq; ssrlia. }
        replace x with (x + 0); last by ssrlia.
        replace (x + 0 + k) with (x + k); last by ssrlia.
        { rewrite (leqRW (MAX_ONE_JOB _ _ _ _ _)); try done.
          - rewrite /max_arrivals /sporadic_as_arrival /max_arrivals_for_min_inter_arrival_time.
            by apply div_ceil_gt0.
          - by ssrlia.
         }
      }
      { specialize (IHl (k - T)).
        feed IHl; first by ssrlia.
        rewrite (num_arrivals_of_task_cat _ _ (x + (k - T))); last by ssrlia.
        rewrite (leqRW IHl). rewrite (leqRW (MAX_ONE_JOB _ _ _ _ _)); try done; last by ssrlia.
        rewrite /max_arrivals /sporadic_as_arrival /max_arrivals_for_min_inter_arrival_time.
        by apply leq_div_ceil_add1.
      }
    }
  Qed.
    
End SporadicTasksAsArrivalCurves.
