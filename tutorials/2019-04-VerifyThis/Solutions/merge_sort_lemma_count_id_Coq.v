Goal typed_lemma_count_id.
Hint count_id,property.
Proof.
intros key low high mem1 mem2 a Hint.
elim (Z_lt_ge_dec high low).
+ intros Hgt.
  assert (L_count mem1 a key low high = 0).
  - generalize (FixL_count key low high mem1 a); simpl.
    unfold itep.
    intros (Hdef, _); auto.
  - assert (L_count mem2 a key low high = 0).
    * generalize (FixL_count key low high mem2 a).
      unfold itep; intros (Hdef, _); auto.
    * auto with zarith.
+ intros Hge.
  apply Zlt_lower_bound_ind with (z:=low) (x:=high); auto with zarith.
  intros high1 Hind Hge1 Heq.
  elim (Zle_lt_or_eq _ _ Hge1); clear Hge1.
  - intros Hgt.
    generalize (FixL_count key low high1 mem1 a).
    generalize (FixL_count key low high1 mem2 a).
    unfold itep.
    intros (_ & Heq2 & Hneq2); auto with zarith.
    intros (_ & Heq1 & Hneq1); auto with zarith.
    elim (Z_eq_dec key (mem1 .[ shift_sint32 a high1])).
    * intros Hkeq.
      rewrite <- Heq1; auto with zarith.
      rewrite <- Heq2; auto with zarith.
      ** rewrite <- (Hind (high1 - 1)); auto with zarith.
         intros i3 a1 Hlbi Hhbi.
         apply Heq; auto with zarith.
      ** rewrite <- (Heq high1); auto with zarith.
    * intros Hkneq.
      rewrite <- Hneq1; auto with zarith.
      rewrite <- Hneq2; auto with zarith.
      ** rewrite <- (Hind (high1 - 1)); auto with zarith.
         intros i3 a1 Hlbi Hhbi.
         apply Heq; auto with zarith.
      ** rewrite <- (Heq high1); auto with zarith.
  - intros Hsame.
    rewrite <- Hsame.
    generalize (FixL_count key low low mem1 a).
    generalize (FixL_count key low low mem2 a).
    unfold itep.
    intros (_ & Heq2 & Hneq2); auto with zarith.
    intros (_ & Heq1 & Hneq1); auto with zarith.
    elim (Z_eq_dec key (mem1 .[ shift_sint32 a low])).
    * intros Hkeq.
      rewrite <- Heq1; auto with zarith.
      rewrite <- Heq2; auto with zarith.
      ** replace (L_count mem1 a key low (low - 1)) with 0.
         *** replace (L_count mem2 a key low (low - 1)) with 0; auto with zarith.
             generalize (FixL_count key low (low - 1) mem2 a); unfold itep; simpl; auto with zarith.
         *** generalize (FixL_count key low (low - 1) mem1 a); unfold itep; simpl; auto with zarith.
      ** rewrite <- (Heq low); auto with zarith.
    * intros Hkneq.
      rewrite <- Hneq1; auto with zarith.
      rewrite <- Hneq2; auto with zarith.
      ** replace (L_count mem1 a key low (low - 1)) with 0.
         *** replace (L_count mem2 a key low (low - 1)) with 0; auto with zarith.
             generalize (FixL_count key low (low - 1) mem2 a); unfold itep; simpl; auto with zarith.
         *** generalize (FixL_count key low (low - 1) mem1 a); unfold itep; simpl; auto with zarith.
      ** rewrite <- (Heq low); auto with zarith.
Qed.
