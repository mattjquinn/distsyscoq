Require Export MQuinnIndProp.

Print ev.

Check ev_SS.

Theorem ev_4 : ev 4.
Proof. apply ev_SS. apply ev_SS. apply ev_0. Qed.

Print ev_4. (* EXAMPLE OF A PROOF OBJECT *)

Check (ev_SS 2 (ev_SS 0 ev_0)).

Theorem ev_4' : ev 4.
Proof. apply (ev_SS 2 (ev_SS 0 ev_0)). Qed.

Theorem ev_4'' : ev 4.
Proof.
  Show Proof.
  apply ev_SS.
  Show Proof.
  apply ev_SS.
  Show Proof.
  apply ev_0.
  Show Proof.
Qed.

Definition ev_4''' : ev 4 :=
  ev_SS 2 (ev_SS 0 ev_0).

Print ev_4.
Print ev_4'.
Print ev_4''.
Print ev_4'''.

Theorem ev_8 : ev 8.
Proof. apply ev_SS. apply ev_SS. apply ev_SS. apply ev_SS. apply ev_0. Qed.

Definition ev_8' : ev 8 :=
  ev_SS 6 (ev_SS 4 (ev_SS 2 (ev_SS 0 ev_0))).

