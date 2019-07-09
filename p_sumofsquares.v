Require Import Znumtheory Zdiv ZArith.
Local Open Scope Z_scope.

(* Lemmas I needed over what the Coq library supplies *)

Lemma div_swap_l: forall a b c, a <> 0 -> (a | b) -> b = a * c <-> b / a = c.
Proof.
  intros a b c a_neq_0 a_div_b.
  split.
  - destruct a_div_b as [x def_a].
    intros def_b.
    rewrite def_a.
    rewrite Z_div_mult_full; auto.
    rewrite def_a, Z.mul_comm in def_b.
    rewrite Z.mul_cancel_l in def_b; auto.
  - intros def_b.
    rewrite <- def_b.
    Search (_ * (_ / _)).
    rewrite <- Z.divide_div_mul_exact; auto.
    Search (_ * _ / _).
    rewrite Z.mul_comm.
    symmetry.
    apply Z_div_mult_full; auto.
Qed.

Lemma div_positive: forall a b, a > 0 -> b > 0 -> (a | b) -> b / a > 0.
Proof.
  intros a b a_gt_0 b_gt_0.
  Search (_ | _).
  intros a_div_b.
  destruct a_div_b as [x def_of_x].
  cut (x > 0). intro Cut.
  rewrite def_of_x, Z_div_mult_full; omega.
  rewrite def_of_x in b_gt_0.
  apply (Zmult_gt_reg_r x 0 a); auto.
Qed.

Lemma square_le_lemma: forall m, m > 0 -> (m / 2) * (m / 2) <=  (m * m) / 4.
Proof.
  intros m m_gt_0.
  replace 4 with (2 * 2) by auto.
  apply Zdiv_le_lower_bound; [omega | auto].
  replace ((m / 2) * (m / 2) * (2 * 2)) with ((2 * (m / 2)) * (2 * (m / 2))) by ring.
  apply Z.square_le_mono_nonneg; [auto | apply Z.mul_div_le; omega].
  replace 0 with (2 * 0) by ring.
  apply Zmult_le_compat_l; [apply Zdiv_le_lower_bound | auto]; omega.
Qed.

Lemma square_gt_0: forall n, n <> 0 -> n * n > 0.
Proof.
  intros n n_not_zero.
  destruct n;
    [contradict n_not_zero; reflexivity |
     auto |
     rewrite <- Pos2Z.opp_pos, Z.mul_opp_opp];
    rewrite <- Pos2Z.inj_mul; apply Zgt_pos_0.
Qed.

Lemma Zgt_ge_incl: forall n m: Z, m > n -> m >= n.
  intros n m n_lt_m.
  apply Z.gt_lt in n_lt_m.
  apply Z.lt_le_incl in n_lt_m.
  rewrite Z.ge_le_iff.
  assumption.
Qed.

Lemma square_ge_0: forall n, n * n >= 0.
Proof.
  intros n.
  destruct n;
    [omega |
     auto |
     rewrite <- Pos2Z.opp_pos, Z.mul_opp_opp];
    rewrite <- Pos2Z.inj_mul; apply Zgt_ge_incl; apply Zgt_pos_0.
Qed.

Lemma sum_of_squares_eq_0: forall a b, a * a + b * b = 0 -> a = 0 /\ b = 0.
Proof.
  intros a b.
  intros eq_0.
  remember (square_ge_0 a).
  remember (square_ge_0 b).
  assert (b * b = 0) by omega.
  rewrite H, Z.add_0_r in eq_0.
  rewrite Z.eq_square_0 in H.
  rewrite Z.eq_square_0 in eq_0.
  split; assumption.
Qed.

Lemma sum_of_squares_gt_0: forall a b, a * a + b * b > 0 -> a * a > 0 \/ b * b > 0.
Proof.
  intros a b gt_0.
  omega.
Qed.

(* Begin descent apparatus *)

Definition descent_modulus a m :=
  let m' := a mod m in
  if Z_le_dec (2 * m') m then
    m'
  else
    (a mod m) - m.

Lemma descent_modulus_le_m_div_2 : forall a m,
    m > 0 -> Z.abs (descent_modulus a m) <= m / 2.
Proof.
  intros a m m_gt_1.
  unfold descent_modulus.
  assert (m > 0) as m_gt_0 by omega.
  remember (Z_mod_lt a _ m_gt_0) as m'_bound.
  destruct Heqm'_bound.
  remember (a mod m) as m'.
  destruct (Z_le_dec (2 * m') m).
  - assert (0 <= m') by omega.
    apply Z.abs_eq_iff in H.
    rewrite H.
    apply Zdiv_le_lower_bound; omega.
  - assert (a mod m - m <= 0) as HQuantityNegative by omega.
    rewrite <- Heqm' in HQuantityNegative.
    apply Z.abs_neq_iff in HQuantityNegative.
    rewrite HQuantityNegative.
    apply Zdiv_le_lower_bound; omega.
Qed.

Lemma descent_modulus_equiv_a_mod_m : forall a m,
    m > 0 -> (descent_modulus a m) mod m = a mod m.
Proof.
  intros a m m_gt_0.
  unfold descent_modulus.
  destruct (Z_le_dec (2 * (a mod m)) m).
  - apply (Z_mod_lt a m) in m_gt_0.
    rewrite Zmod_mod; reflexivity.
  - apply (Z_mod_lt a m) in m_gt_0.
    rewrite Zminus_mod, Z_mod_same_full, Z.sub_0_r.
    repeat rewrite Zmod_mod.
    reflexivity.
Qed.

Lemma descent_modulus_eq_0: forall a m, m > 0 -> descent_modulus a m = 0 -> (m | a).
Proof.
  intros a m m_not_0.
  unfold descent_modulus.
  destruct (Z_le_dec (2 * (a mod m)) m).
  - intros eq_0; apply Zmod_divide; omega.
  - intros eq_0. apply Zmod_divide; [omega | ].
    Search (_ - _ = _).
    rewrite Z.sub_move_r in eq_0.
    simpl in eq_0.
    remember (Z_mod_lt a m).
    omega.
Qed.

(* N = a^2 + b^2 = m * q, return (c^2 + d^2)k*q, k < m *)
Definition descent a b q :=
  let N := a * a + b * b in
  let m := N / q in
  if Z.eq_dec m 1 then
    (1, a, b)
  else
    let (u, v) := (descent_modulus a m, descent_modulus b m) in
    ((u * u + v * v) / m, (a * u + b * v)/m, (b * u - a * v)/m).

(* 3^2 + 2^2 = 13 *)
(* 5^2 + 1 = 2 * 13 *)

(* Examples of the descent step *)
Compute (descent 5 1 13).
Compute (descent 12 1 29).
Compute (descent (-7) 3 29).
Compute (descent 442 1 953).
Compute (descent 69 2 953).
Compute (descent (-15) (-41) 953).

Lemma descent_inequality: forall m,
    m > 0 -> (m / 2) * (m / 2) + (m / 2) * (m / 2) < m * m.
Proof.
  intros m m_gt_0.
  cut (((m * m) / 4) + (m * m) / 4 < m * m).
  intros Cut.
  remember (square_le_lemma m m_gt_0).
  omega.
  cut ((m * m / 4 + m * m / 4) <= (m * m / 2)).
  intros Cut.
  apply (Z.le_lt_trans _ (m * m / 2) _ Cut).
  apply Z_div_lt; [omega | apply Zmult_gt_0_compat; auto].
  replace ((m * m / 4) + (m * m / 4)) with (2 * (m * m / 4)) by ring.
  apply Zdiv_le_lower_bound; [omega | auto].
  replace (2 * (m * m / 4) * 2) with (4 * (m * m / 4)) by ring.
  apply Z_mult_div_ge; omega.
Qed.

Lemma descent_nonzero_inequality: forall u v, ~ (u * u + v * v) = 0 -> u * u + v * v > 0.
Proof.
  intros u v c.
  remember (square_ge_0 u).
  remember (square_ge_0 v).
  omega.
Qed.


Lemma descent_nonzero: forall a b q N m,
  prime q ->
  q > 0 -> N > 0 ->
  N = (a * a + b * b) ->
  (q | N) ->
  m = N / q ->
  1 < m < q ->
  descent_modulus a m * descent_modulus a m + descent_modulus b m * descent_modulus b m > 0.
Proof.
  intros a b q N m q_prime q_gt_0 N_gt_0 def_N q_divides_N def_m mt_gt_1.
  remember (descent_modulus a m) as u.
  remember (descent_modulus b m) as v.
  apply descent_nonzero_inequality.
  assert (u * u + v * v = 0 -> (m | a) /\ (m | b)) as zero_means_m_divides_a_and_b.
  intros eq_0.
  rewrite Hequ, Heqv in eq_0.
  apply sum_of_squares_eq_0 in eq_0.
  destruct eq_0 as [H I]; apply descent_modulus_eq_0 in H; apply descent_modulus_eq_0 in I;
    [| omega | omega | omega ]; auto.
  assert ((m | a) /\ (m | b) -> (m * m | a * a + b * b)) as divide_one_divide_all.
  intros [m_div_a m_div_b].
  destruct m_div_a as [k def_k].
  destruct m_div_b as [j def_j].
  exists (k * k + j * j).
  rewrite def_k, def_j; ring.
  assert ((m * m | a * a + b * b) -> (m | q)) as divide_all_implies_divide_prime.
  (* we know q * m = N *)
  (* we know m * m divides N *)
  (* so m divides q *)
  rewrite <- def_N.
  Search (prime _).
  symmetry in def_m.
  rewrite <- (div_swap_l q N) in def_m; [|omega|]; auto.
  rewrite def_m.
  Search (_ * _ | _ * _).
  rewrite Z.mul_divide_cancel_r; [|omega]; auto.
  unfold not.
  intros eq_0.
  apply zero_means_m_divides_a_and_b in eq_0.
  apply divide_one_divide_all in eq_0.
  apply divide_all_implies_divide_prime in eq_0.
  Search (prime _).
  apply (prime_divisors q q_prime m) in eq_0.
  omega.
Qed.

Lemma div_swap_lt_l: forall a b c, a > 0 -> (a | c) -> a * b < c <-> b < c / a.
Proof.
  intros a b c a_gt_0 a_div_c.
  destruct a_div_c as [x def_c].
  rewrite def_c.
  rewrite (Z.mul_comm a b).
  rewrite Z_div_mult_full; [|omega]; auto.
  rewrite <- Z.mul_lt_mono_pos_r; omega.
Qed.

Lemma div_swap_lt_r: forall a b c, a > 0 -> (a | b) -> b < a * c <-> b / a < c.
Proof.
  intros a b c a_gt_0 a_div_c.
  destruct a_div_c as [x def_c].
  rewrite def_c.
  rewrite Z_div_mult_full; [|omega]; auto.
  rewrite (Z.mul_comm x a).
  rewrite <- Z.mul_lt_mono_pos_l; omega.
Qed.

(* Prove that the descent step either terminates or produces a smaller integer *)
Theorem descent_smaller: forall a b q N m,
  prime q ->
  q > 0 -> N > 0 ->
  N = (a * a + b * b) ->
  (q | N) ->
  m = N / q ->
  m < q ->
  forall k t1 t2,  (k, t1, t2) = descent a b q ->
  k = 1 \/ (0 < k < m).
Proof.
  intros a b q N m q_prime q_gt_0 N_gt_0 def_N q_div_N def_m m_lt_q k u v.
  assert (m > 0) as m_gt_0.
  rewrite def_m; apply div_positive; auto.
  unfold descent.
  rewrite <- def_N, <- def_m.
  destruct (Z.eq_dec m 1); intros descent_def; inversion descent_def.
  - left; reflexivity.
  - right.
    split.
    rewrite <- div_swap_lt_l; [ | omega | ]; auto.
    remember (descent_nonzero a b q N m q_prime q_gt_0 N_gt_0 def_N q_div_N def_m); omega.
    rewrite <- Z.mod_divide; [|omega].
    rewrite Zplus_mod.
    rewrite (Zmult_mod (descent_modulus a m)).
    rewrite (Zmult_mod (descent_modulus b m)).
    repeat rewrite descent_modulus_equiv_a_mod_m; auto.
    repeat rewrite <- Zmult_mod.
    repeat rewrite <- Zplus_mod.
    rewrite <- def_N, Z.mod_divide; [|omega].
    exists q.
    rewrite div_swap_l; [auto | omega |assumption].
    rewrite <- (Z.abs_square (descent_modulus a m)).
    rewrite <- (Z.abs_square (descent_modulus b m)).
    apply Z.div_lt_upper_bound; [apply Z.gt_lt; apply m_gt_0; auto | auto].
    remember (descent_modulus_le_m_div_2 a m m_gt_0).
    remember (descent_modulus_le_m_div_2 b m m_gt_0).
    assert ((Z.abs (descent_modulus a m)) *
            (Z.abs (descent_modulus a m)) <= (m / 2) * (m / 2)).
    apply Z.square_le_mono_nonneg; [apply Z.abs_nonneg | auto].
    assert ((Z.abs (descent_modulus b m)) *
            (Z.abs (descent_modulus b m)) <= (m / 2) * (m / 2)).
    apply Z.square_le_mono_nonneg; [apply Z.abs_nonneg | auto].
    assert (Z.abs (descent_modulus a m) *
            Z.abs (descent_modulus a m) +
            Z.abs (descent_modulus b m) *
            Z.abs (descent_modulus b m) <= (m / 2) * (m / 2) + (m / 2) * (m / 2)) by omega.
    apply (Z.le_lt_trans _ _ _ H4).
    apply descent_inequality; auto.
Qed.

Lemma diophantine_identity:
  forall a b c d, (a * a + b * b) * (c * c + d * d) = (a * c + b * d) * (a * c + b * d) + (b * c - a * d) * (b * c - a * d).
Proof.
  intros; ring.
Qed.

Lemma descent_div_sum: forall a b q N m,
  q > 0 -> N > 0 ->
  N = (a * a + b * b) ->
  m = N / q ->
  (q | N) ->
  (m | (descent_modulus a m * descent_modulus a m + descent_modulus b m * descent_modulus b m)).
Proof.
  intros a b q N m q_gt_0 N_gt_0 def_N def_m q_div_N.
  assert (m > 0) as m_gt_0.
  rewrite def_m; apply div_positive; auto.
  rewrite <- Z.mod_divide; [|omega].
  rewrite Zplus_mod.
  repeat rewrite (Zmult_mod (descent_modulus a m) (descent_modulus a m) m), descent_modulus_equiv_a_mod_m; [|omega].
  repeat rewrite (Zmult_mod (descent_modulus b m) (descent_modulus b m) m), descent_modulus_equiv_a_mod_m; [|omega].
  repeat rewrite <- Zmult_mod.
  rewrite <- Zplus_mod.
  rewrite Z.mod_divide; [auto | omega].
  exists q.
  rewrite def_m, def_N.
  apply Zdivide_Zdiv_eq; [omega | auto].
  rewrite <- def_N; auto.
Qed.

Lemma descent_div_N: forall a b q N m,
  q > 0 -> N > 0 ->
  N = (a * a + b * b) ->
  m = N / q ->
  (q | N) -> (m | N).
Proof.
  intros a b q N m q_gt_0 N_gt_0 def_N def_m q_div_N.
  exists q.
  rewrite def_m.
  apply Zdivide_Zdiv_eq; [omega| auto].
Qed.

(*
  (u * u + v * v) / m * q =
  (a * u + b * v) / m * ((a * u + b * v) / m) + (a * v - b * u) / m * ((a * v - b * u) / m)
 *)

Lemma descent_div_term1: forall a b q N m,
  q > 0 -> N > 0 ->
  N = (a * a + b * b) ->
  m = N / q ->
  (q | N) ->
  (m | (a * descent_modulus a m + b * descent_modulus b m)).
Proof.
  intros a b q N m q_gt_0 N_gt_0 def_N def_m q_div_N.
  (* must show m > 0 as ever *)
  assert (m > 0).
  rewrite def_m; apply div_positive; auto.
  rewrite <- Z.mod_divide; [| omega].
  rewrite Zplus_mod, (Zmult_mod a _ _), (Zmult_mod b _ _).
  repeat rewrite descent_modulus_equiv_a_mod_m; auto.
  repeat rewrite <- Zmult_mod.
  repeat rewrite <- Zplus_mod.
  rewrite Z.mod_divide; [| omega].
  exists q.
  rewrite <- def_N.
  rewrite div_swap_l; [auto| omega | auto].
Qed.

Lemma descent_div_term2: forall a b q N m,
  q > 0 -> N > 0 ->
  N = (a * a + b * b) ->
  m = N / q ->
  (q | N) ->
  (m | (b * descent_modulus a m - a * descent_modulus b m)).
Proof.
  intros a b q N m q_gt_0 N_gt_0 def_N def_m q_div_N.
  (* must show m > 0 as ever *)
  assert (m > 0).
  rewrite def_m; apply div_positive; auto.
  rewrite <- Z.mod_divide; [| omega].
  rewrite Zminus_mod, (Zmult_mod a _ _), (Zmult_mod b _ _).
  repeat rewrite descent_modulus_equiv_a_mod_m; auto.
  repeat rewrite <- Zmult_mod.
  repeat rewrite <- Zminus_mod.
  rewrite Z.mul_comm.
  rewrite Z.sub_diag.
  Search (_ mod _ = 0).
  rewrite Zmod_0_l; reflexivity.
Qed.

Lemma add_div_distr: forall a b c,
    a <> 0 -> (a | b) -> (a | c) -> (b + c) / a = b / a + c / a.
Proof.
  intros a b c a_not_0 a_div_b a_div_c.
  destruct a_div_b as [k def_k].
  destruct a_div_c as [j def_j].
  rewrite def_k, def_j.
  replace (k * a + j * a) with ((k + j) * a) by ring.
  repeat rewrite Z_div_mult_full; auto.
Qed.

Lemma descent_mult_key_lemma_sublemma: forall t0 t1 m a,
    m <> 0 ->
    (m | t0) ->
    (m | t1) ->
    (t0 + t1 = m * a) -> (t0 / m + (t1 / m) = a).
Proof.
  intros t0 t1 m a m_not_0 m_div_t0 m_div_t1.
  rewrite (div_swap_l m (t0 + t1) a); auto.
  rewrite add_div_distr; auto.
  apply Z.divide_add_r; auto.
Qed.

Lemma square_div_rearrange: forall a b, b <> 0 -> (b | a) -> a * a / (b * b) = (a / b) * (a / b).
Proof.
  intros a b b_not_0 b_div_a.
  destruct b_div_a.
  rewrite H.
  replace (x * b * (x * b)) with (x * x * (b * b)) by ring.
  repeat rewrite Z_div_mult_full; auto.
  apply Z.neq_mul_0; auto.
Qed.

Lemma descent_mult_key_lemma: forall t0 t1 m a,
    m <> 0 ->
    (m | t0) ->
    (m | t1) ->
    (t0 * t0 + t1 * t1 = m * m * a) -> (t0 / m * (t0 / m) + t1 / m * (t1 / m) = a).
Proof.
  intros t0 t1 m a m_not_0 m_div_t0 m_div_t1.
  assert (m * m <> 0).
  apply Z.neq_mul_0; auto.
  rewrite (div_swap_l (m * m) (t0 * t0 + t1 * t1) a); auto.
  rewrite add_div_distr; auto.
  repeat rewrite square_div_rearrange; auto.
  - destruct m_div_t0 as [k def_k]; exists (k * k); rewrite def_k; ring.
  - destruct m_div_t1 as [j def_j]; exists (j * j); rewrite def_j; ring.
  - destruct m_div_t0 as [k def_k].
    destruct m_div_t1 as [j def_j].
    rewrite def_k, def_j.
    exists (k * k + j * j).
    ring.
Qed.

Theorem descent_mult: forall a b q N,
    q > 0 -> N > 0 -> N = (a * a + b * b) -> (q | N) ->
    forall k r s,
      (k, r, s) = descent a b q ->
      k * q = r * r + s * s.
Proof.
  intros a b q N.
  intros q_gt_0 N_gt_0 def_N q_div_N.
  intros k r s descent_def.
  unfold descent in descent_def.
  rewrite <- def_N in descent_def.
  remember (N / q) as m.
  assert (m > 0) as m_gt_0.
  rewrite Heqm; apply div_positive; auto.
  destruct (Z.eq_dec m 1); inversion descent_def.
  - destruct q_div_N as [x def_N_with_q].
    rewrite Z.mul_1_l, <- def_N, def_N_with_q.
    rewrite e, def_N_with_q in Heqm.
    rewrite Z_div_mult_full in Heqm; [auto | omega].
    symmetry in Heqm.
    rewrite Heqm, Z.mul_1_l; reflexivity.
  - remember (descent_modulus a m) as u.
    remember (descent_modulus b m) as v.
    remember (descent_div_sum a b q N m q_gt_0 N_gt_0 def_N Heqm q_div_N) as m_div_u_v.
    destruct m_div_u_v as [x m_div_u_v].
    assert ((u * u + v * v)*(a * a + b * b) = m * m * x * q) as H.
    destruct Heqm_div_u_v.
    rewrite <- Hequ, <- Heqv in m_div_u_v.
    rewrite Z.gt_lt_iff in q_gt_0.
    destruct q_div_N as [y def_N_with_q].
    rewrite def_N_with_q, Z_div_mult_full in Heqm; [auto | omega].
    rewrite <- Heqm in def_N_with_q.
    rewrite <- def_N, m_div_u_v, def_N_with_q.
    ring.
    rewrite Z.mul_comm in H at 1.
    rewrite diophantine_identity in H.
    remember (a * u + b * v) as t0.
    remember (b * u - a * v) as t1.
    remember (descent_div_term1 a b q N m q_gt_0 N_gt_0 def_N Heqm q_div_N) as div_t0.
    remember (descent_div_term2 a b q N m q_gt_0 N_gt_0 def_N Heqm q_div_N) as div_t1.
    destruct Heqdiv_t0.
    destruct Heqdiv_t1.
    rewrite <- Hequ, <- Heqv, <- Heqt0 in div_t0.
    rewrite <- Hequ, <- Heqv, <- Heqt1 in div_t1.
    replace (m * m * x * q) with (m * m * (x * q)) in H by ring.
    apply descent_mult_key_lemma in H; [ | omega | |]; auto.
    rewrite H.
    destruct Heqm_div_u_v.
    rewrite <- Hequ, <- Heqv in m_div_u_v.
    rewrite (Z.mul_comm x m) in m_div_u_v.
    apply div_swap_l in m_div_u_v; [ | omega | rewrite Hequ, Heqv; apply (descent_div_sum a b q N m)]; auto.
    rewrite m_div_u_v; reflexivity.
Qed.

Compute (descent 557 55 12049).
Compute (descent 242 41 12049).

Check nat.

Require Coq.Init.Nat.
Check Nat.zero.

Fixpoint prime_sum_of_squares_helper a b p (n: nat) :=
  match n with
  | S m => match descent a b p with
             (k, u, v) => if Z.eq_dec k 1 then
                            (u, v)
                          else
                            prime_sum_of_squares_helper u v p m
           end
  | zero => (0, 0)
  end.

Import N2Z.

Definition prime_sum_of_squares a b p :=
  match prime_sum_of_squares_helper a b p (Z.to_nat (a * a + b * b + 1)) with
    (u, v) => (Z.abs u, Z.abs v)
  end.

Lemma prime_sum_of_squares_helper_works: forall n a b p u v,
    prime p ->
    p > 0 ->
    a * a + b * b > 0 ->
    a * a + b * b < p * p ->
    (p | a*a + b*b) ->
    Nat.lt (Z.to_nat (a * a + b * b)) n ->
    (u, v) = prime_sum_of_squares_helper a b p n ->
    u * u + v * v = p.
Proof.
  induction n;
    intros a b p u v p_prime p_gt_0 args_gt_0 args_lt_p_sq p_div_a_square_plus_b_square n_bound;
     unfold prime_sum_of_squares_helper; intros def_u_v.
  contradict n_bound; unfold Nat.lt; omega.
  fold prime_sum_of_squares_helper in def_u_v.
  remember (descent a b p) as c'.
  destruct c' as [[k u'] v'].
  assert ((k, u', v') = descent a b p) as Heqd' by assumption.
  apply (descent_mult a b p (a * a + b * b)) in Heqc'; auto.
  apply (descent_smaller a b p (a * a + b * b) ((a * a + b * b) / p)) in Heqd'; auto.
  destruct (Z.eq_dec k 1); inversion def_u_v.
  - rewrite <- Heqc', e, Z.mul_1_l; reflexivity.
  - assert (u' * u' + v' * v' > 0) as result_gt_0.
    destruct Heqd' as [k_eq_1 | k_bounded];
      [|rewrite <- Heqc'; rewrite Z.gt_lt_iff; apply Z.mul_pos_pos]; omega.
    assert (u' * u' + v' * v' < a * a + b * b) as recursion_bounded.
    destruct Heqd'; [contradict H |]; auto.
    rewrite <- Heqc'.
    rewrite <- div_swap_lt_l in H; auto.
    rewrite Z.mul_comm; destruct H; assumption.
    apply IHn in def_u_v; [ | | | |omega | exists k; symmetry; assumption | ]; auto.
    rewrite Z2Nat.inj_lt in recursion_bounded; [| omega | omega].
    apply lt_n_Sm_le in n_bound.
    apply (lt_le_trans _ (Z.to_nat (a * a + b * b)) _); [assumption | omega].
  - rewrite <- div_swap_lt_r; auto.
Qed.
