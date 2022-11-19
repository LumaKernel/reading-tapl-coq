Set Printing Universes.
Require Import Bool.
Open Scope bool.

(* - 型付き算術式 *)

(* -- 項(term)の定義 *)
  Inductive term: Set :=
  | TRUE: term
  | FALSE: term
  | IF_THEN_ELSE: term -> term -> term -> term
  | ZERO: term
  | SUCC: term -> term
  | PRED: term -> term
  | ISZERO: term -> term.

  Notation "'S' n" := (SUCC n) (at level 4, right associativity).
  Notation "'P' n" := (PRED n) (at level 4, right associativity).
  Notation "0" := ZERO.
  Notation "1" := (S 0).
  Notation "2" := (S 1).
  Notation "3" := (S 2).
  Notation "4" := (S 3).
  Notation "5" := (S 4).
  Notation "6" := (S 5).
  Notation "7" := (S 6).
  Notation "8" := (S 7).
  Notation "9" := (S 8).
  Notation "10" := (S 9).

  Notation "'IF' t1 'THEN' t2 'ELSE' t3" := (IF_THEN_ELSE t1 t2 t3) (at level 3).

  (* 例: 構文同値性はそのままCoqのLeibniz同値性を利用できる *)
  Goal 1 = 1 /\ 2 = 2 /\ IF 1 THEN 2 ELSE 3 <> 4.
    repeat split; compute; trivial.
    intro. discriminate H.
  Qed.


  (* 部分項を定義: subはtの(弱)部分項である、という述語 *)
  Fixpoint subterm (t sub: term): Prop :=
    t = sub \/
    match t with
    | IF t1 THEN t2 ELSE t3 => subterm t1 sub \/ subterm t2 sub \/ subterm t3 sub
    | S t1 => subterm t1 sub
    | P t1 => subterm t1 sub
    | ISZERO t1 => subterm t1 sub
    | _ => False
    end.

  (* 使わないけどおまけで証明．subterm関係のtransitivity *)
  Lemma subterm_transitive: forall (t1 t2 t3: term),
    subterm t1 t2 /\ subterm t2 t3 -> subterm t1 t3.
    intros. destruct H.
    induction t1.
    - destruct t2; destruct t3; compute; compute in H;
      match goal with
      | H: _ \/ _ |- _ => compute in H; destruct H;
        match goal with
        | H: _ = _ |- _ => discriminate H
        | _ => contradiction
        end
      | _ => auto
      end.
    - destruct t2; destruct t3; compute; compute in H;
      match goal with
      | H: _ \/ _ |- _ => compute in H; destruct H;
        match goal with
        | H: _ = _ |- _ => discriminate H
        | _ => contradiction
        end
      | _ => auto
      end.
    - compute in H. destruct H.
    -- rewrite -> H. exact H0.
    -- compute in H. repeat destruct H.
    --- apply IHt1_1 in H. compute. right. compute. left. exact H.
    --- apply IHt1_2 in H. compute. right. compute. right. left. exact H.
    --- apply IHt1_3 in H. compute. right. compute. right. right. exact H.
    - destruct t2; destruct t3; compute; compute in H;
      match goal with
      | H: _ \/ _ |- _ => compute in H; destruct H;
        match goal with
        | H: _ = _ |- _ => discriminate H
        | _ => contradiction
        end
      | _ => auto
      end.
    - compute in H. destruct H.
    -- rewrite -> H. exact H0.
    -- apply IHt1 in H. compute. right. exact H.
    - compute in H. destruct H.
    -- rewrite -> H. exact H0.
    -- apply IHt1 in H. compute. right. exact H.
    - compute in H. destruct H.
    -- rewrite -> H. exact H0.
    -- apply IHt1 in H. compute. right. exact H.
  Qed.

  Lemma subterm_TRUE: forall (t1: term), subterm TRUE t1 -> t1 = TRUE.
  Proof.
    intros. compute in H. destruct H.
    - symmetry. exact H.
    - contradiction.
  Qed.

  Lemma subterm_FALSE: forall (t1: term), subterm FALSE t1 -> t1 = FALSE.
  Proof.
    intros. compute in H. destruct H.
    - symmetry. exact H.
    - contradiction.
  Qed.

  Lemma subterm_ZERO: forall (t1: term), subterm 0 t1 -> t1 = 0.
  Proof.
    intros. compute in H. destruct H.
    - symmetry. exact H.
    - contradiction.
  Qed.
(* -- *)

(* -- 値(value)の定義 *)
  (* --- まずは数値(number value)を定義する *)
  Inductive is_num: term -> Prop :=
  | IS_NUM_ZERO: is_num 0
  | IS_NUM_SUCC: forall (t: term), is_num t -> is_num (S t)
  .

  (* --- そして値を定義する *)
  Inductive is_val: term -> Prop :=
  | IS_VAL_TRUE: is_val TRUE
  | IS_VAL_FALSE: is_val FALSE
  | IS_VAL_NUM: forall (t: term), is_num t -> is_val t
  .
(* -- *)

(* -- 構文形式 *)
  Inductive type: Set :=
    (* Bool *)
    | BOOL: type
    (* Nat *)
    | NAT: type.

(* -- 型付け規則 *)

  (*
    規則(rule)をCoqで表現している。次のように読み替えるとよい。
    forall: メタ変数を定義する。t{n} と T{n} をそれぞれ項と型のメタ変数として利用。
    -> 無しのコンストラクタ: 無前提の規則。公理
    -> ありのコンストラクタ: 前提とその帰結
  *)
  Inductive typing: term -> type -> Prop :=
    (* Bool *)
    | T_TRUE:
        (* ======================================== *)
        typing TRUE BOOL
    | T_FALSE:
        (* ======================================== *)
        typing FALSE BOOL
    | T_IF: forall (t1 t2 t3: term) (T: type),
        typing t1 BOOL -> typing t2 T -> typing t3 T
        (* =============== *) -> (* =============== *)
        typing (IF t1 THEN t2 ELSE t3) T
    (* Nat *)
    | T_ZERO:
        (* ======================================== *)
        typing 0 NAT
    | T_SUCC: forall (t1: term) (T: type),
        typing t1 NAT
        (* =============== *) -> (* =============== *)
        typing (S t1) NAT
    | T_PRED: forall (t1: term) (T: type),
        typing t1 NAT
        (* =============== *) -> (* =============== *)
        typing (P t1) NAT
    | T_ISZERO: forall (t1: term) (T: type),
        typing t1 NAT
        (* =============== *) -> (* =============== *)
        typing (ISZERO t1) BOOL
    .

  (*
    Coq: Notationを利用してtypingをt:Tの形で表記できるようにしている。
         Coqの標準の構文と混同する可能性があるので、おすすめはしない。
  *)
  Notation "t : T" := (typing t T) (at level 13).

  (*
    例: IF (ISZERO 1) THEN 0 ELSE 1 : NAT を示す．
        Inductiveによって定義したので，型付け関係をCoqの証明体系でそのまま≪証明≫できる．
  *)
  Goal IF (ISZERO 1) THEN 0 ELSE 1 : NAT.
    apply T_IF.
    - apply (T_ISZERO 1 BOOL). apply (T_SUCC 0 NAT). exact T_ZERO.
    - exact T_ZERO.
    - apply (T_SUCC 0 NAT). exact T_ZERO.
  Qed.

(* -- 8.2.2. 生成補題(型付け関係の逆転)の証明 *)
  Lemma generation_TRUE: forall (R: type), (TRUE : R) -> R = BOOL.
    intros.
    destruct R.
    - reflexivity.
    - apply False_ind.
      apply (fun (H: (TRUE:NAT)) =>
        match H in (t:T) return
                      match t,T with
                      | TRUE, NAT => False
                      |  _, _ => True
                      end
          with
          | T_TRUE | _ => I
        end).
      apply H.
  Qed.

  Lemma generation_FALSE: forall (R: type), (FALSE : R) -> R = BOOL.
    intros.
    destruct R.
    - reflexivity.
    - apply False_ind.
      apply (fun (H: (FALSE:NAT)) =>
        match H in (t:T) return
                      match t,T with
                      | FALSE, NAT => False
                      |  _, _ => True
                      end
          with
          | T_TRUE | _ => I
        end).
      exact H.
  Qed.

  Lemma generation_IF: forall (t1 t2 t3 : term) (R: type),
    (IF t1 THEN t2 ELSE t3 : R -> t1 : BOOL /\ t2 : R /\ t3 : R).
  Proof.
    exact (
      fun (t1 t2 t3 : term) (R : type) (H : IF t1 THEN t2 ELSE t3 : R) =>
      match H with
      | T_IF _ _ _ _ H1 H2 H3 => conj H1 (conj H2 H3)
      end
    ).
  Qed.

  Lemma generation_ZERO: forall (R: type), (0 : R) -> R = NAT.
    intros.
    destruct R.
    - apply False_ind.
      apply (fun (H: (0:BOOL)) =>
        match H in (t:T) return match t,T with
                    | 0, BOOL => False
                    | _, _ => True
                    end with
        | T_TRUE | _ => I
        end
      ).
      exact H.
    - reflexivity.
  Qed.

  Section SUCC.
    Let sub1: forall (t1: term) (R: type),
        (S t1 : R) -> R = NAT.
    Proof.
      intros.
      destruct R.
      - apply False_ind.
         apply (fun (H: (S t1: BOOL)) =>
           match H in (t:T) return match t,T with
                      | S _, BOOL => False
                      | _, _ => True
                      end
          with
          | T_TRUE | _ => I
          end
         ).
         exact H.
      - reflexivity.
    Qed.

    Let sub2: forall (t1: term),
        (S t1 : NAT) -> (t1:NAT).
    Proof.
      exact (fun (t1: term) (H: (S t1 : NAT)) =>
        match H in (t:T) with
        | T_SUCC _ _ H1 => H1
        end
      ).
    Qed.

    Lemma generation_SUCC: forall (t1: term) (R: type),
        (S t1 : R) -> R = NAT /\ (t1:NAT).
    Proof.
      split.
      - revert t1 R H. exact sub1.
      - assert (H1:=H).
        apply sub1 in H.
        rewrite -> H in (type of H1).
        revert t1 H1. exact sub2.
    Qed.
  End SUCC.

  Section PRED.
    Let sub1: forall (t1: term) (R: type),
        (P t1 : R) -> R = NAT.
    Proof.
      intros.
      destruct R.
      - apply False_ind.
         apply (fun (H: (P t1: BOOL)) =>
           match H in (t:T) return match t,T with
                      | P _, BOOL => False
                      | _, _ => True
                      end
          with
          | T_TRUE | _ => I
          end
         ).
         exact H.
      - reflexivity.
    Qed.

    Let sub2: forall (t1: term),
        (P t1 : NAT) -> (t1:NAT).
    Proof.
      exact (fun (t1: term) (H: (P t1 : NAT)) =>
        match H in (t:T) with
        | T_PRED _ _ H1 => H1
        end
      ).
    Qed.

    Lemma generation_PRED: forall (t1: term) (R: type),
        (P t1 : R) -> R = NAT /\ (t1:NAT).
    Proof.
      split.
      - revert t1 R H. exact sub1.
      - assert (H1:=H).
        apply sub1 in H.
        rewrite -> H in (type of H1).
        revert t1 H1. exact sub2.
    Qed.
  End PRED.

  Section ISZERO.
    Let sub1: forall (t1: term) (R: type),
        (ISZERO t1 : R) -> R = BOOL.
    Proof.
      intros.
      destruct R.
      - reflexivity.
      - apply False_ind.
         apply (fun (H: (ISZERO t1 : NAT)) =>
           match H in (t:T) return match t,T with
                      | ISZERO _, NAT => False
                      | _, _ => True
                      end
          with
          | T_TRUE | _ => I
          end
         ).
         exact H.
    Qed.

    Let sub2: forall (t1: term),
        (ISZERO t1 : BOOL) -> (t1:NAT).
    Proof.
      exact (fun (t1: term) (H: (ISZERO t1 : BOOL)) =>
        match H in (t:T) with
        | T_ISZERO _ _ H1 => H1
        end
      ).
    Qed.

    Lemma generation_ISZERO: forall (t1: term) (R: type),
        (ISZERO t1 : R) -> R = BOOL /\ (t1:NAT).
    Proof.
      split.
      - revert t1 R H. exact sub1.
      - assert (H1:=H).
        apply sub1 in H.
        rewrite -> H in (type of H1).
        revert t1 H1. exact sub2.
    Qed.
  End ISZERO.

  (*
    Coq: 証明におけるいくつかの補足。

    - I は True のコンストラクタ
    - T_TRUE | _ => I というパターンマッチは一見不必要に思える ( _ => I でよい用に思える ) が、 match p with _ => q end は単に q の糖衣構文であるかのように扱われてしまう。
      それに対し、 ... in ... return ... と上述のものを組み合わせると、Coqに明示的に、コンストラクタのとあるパターンが存在しないことを探させることができる。
      例えば、 TRUE : NAT のコンストラクタが存在しない、ということをいうにはこ方法が使える。
  *)

(* -- 8.2.2. 証明終わり。すべてPrintする *)
  Print generation_TRUE.
  Print generation_FALSE.
  Print generation_IF.
  Print generation_SUCC.
  Print generation_PRED.
  Print generation_ISZERO.

(* -- 8.2.3. 正しく型付けされた項の部分項はただしく型付けされている *)
  Lemma subterm_of_typed_term_is_typed:
    forall (t1 t2: term) (T1: type),
      (t1:T1) -> (subterm t1 t2) -> exists (T2: type), (t2:T2).
  Proof.
    intros.
    revert T1 H.
    induction t1.

    (* t1 = TRUE *) (* TRUEの部分項はすべてTRUE，簡単 *)
    - apply subterm_TRUE in H0. rewrite H0.
      exists BOOL. exact T_TRUE.

    (* t1 = FALSE *) (* TRUEと同様 *)
    - apply subterm_FALSE in H0. rewrite H0.
      exists BOOL. exact T_FALSE.

    (* t1 = IF t1_1 THEN t1_2 ELSE t1_3 *)
    - intros. compute in H0. destruct H0.
    (* 自明な場合 (t1 = t2) *)
    -- rewrite -> H0 in H. exists T1. exact H.
      (* Coq: 分割 *)
      -- apply (generation_IF t1_1 t1_2 t1_3 T1) in H. destruct H. destruct H1.
         destruct H0.
    (* subterm t1_1 t2 の場合  *)
    --- assert (H4 := IHt1_1 H0 BOOL H). exact H4.
      (* Coq: 分割 *)
      --- destruct H0.
    (* subterm t1_2 t2 の場合  *)
    ---- assert (H4 := IHt1_2 H0 T1 H1). exact H4.
    (* subterm t1_3 t2 の場合  *)
    ---- assert (H4 := IHt1_3 H0 T1 H2). exact H4.

    (* t1 = 0 *) (* TRUEと同様 *)
    - apply subterm_ZERO in H0. rewrite H0.
      exists NAT. exact T_ZERO.

    (* t1 = S ... *)
    - intros. compute in H0. destruct H0.
    -- rewrite -> H0 in H. exists T1. exact H.
    -- assert (H4 := generation_SUCC t1 T1 H). destruct H4.
       assert (H4 := IHt1 H0 NAT H2). exact H4.

    (* t1 = P ... *)
    - intros. compute in H0. destruct H0.
    -- rewrite -> H0 in H. exists T1. exact H.
    -- assert (H4 := generation_PRED t1 T1 H). destruct H4.
       assert (H4 := IHt1 H0 NAT H2). exact H4.

    (* t1 = ISZERO ... *)
    - intros. compute in H0. destruct H0.
    -- rewrite -> H0 in H. exists T1. exact H.
    -- assert (H4 := generation_ISZERO t1 T1 H). destruct H4.
       assert (H4 := IHt1 H0 NAT H2). exact H4.
  Qed.

  (* 証明終わり．Printする *)
  Print subterm_of_typed_term_is_typed.
