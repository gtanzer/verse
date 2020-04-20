Require Import ZArith String Ascii List Recdef Bool.
Require Import FMapAVL FMapFacts OrderedType OrderedTypeEx.
Require Import Program Equality.
Import ListNotations.

Require Import FSetAVL FSetFacts.

Module IdentSet := FSetAVL.Make(N_as_OT).
Module IdentSetFacts := FSetFacts.WFacts_fun N_as_OT IdentSet.

Module IdentMap := FMapAVL.Make(N_as_OT).
Module IdentMapFacts := FMapFacts.WFacts_fun N_as_OT IdentMap.

Module NatSet := FSetAVL.Make(N_as_OT).
Module NatSetFacts := FSetFacts.WFacts_fun N_as_OT NatSet.

Module NatMap := FMapAVL.Make(N_as_OT).
Module NatMapFacts := FMapFacts.WFacts_fun N_as_OT NatMap.

(* notation for constructing dependent sum types (sigT) *)
Notation "( x & y & .. & z )" := (existT _ .. (existT _ x y) .. z).

(* monad-ish notations for propagating errors *)
Definition bind {A B : Type} : option A -> (A -> option B) -> option B := fun x f => match x with None => None | Some a => f a end.
Notation "'do' X <- A ; B" := (bind A (fun X => B)) (at level 200, X ident, A at level 100, B at level 200).

Remark bind_inversion:
  forall (A B: Type) (f: option A) (g: A -> option B) (y: B),
  bind f g = Some y ->
  exists x, f = Some x /\ g x = Some y.
Proof.
  destruct f; eauto; discriminate.
Qed.
  
Ltac undo H :=
  match type of H with
  | (bind ?F ?G = Some ?X) => eapply bind_inversion in H; do 2 destruct H
  end.

Ltac napply thm H := let H' := fresh "H" in eapply thm in H as H'.
Ltac napply_r thm H := let H' := fresh "H" in eapply thm in H as H'; rewrite H'; cbn.

Ltac branch X :=
  let H := fresh "H" in destruct X eqn:H; inversion H.

Ltac branch2 X H :=
  branch X; try injection H; intros.

Ltac boom' :=
  match goal with
  | [H : (if ?X then _ else _) = _ |- _ ] => branch2 X H
  | [ |- (if ?X then _ else _) = _ ] => branch X
  | [H : match ?X with Some _ => _ | None => _ end = _ |- _] => branch2 X H
  | [ |- match ?X with Some _ => _ | None => _ end = _] => branch X
  | [H : (do _ <- _; _) = _ |- _ ] => undo H
  | [H : (let (_, _) := ?X in _) = _ |- _ ] => branch X
  | [H : exists x, _ |- _ ] => destruct H
  | [H : _ /\ _ |- _ ] => destruct H
  | [H : _ \/ _ |- _ ] => destruct H 
  | [H: Some _ = Some _ |- _ ] => inversion H; subst
  end.

Ltac boom :=
  cbn in *; eauto; boom'; subst; try discriminate; try contradiction; eauto.

(* typeclass for decidable equality *)
Class decidable (A : Type) := {
  eq_dec : forall (a1 a2 : A), {a1 = a2} + {a1 <> a2};
}.

Definition eqb {A} {dec : decidable A} (a1 a2 : A) := if eq_dec a1 a2 then true else false.

Theorem eqb_refl {A} {dec : decidable A} : forall a, eqb a a = true.
Proof.
  intros. unfold eqb; destruct (eq_dec a a); auto.
Qed.

Theorem eqb_eq {A} {dec : decidable A} : forall a1 a2, eqb a1 a2 = true <-> a1 = a2.
Proof.
  intros; unfold eqb; destruct (eq_dec a1 a2); split; subst; auto; discriminate.
Qed.

Theorem eqb_neq {A} {dec : decidable A} : forall a1 a2, eqb a1 a2 = false <-> a1 <> a2.
Proof.
  intros; unfold eqb; destruct (eq_dec a1 a2); split; subst; auto; try discriminate; try contradiction.
Qed.

(* generates eqb, eqb_eq, and eqb_neq from an eq_dec *)
Instance gen_dec {A} eq_dec : decidable A := {
  eq_dec := eq_dec;
}.

Instance bool_dec : decidable bool := gen_dec bool_dec.
Instance nat_dec : decidable nat := gen_dec Nat.eq_dec.
Instance N_dec : decidable N := gen_dec N.eq_dec.
Instance Z_dec : decidable Z := gen_dec Z.eq_dec.
Instance string_dec : decidable string := gen_dec string_dec.
#[refine] Instance unit_dec : decidable unit := gen_dec _.
  Proof. intros. decide equality. Defined.
#[refine] Instance option_dec A {dec : decidable A}: decidable (option A) := gen_dec _.
  Proof. decide equality. apply eq_dec. Defined.
#[refine] Instance pair_dec A B {decA : decidable A} {decB : decidable B} : decidable (A * B) := gen_dec _.
  Proof. decide equality; apply eq_dec. Defined.

Section PolyMap.
  (* key-polymorphic map implemented as an association list
     requires only an eq_dec for the key type *)
  Definition PolyMap (kt vt : Type) (dec : decidable kt) := list (kt * vt).

  (* an empty PolyMap *)
  Definition PolyMap_empty {kt vt dec} : PolyMap kt vt dec := [].

  (* remove key k from map m *)
  Fixpoint PolyMap_remove {kt vt dec} k m : PolyMap kt vt dec :=
    match m with
    | [] => []
    | (a, b) :: abs => let rest := PolyMap_remove k abs in
                       if eq_dec a k then rest else (a, b) :: rest
    end.

  (* add key-value pair k v to map m *)
  Definition PolyMap_add {kt vt dec} k v m : PolyMap kt vt dec :=
    (k, v) :: PolyMap_remove k m.

  (* return the Some value of key k in map m if it exists, or None otherwise *)
  Fixpoint PolyMap_find {kt vt dec} k (m : PolyMap kt vt dec) : option vt :=
    match m with
    | [] => None
    | (a, b) :: abs => if eq_dec a k then Some b else PolyMap_find k abs
    end.

  Definition PolyMap_find_pf {kt vt dec} k (m : PolyMap kt vt dec) : option {s : vt | PolyMap_find k m = Some s}.
    remember (PolyMap_find k m). destruct o; [ apply Some; now exists v | apply None ]. Defined.

  Lemma PolyMap_find_impl_In :
    forall (kt vt : Type) (dec : decidable kt) m k v,
      @PolyMap_find kt vt dec k m = Some v -> In (k, v) m.
  Proof.
    induction m; cbn; intros.
    discriminate. destruct a, (eq_dec k0 k); subst;
    [inject H | apply IHm in H]; auto.
  Qed.

  (* return true if map m has a binding for key k and false otherwise *)
  Fixpoint PolyMap_mem {kt vt dec} k (m : PolyMap kt vt dec) : bool :=
    match m with
    | [] => false
    | (a, b) :: abs => if eq_dec a k then true else PolyMap_mem k abs
    end.

  (* the proposition that key k has a mapping in map m *)
  Definition PolyMap_In {kt vt dec} k (m : PolyMap kt vt dec) := exists v, In (k, v) m.
End PolyMap.

Section PolySet.
  (* key-polymorphic set implemented as a list
     requires only an eq_dec for the element type *)
  Definition PolySet (kt : Type) (dec : decidable kt) := list kt.

  (* an empty PolySet *)
  Definition PolySet_empty {kt dec} : PolySet kt dec := [].

  (* remove element k from set s *)
  Fixpoint PolySet_remove {kt dec} k s : PolySet kt dec :=
    match s with
    | [] => []
    | x :: xs => let rest := PolySet_remove k xs in
                 if eq_dec x k then rest else x :: rest
    end.

  (* add element k to set s *)
  Definition PolySet_add {kt dec} k s : PolySet kt dec :=
    k :: PolySet_remove k s.

  (* return true if element k is a member of set s and false otherwise *)
  Fixpoint PolySet_mem {kt dec} k (s : PolySet kt dec) : bool :=
    match s with
    | [] => false
    | x :: xs => if eq_dec x k then true else PolySet_mem k xs
    end.

  (* the proposition that element k is in set s *)
  Definition PolySet_In {kt dec} k (s : PolySet kt dec) := In k s.

  Definition PolySet_union {kt dec} (s1 s2 : PolySet kt dec) : PolySet kt dec :=
    fold_left (fun s e1 => PolySet_add e1 s) s1 s2.

  Definition list_prod {A B} (l1 : list A) (l2 : list B) : list (A * B) :=
    fold_left (fun l a => (map (fun b => (a, b)) l2) ++ l) l1 [].

  Definition PolySet_prod {kt1 kt2 dec1 dec2} (s1 : PolySet kt1 dec1) (s2 : PolySet kt2 dec2) : PolySet (kt1 * kt2) _ :=
    list_prod s1 s2.

  Definition PolySet_option_prod {kt1 kt2} {dec1 : decidable kt1} {dec2 : decidable kt2} (s1 : PolySet (option kt1) _) (s2 : PolySet (option kt2) _) : PolySet (option (kt1 * kt2)) _ :=
    fold_left (fun s oe1 =>
      fold_left (fun s oe2 =>
        match oe1, oe2 with
        | Some e1, Some e2 => Some (e1, e2) :: s
        | _, _ => PolySet_add None s
        end) s2 s) s1 [].
End PolySet.

(* non-empty list *)
Inductive nelist (A : Type) :=
  | NEBase : A -> nelist A
  | NECons : A -> nelist A -> nelist A.

Notation "+[ x ]" := (NEBase _ x).
Notation "a +:: b" := (NECons _ a b) (at level 20).
Notation "+[ x ; .. ; y ; z ]" := (NECons _ x .. (NECons _ y (NEBase _ z)) ..).

Fixpoint NEIn {A} (a : A) (l : nelist A) : Prop :=
  match l with
    | +[b] => b = a
    | b +:: m => b = a \/ NEIn a m
  end.

Fixpoint nemap {A B} (f : A -> B) (l : nelist A) :=
  match l with
  | +[x] => +[f x]
  | x +:: xs => f x +:: nemap f xs
  end.

Section nefold.
  Variables (A : Type) (B : Type).
  Variable f : A -> B -> A.

Fixpoint nefold (l : nelist B) (a : A) :=
  match l with
  | +[x] => f a x
  | x +:: xs => nefold xs (f a x)
  end.
End nefold.

#[refine] Instance nelist_dec A {dec : decidable A} : decidable (nelist A) := gen_dec _.
Proof. decide equality; apply eq_dec. Defined.

(* free identifiers (for primitive names) *)
Definition id := N.
Definition id_ctxt A := IdentMap.t A.

(* bound identifiers (for function arguments, including example input) *)
Definition bid := N.
Definition bid_ctxt A := NatMap.t A.

(* dsl grammar rule identifiers *)
Definition rid := N.
Definition rid_ctxt A := NatMap.t A.

(* dsl identifiers, for recursive dsls *)
Definition lid := N.

(* primitive identifiers, in a compiled library *)
Definition pid := N.
Definition pid_ctxt A := NatMap.t A.

(* vsa rule identifiers *)
Definition vid := N.
Definition vid_ctxt A := NatMap.t A.

(* stream identifiers, for recursive synthesis (for functions) *)
Definition sid := N.

(* type of a value (anything that can be input/output of synthesis) *)
Inductive vtype :=
  | TBool | TNat | TInt | TStr
  | TPair : vtype -> vtype -> vtype
  | TList : vtype -> vtype.

(* overall type, including functions *)
(* functions are not values *)
Inductive type :=
  | TVal : vtype -> type
  | TFun : vtype -> vtype -> type.

(* represents the argument types for a primitive function *)
Definition ftype := nelist type.

#[refine] Instance vtype_dec : decidable vtype := gen_dec _.
  Proof. decide equality. Defined.
#[refine] Instance type_dec : decidable type := gen_dec _.
  Proof. decide equality; apply eq_dec. Defined.

(* raise a vtype vt into its native Coq equivalent *)
Fixpoint vraise vt : Type :=
  match vt with
  | TBool => bool
  | TNat => nat
  | TInt => Z
  | TStr => string
  | TPair vt1 vt2 => (vraise vt1) * (vraise vt2)
  | TList vt => list (vraise vt)
  end.

(* the type of a collection of examples for inductive synthesis *)
Definition examples I O := nelist (vraise I * vraise O).

Inductive exp {tid : Type} :=
  | EB : bid -> exp                            (* bound id *)
  | EC vt : vraise vt -> exp                   (* constant *)
  | EL : bid -> vtype -> exp -> exp            (* lambda *)
  | EF : ftype -> tid -> nelist_exp -> exp     (* primitive *)
with nelist_exp {tid : Type} :=
  | EBase : exp -> nelist_exp
  | ECons : exp -> nelist_exp -> nelist_exp.

Definition corpus {tid} : Type := vtype * vtype * nelist (@exp tid).

Definition texp := @exp pid.

(* raise a type t into its native Coq equivalent for forward semantics
   functions are not represented natively, but rather as an algebraic expression type *)
Fixpoint traise_fw E t : Type :=
  match t with
  | TVal vt => vraise vt
  | TFun vt rt => bid * vtype * E
  end.

Definition traise_fwt := traise_fw texp.

(* raise a type t into its native Coq equivalent for backward semantics / deduction
   functions are represented as specifications for recursive synthesis *)
Fixpoint traise_bw t : Type :=
  match t with
  | TVal vt => vraise vt
  | TFun vt rt => examples vt rt
  end.

Fixpoint fraise (traise : type -> Type) ft : Type :=
  match ft with
  | +[t] => option (traise t)
  | t +:: ft => (option (traise t)) * (fraise traise ft)
  end.

Definition fraise_fwt := fraise (traise_fw texp).
Definition fraise_bw := fraise traise_bw.

(* create a tuple of Ts with the shape of ft *)
Fixpoint fraiseT (T : Type) (ft : ftype) : Type :=
  match ft with
  | +[t] => T
  | t +:: ft => T * (fraiseT T ft)
  end.

#[refine] Instance vraise_dec vt : decidable (vraise vt) := gen_dec _.
Proof. intros; induction vt; cbn in *; try apply eq_dec; decide equality. Defined.

Ltac prune H := destruct H; [subst; try now left | right; injection; intros; try contradiction].

Lemma exp_dec : forall tid (dec : decidable tid) (te1 te2 : @exp tid), {te1 = te2} + {te1 <> te2}
with nelist_exp_dec : forall tid (dec : decidable tid) (tes1 tes2 : @nelist_exp tid), {tes1 = tes2} + {tes1 <> tes2}.
Proof.
  - clear exp_dec. induction te1; destruct te2; try (right; discriminate).
    + prune (eq_dec b b0).
    + prune (eq_dec vt vt0). prune (eq_dec v v0).
      apply Eqdep_dec.inj_pair2_eq_dec in H0.
      contradiction. apply eq_dec.
    + prune (eq_dec b b0). prune (eq_dec v v0). prune (IHte1 te2).
    + prune (eq_dec f f0). prune (eq_dec t t0). prune (nelist_exp_dec _ _ n n0).
  - clear nelist_exp_dec. decide equality.
Defined.

#[refine] Instance exp_dec2 tid (dec : decidable tid) : decidable (@exp tid) := gen_dec (exp_dec tid dec). Defined.
#[refine] Instance nelist_exp_dec2 tid (dec : decidable tid) : decidable (@nelist_exp tid) := gen_dec (nelist_exp_dec tid dec). Defined.
#[refine] Instance traise_fw_dec E t (dec : decidable E) : decidable (traise_fw E t) := gen_dec _.
  Proof. intros; destruct t; apply eq_dec. Defined.
#[refine] Instance fraise_fw_dec E t (dec : decidable E) : decidable (fraise (traise_fw E) t) := gen_dec _.
  Proof. intros; induction t. apply eq_dec. decide equality; apply eq_dec. Defined.
#[refine] Instance traise_bw_dec t : decidable (traise_bw t) := gen_dec _.
  Proof. intros; destruct t. apply eq_dec. decide equality; apply eq_dec. Defined.
#[refine] Instance fraise_bw_dec ft : decidable (fraise_bw ft) := gen_dec _.
  Proof. intros; induction ft. apply eq_dec. decide equality; apply eq_dec. Defined.
#[refine] Instance fraiseT_dec T ft (dec : decidable T) : decidable (fraiseT T ft) := gen_dec _.
  Proof. intros; induction ft; cbn in *; repeat decide equality; apply eq_dec. Defined.

(* tuple of bools corresponding to whether each argument to a primitive
     should be generated from the top down (from B and C tconstructors) 
     and provided to the backward semantics *)
Definition ftbool ft := fraiseT bool ft.

Fixpoint fraiseb (ft : ftype) (ftb : ftbool ft) : Type :=
  match ft, ftb with
  | +[t], b => if b then option (traise_fwt t) else unit
  | t +:: ft, (b, ftb) => (if b then option (traise_fwt t) else unit) * (fraiseb ft ftb)
  end.

(* grammar constructor for a value of type vt *)
Inductive gconstructor {tid : Type} (vt : vtype) :=
  | B : bid -> gconstructor vt                      (* bound id *)
  | C : vraise vt -> gconstructor vt                (* specific constant *)
  | T : gconstructor vt                             (* arbitrary constant *)
  | F ft : tid -> fraiseT rid ft -> gconstructor vt (* primitive *).

(* grammar rule *)
Inductive grule {tid : Type} :=
  | R (vt : vtype) : nelist (@gconstructor tid vt) -> grule (* normal constructor *)
  | L (rt : vtype) : bid -> vtype -> lid -> grule           (* lambda *).

(* a domain specific library grammar is a collection of rules, indexed by rids *)
Inductive dsl {tid} :=
| DSL : rid_ctxt (bool * @grule tid) -> PolyMap lid dsl _ -> dsl.

#[refine] Instance gconstructor_dec tid (dec : decidable tid) vt : decidable (@gconstructor tid vt) := gen_dec _.
  Proof. intros. destruct a1, a2; try (right; discriminate).
  - prune (eq_dec b b0).
  - prune (eq_dec v v0).
  - now left.
  - prune (eq_dec ft ft0). prune (eq_dec t t0). prune (eq_dec f f0). dependent destruction H. contradiction.
  Defined.

(* the type of primitive forward semantics *)
Definition fsem (ft : ftype) (rt : vtype) :=
  forall tid, fraise (traise_fw (@exp tid)) ft -> option (vraise rt).

(* the type of primitive backward semantics *)
Definition bsem (ft : ftype) (rt : vtype) (ftb : ftbool ft) :=
  vraise rt -> fraiseb ft ftb -> list (fraise_bw ft).
  
(* a primitive's type, plus forward and backward semantics *)
Inductive prim :=
  | P (ft : ftype) (rt : vtype) (ftb : ftbool ft) : fsem ft rt -> bsem ft rt ftb -> prim.

(* type context for bound ids *)
Definition btctxt := bid_ctxt vtype.

(* value context for bound ids (essentially environment semantics) *)
Definition bctxt := bid_ctxt {vt & vraise vt}.
Definition btctxt_from_bctxt (b : bctxt) : btctxt := NatMap.map (fun vtv => projT1 vtv) b.
Definition bctxt_empty := NatMap.empty {vt & vraise vt}.

(* btctxt and bctxts are compatible when the types for all bindings match *)
Definition wt_bctxt (tc : btctxt) (c : bctxt) :=
  forall b vt, NatMap.MapsTo b vt tc <-> exists v, NatMap.MapsTo b (vt & v) c. 

Definition bt_input I : btctxt := NatMap.add N0 I (NatMap.empty _).
Definition b_input I i : bctxt :=  NatMap.add N0 (I & i) (NatMap.empty _).

Definition transfer {T} {decT : decidable T} (f : T -> Type) {decf : forall x, decidable (f x)} A B : f A -> option (f B).
Proof.
  intros. destruct (eq_dec A B); [subst | apply None]. apply (Some X).
Defined.

Lemma transfer_refl {T} {decT : decidable T} {f} {decf : forall x, decidable (f x)} : forall a b, transfer f a a b = Some b.
Proof.
  intros. unfold transfer. destruct (eq_dec a a); [| contradiction].
  erewrite <- rew_swap; eauto. unfold eq_rect.
  dependent destruction e. auto.
Qed.

Lemma transfer1 {T} {decT : decidable T} {f} {decf : forall x, decidable (f x)} : forall a b c d, transfer f a b c = Some d -> a = b.
Proof.
  intros. unfold transfer in H. destruct (eq_dec a b); [now subst | discriminate].
Qed.

Lemma transfer2 {T} {decT : decidable T} {f} {decf : forall x, decidable (f x)} : forall a c d, transfer f a a c = Some d -> c = d.
Proof.
  intros. unfold transfer in H. destruct (eq_dec a a); try contradiction.
  unfold eq_rect_r in H. unfold eq_rect in H. dependent destruction e. cbn in H. now inversion H.
Qed.

Definition transfer_fw := transfer traise_fwt.
Definition transfer_bw := transfer traise_bw.
Definition vtransfer A B := transfer_fw (TVal A) (TVal B).

Lemma transfer1Val : forall t a b c d (dec : forall v, decidable (traise_fw (@exp t) v)), transfer (traise_fw exp) (TVal a) (TVal b) c = Some d -> a = b.
Proof. intros. apply transfer1 in H. now injection H. Qed.

Lemma transfer2Val : forall t a c d (dec : forall v, decidable (traise_fw (@exp t) v)), transfer (traise_fw exp) (TVal a) (TVal a) c = Some d -> c = d.
Proof. intros. now apply transfer2 in H. Qed.

Ltac fork H := let Heq := fresh "Heq" in destruct H eqn:Heq.

Ltac scrub :=
  repeat match goal with
  | [H : ?X = ?X |- _ ] => clear H
  end.

Ltac condense :=
  match goal with
  | [H : eqb ?X ?Y = true |- _ ] => let T := type of X in eapply (@eqb_eq T) in H
  | [H : eqb ?X ?Y = false |- _ ] => let T := type of X in eapply (@eqb_neq T) in H
  end; subst; try contradiction; scrub.

Ltac scatter :=
  repeat match goal with
  | [H : {_ & _} |- _ ] => destruct H
  | [H : {_ | _} |- _ ] => destruct H
  | [H : (_, _) |- _ ] => destruct H
  | [H : _ * _ |- _ ] => destruct H
  | [H : let '_ := ?X in _ |- _ ] => destruct X
  | [H : prim |- _ ] => destruct H
  end.

Ltac equate A B := destruct (eq_dec A B); [subst | apply None].
Ltac ret A := apply (Some A).
Ltac forkL H := fork H; [|apply None].
Ltac forkR H := fork H; [apply None|].
Ltac search k m := fork (NatMap.find k m); [scatter | apply None].

Ltac switch H callback :=
  match type of H with
  | IdentMap.MapsTo _ _ _ => callback IdentMapFacts.find_mapsto_iff H
  | IdentMap.find _ _ = Some _ => callback IdentMapFacts.find_mapsto_iff H
  | NatMap.MapsTo _ _ _ => callback NatMapFacts.find_mapsto_iff H
  | NatMap.find _ _ = Some _ => callback NatMapFacts.find_mapsto_iff H
  | ~ NatMap.In _ _ => callback NatMapFacts.not_mem_in_iff H
  | NatMap.mem _ _ = false => callback NatMapFacts.not_mem_in_iff H
  end.

Ltac flip H := switch H napply.
Ltac click H := switch H napply_r.
Ltac inject H := injection H; intros; subst.
Ltac invert H := inversion H; subst.
Ltac splitb H := apply andb_prop in H; destruct H.
Ltac depinvert H := dependent destruction H. 
Ltac depinject H := inversion H; subst; apply Eqdep_dec.inj_pair2_eq_dec in H; subst;[|apply eq_dec].
Ltac untransfer H := let H' := fresh "H" in apply transfer1Val in H as H'; subst; apply transfer2Val in H; subst.

Definition MTT {tid lib} := tid -> prim -> lib -> Prop.
Definition FDT {tid lib} := tid -> lib -> option prim.

Definition MapsTo_fun {tid lib} (MapsTo : MTT) :=
  forall (m : lib) (x : tid) (e e' : prim),
    MapsTo x e m -> MapsTo x e' m -> e = e'.

Definition find_mapsto_iff {tid lib} (find : FDT) (MapsTo : MTT) :=
  forall (m : lib) (x : tid) (e : prim),
    MapsTo x e m <-> find x m = Some e.

Fixpoint eval {tid} {dec : decidable tid} {lib} (find : FDT) (p : lib) (b : bctxt) (B : type) (e : @exp tid) : option (option (traise_fw (@exp tid) B)) :=
  match e with
  | EB ib => do vtv <- NatMap.find ib b;
              let (vt, v) := vtv in
              do v' <- transfer (traise_fw (@exp tid)) (TVal vt) B v;
              Some (Some v')
  | EC vt v => do v' <- transfer (traise_fw (@exp tid)) (TVal vt) B v;
                Some (Some v')
  | EL x bt e' => match B with
                  | TVal _ => None
                  | TFun bt' _ => if eqb bt bt'
                                  then Some (Some (x, bt, e'))
                                  else None
                  end
  | EF ft' ip es => do pr <- find ip p;
                    let '(P ft rt ftb fs bs) := pr in
                    if eqb ft ft'
                    then do vargs <- eval_args find p b ft es;
                          let v := (@fs tid vargs) in
                          match v with
                          | Some v' => Some (transfer (traise_fw (@exp tid)) (TVal rt) B v')
                          | None => Some (None)
                          end
                    else None
  end
with eval_args {tid} {dec : decidable tid} {lib} (find : FDT) (p : lib) (b : bctxt) (FT : ftype) (es : @nelist_exp tid) : option (fraise (traise_fw (@exp tid)) FT) :=
  match es, FT with
  | EBase e, +[t] => eval find p b t e
  | ECons e es', t +:: ts => do v <- eval find p b t e;
                              do vs <- eval_args find p b ts es';
                              Some (v, vs)
  | _, _ => None
  end.

Definition interpret {tid} {dec : decidable tid} {lib} (find : FDT) (p : lib) (I O : vtype) (e : @exp tid) (i : vraise I) : option (option (vraise O)) :=
  eval find p (b_input I i) (TVal O) e.

Inductive wt_exp {tid lib} {MapsTo : MTT} : lib -> btctxt -> @exp tid -> type -> Prop :=
  | WT_EB : forall vt p b ib,
              NatMap.MapsTo ib vt b ->
                wt_exp p b (EB ib) (TVal vt)
  | WT_EC : forall vt p b v,
              wt_exp p b (EC vt v) (TVal vt)
  | WT_EL : forall p b x e bt rt,
              wt_exp p (NatMap.add x bt b) e (TVal rt) ->
                wt_exp p b (EL x bt e) (TFun bt rt)
  | WT_EF : forall p b ip es ft rt ftb fs bs,
              MapsTo ip (P ft rt ftb fs bs) p ->
              wt_nelist_exp p b es ft ->
                wt_exp p b (EF ft ip es) (TVal rt)
with wt_nelist_exp {tid lib} {MapsTo : MTT} : lib -> btctxt -> @nelist_exp tid -> ftype -> Prop :=
  | WT_EBase : forall p b e t,
                 wt_exp p b e t ->
                   wt_nelist_exp p b (EBase e) +[t]
  | WT_ECons : forall p b e es t ts,
                 wt_exp p b e t ->
                 wt_nelist_exp p b es ts ->
                   wt_nelist_exp p b (ECons e es) (t +:: ts).

Inductive wt_corpus {tid lib} {MapsTo : MTT} : lib -> @corpus tid -> Prop :=
  | WTCBase : forall p I O e,
                @wt_exp tid lib MapsTo p (bt_input I) e (TVal O) ->
                  wt_corpus p (I, O, +[e])
  | WTCCons : forall p I O e es,
                @wt_exp tid lib MapsTo p (bt_input I) e (TVal O) ->
                wt_corpus p (I, O, es) ->
                  wt_corpus p (I, O, e +:: es).

Fixpoint tc_exp {tid} {dec : decidable tid} {lib} (find : FDT)
         (p : lib) (b : btctxt) (e : @exp tid) (t : type) : bool :=
  match e with
  | EB ib => match NatMap.find ib b with
             | Some vt => eqb t (TVal vt)
             | None => false
             end
  | EC vt c => eqb t (TVal vt)
  | EL ib bt e' => match t with
                   | TFun bt' rt' => eqb bt bt'
                                     && tc_exp find p (NatMap.add ib bt b) e' (TVal rt')
                   | _ => false
                   end
  | EF ft ip es => match find ip p with
                   | Some (P ft' rt ftb fs bs) => eqb ft ft'
                                                  && eqb t (TVal rt)
                                                  && tc_nelist_exp find p b es ft
                   | None => false
                   end
  end
with tc_nelist_exp {tid} {dec : decidable tid} {lib} (find : FDT)
     (p : lib) (b : btctxt) (es : @nelist_exp tid) (ft : ftype) : bool :=
  match es, ft with
  | EBase e, +[t] => tc_exp find p b e t
  | ECons e es', t +:: ft' => tc_exp find p b e t
                              && tc_nelist_exp find p b es' ft'
  | _, _ => false
  end.

Fixpoint tc_exps {tid} {dec : decidable tid} {lib} (find : FDT)
         (p : lib) (I O : vtype) (es : nelist (@exp tid)) : bool :=
  match es with
  | +[e] => tc_exp find p (bt_input I) e (TVal O)
  | e +:: es' => (tc_exp find p (bt_input I) e (TVal O))
                 && tc_exps find p I O es'
  end.

Definition tc_corpus {tid} {dec : decidable tid} {lib} (find : FDT)
                     (p : lib) (c : @corpus tid) : bool :=
  let '(i, o, es) := c in
  tc_exps find p i o es.

Lemma tc_exp_correctness :
  forall tid d l F M (FMI : find_mapsto_iff F M) (MF: MapsTo_fun M),
  forall p b e t,
    @tc_exp tid d l F p b e t = true <-> @wt_exp tid l M p b e t
with tc_nelist_exp_correctness :
  forall tid d l F M (FMI : find_mapsto_iff F M) (MF: MapsTo_fun M),
  forall p b es ft,
    @tc_nelist_exp tid d l F p b es ft = true <-> @wt_nelist_exp tid l M p b es ft.
Proof with eauto; cbn.
  - clear tc_exp_correctness; unfold iff; split; revert p b t;
    induction e; intros; cbn in *.
    + boom; condense. apply NatMapFacts.find_mapsto_iff in H0; econstructor...
    + condense. econstructor.
    + destruct t. discriminate. splitb H.
      condense. apply IHe in H0. econstructor...
    + repeat boom. repeat splitb H. repeat condense.
      eapply tc_nelist_exp_correctness in H1...
      apply FMI in H0. econstructor...
    + invert H. apply NatMapFacts.find_mapsto_iff in H3.
      rewrite H3. apply eqb_refl.
    + invert H. depinject H4. apply eqb_refl. 
    + invert H. rewrite eqb_refl. apply IHe in H6...
    + invert H. apply FMI in H6. rewrite H6.
      do 2 rewrite eqb_refl. eapply tc_nelist_exp_correctness in H7...
      now rewrite H7.
  - clear tc_nelist_exp_correctness; unfold iff; split; revert p b ft;
    induction es; intros; cbn in *.
    + destruct ft. eapply tc_exp_correctness in H...
      econstructor... discriminate.
    + destruct ft. discriminate. splitb H.
      eapply tc_exp_correctness in H... econstructor...
    + invert H. eapply tc_exp_correctness in H3...
    + invert H. eapply tc_exp_correctness in H4...
      eapply IHes in H6. rewrite H4. now rewrite H6.
Qed.

Lemma tc_exps_correctness :
  forall t d l F M (FMI : find_mapsto_iff F M) (MF: MapsTo_fun M),
  forall es p I O,
    @tc_exps t d l F p I O es = true <-> @wt_corpus t l M p (I, O, es).
Proof with eauto; cbn.
  unfold iff; split; revert p I O; induction es; intros.
  - invert H. eapply tc_exp_correctness in H1... econstructor...
  - invert H. apply andb_prop in H1; destruct H1.
    eapply tc_exp_correctness in H0... econstructor...
  - invert H. eapply tc_exp_correctness in H2...
  - invert H. eapply tc_exp_correctness in H3... eapply IHes in H6...
    rewrite H3. now rewrite H6.
Qed.

Theorem tc_corpus_correctness :
  forall t d l F M (FMI : find_mapsto_iff F M) (MF: MapsTo_fun M),
  forall p c,
    @tc_corpus t d l F p c = true <-> @wt_corpus t l M p c.
Proof.
  intros. destruct c, p0. cbn. now apply tc_exps_correctness.
Qed.

(* large step semantics for texps *)
Inductive lstep_exp {tid lib} {MapsTo : MTT} : lib -> bctxt -> @exp tid -> {t & option (traise_fw (@exp tid) t)} -> Prop :=
  | LS_EB : forall p b ib vt v,
              NatMap.MapsTo ib (vt & v) b ->
                lstep_exp p b (EB ib) (TVal vt & Some v)
  | LS_EC : forall p b vt v,
              lstep_exp p b (EC vt v) (TVal vt & Some v)
  | LS_EL : forall p b x bt rt e,
              lstep_exp p b (EL x bt e) (TFun bt rt & Some (x, bt, e))
  | LS_EF : forall p b ip ft rt ftb fs bs es args,
              MapsTo ip (P ft rt ftb fs bs) p ->
              lstep_nelist_exp p b es (ft & args) ->
                lstep_exp p b (EF ft ip es) (TVal rt & fs tid args)
with lstep_nelist_exp {tid lib} {MapsTo : MTT} : lib -> bctxt -> @nelist_exp tid -> {ft & fraise (traise_fw (@exp tid)) ft} -> Prop :=
  | LS_EBase : forall p b e T t,
                 lstep_exp p b e (T & t) ->
                   lstep_nelist_exp p b (EBase e) (+[T] & t)
  | LS_ECons : forall p b e es T t Ts ts,
                 lstep_exp p b e (T & t) ->
                 lstep_nelist_exp p b es (Ts & ts) ->
                   lstep_nelist_exp p b (ECons e es) (T +:: Ts & (t, ts)).

Theorem wt_exp_uniqueness :
  forall t l M (MF : MapsTo_fun M),
  forall e p tb A B,
    @wt_exp t l M p tb e A ->
    @wt_exp t l M p tb e B ->
      A = B.
Proof with try econstructor; eauto.
  intros t l M. induction e; intros; invert H; invert H0.
  - eapply NatMapFacts.MapsTo_fun in H5; [|eapply H4]. now subst.
  - depinject H6. now depinject H2.
  - apply IHe with (A := TVal rt) in H8... now invert H8.
  - specialize (MF _ _ _ _ H7 H9). now inject MF. 
Qed.

Theorem wt_exp_soundness :
  forall t l M e p tb b B,
    wt_bctxt tb b ->
    @wt_exp t l M p tb e B ->
      exists r, @lstep_exp t l M p b e (B & r)
with wt_nelist_exp_soundness :
  forall t l M es p tb b FT,
    wt_bctxt tb b ->
    @wt_nelist_exp t l M p tb es FT ->
      exists r, @lstep_nelist_exp t l M p b es (FT & r).
Proof with try eexists; econstructor; eauto.
  - clear wt_exp_soundness. induction e; intros; invert H0.
    + napply H H4; boom; eexists...
    + depinject H5. eexists...
    + eexists...
    + eapply wt_nelist_exp_soundness in H8; boom...
  - clear wt_nelist_exp_soundness. induction es; intros; invert H0.
    + eapply wt_exp_soundness in H4; boom...
    + eapply wt_exp_soundness in H5; boom. eapply IHes in H7; boom...
Qed.

Scheme wt_exp_ind2 := Induction for wt_exp Sort Prop
with wt_nelist_exp_ind2 := Induction for wt_nelist_exp Sort Prop.
Combined Scheme wt_exp_nelist_exp_ind from wt_exp_ind2, wt_nelist_exp_ind2.

Definition eval_correctP t d l F M p tb e B (_ : @wt_exp t l M p tb e B) :=
    forall b r,
    wt_bctxt tb b ->
      @eval t d l F p b B e = Some r <-> @lstep_exp t l M p b e (B & r).

Definition eval_args_correctP t d l F M p tb es FT (_ : @wt_nelist_exp t l M p tb es FT) :=
    forall b r,
    wt_bctxt tb b ->
      @eval_args t d l F p b FT es = Some r <-> @lstep_nelist_exp t l M p b es (FT & r).

Lemma eval_correct :
  forall t d l F M (FMI : find_mapsto_iff F M) (MF: MapsTo_fun M),
  forall e p tb b B r,
    wt_bctxt tb b ->
    @wt_exp t l M p tb e B ->
      @eval t d l F p b B e = Some r <-> @lstep_exp t l M p b e (B & r).
Proof with eauto; cbn.
  intros t d l F M.
  specialize (wt_exp_nelist_exp_ind t l M (eval_correctP t d l F M) (eval_args_correctP t d l F M)); unfold eval_correctP, eval_args_correctP; intros.
  destruct H; split; intros...
  - repeat boom. flip H2. untransfer H3. econstructor...
  - depinvert H2. click H2. unfold transfer_fw. rewrite transfer_refl...
  - repeat boom. untransfer H2. econstructor.
  - depinvert H2... unfold transfer_fw. rewrite transfer_refl...
  - repeat boom... econstructor.
  - depinvert H3... now rewrite eqb_refl.
  - repeat boom; apply FMI in H3; specialize (MF _ _ _ _ m H3);
    depinvert MF; apply H in H4...
    + rewrite transfer_refl... rewrite <- H11; econstructor...
    + rewrite <- H11; econstructor...
  - depinvert H3. apply FMI in H3; rewrite H3...
    rewrite eqb_refl. eapply H in H4... rewrite H4...
    boom. rewrite transfer_refl. rewrite H5...
  - invert H3. eapply H in H5... econstructor...
  - depinvert H3; eapply H in H3...
  - invert H4. repeat boom. inject H9. eapply H in H4... eapply H2 in H5... econstructor...
  - depinvert H4... eapply H in H4... rewrite H4...
    eapply H2 in H5... rewrite H5...
  - eapply H in H3...
  - eapply H in H3...
Qed.

Theorem interpret_correct :
  forall t d l F M (FMI : find_mapsto_iff F M) (MF: MapsTo_fun M),
  forall p I O e i r,
    @wt_exp t l M p (bt_input I) e (TVal O) ->
      @interpret t d l F p I O e i = Some r <-> @lstep_exp t l M p (b_input I i) e (TVal O & r).
Proof with cbn in *; eauto.
  intros; unfold interpret. eapply eval_correct in H...
  unfold wt_bctxt, bt_input, b_input, iff; split; intros;
  repeat boom; apply NatMapFacts.add_mapsto_iff in H0; repeat boom;
  try inversion H1; try eexists; apply NatMapFacts.find_mapsto_iff...
Qed.

(* well-foundedness of DSLs (for finite enumeration) *)
Inductive wf_gconstructor {tid} : forall vt, @dsl tid -> @gconstructor tid vt -> Prop :=
  | WF_B : forall vt d ib,
             wf_gconstructor vt d (B _ ib)
  | WF_C : forall vt d c,
             wf_gconstructor vt d (C _ c)
  | WF_F : forall rt d ft ip irs,
             wf_fraise_id ft d irs ->
               wf_gconstructor rt d (F _ ft ip irs)
  | WF_TBool : forall d,
                 wf_gconstructor TBool d (T _)
  | WF_TPair : forall vt1 vt2 d,
                 wf_gconstructor vt1 d (T _) ->
                 wf_gconstructor vt2 d (T _) ->
                   wf_gconstructor (TPair vt1 vt2) d (T _)

with wf_fraise_id {tid} : forall ft, @dsl tid -> fraiseT rid ft -> Prop :=
  | WF_FBase : forall t d ds ir r,
                 NatMap.MapsTo ir (true, r) d ->
                 wf_grule (DSL d ds) r ->
                   wf_fraise_id +[t] (DSL d ds) ir
  | WF_FCons : forall t ts d ds ir r irs,
                 NatMap.MapsTo ir (true, r) d ->
                 wf_grule (DSL d ds) r ->
                 wf_fraise_id ts (DSL d ds) irs ->
                   wf_fraise_id (t +:: ts) (DSL d ds) (ir, irs)

with wf_grule {tid} : @dsl tid -> @grule tid -> Prop :=
  | WF_R : forall d vt cs,
             wf_nelist_gconstructor vt d cs ->
               wf_grule d (R vt cs)
  | WF_L : forall d ds d' ds' il ib bt rt cs,
             PolyMap_find il ds = Some (DSL d' ds') ->
             NatMap.MapsTo N0 (true, (R rt cs)) d' ->
             (forall ir b r, NatMap.MapsTo ir (b, r) d' -> b = true /\ wf_grule (DSL d' ds') r) ->
               wf_grule (DSL d ds) (L rt ib bt il)

with wf_nelist_gconstructor {tid} : forall vt, @dsl tid -> nelist (@gconstructor tid vt) -> Prop :=
  | WF_RBase : forall vt d c,
                 wf_gconstructor vt d c ->
                   wf_nelist_gconstructor vt d +[c]
  | WF_RCons : forall vt d c cs,
                 wf_gconstructor vt d c ->
                 wf_nelist_gconstructor vt d cs ->
                   wf_nelist_gconstructor vt d (c +:: cs).

(* well-typedness for DSLs *)
Inductive wt_gconstructor {tid lib} {MapsTo : MTT} : forall vt, @dsl tid -> lib -> btctxt -> @gconstructor tid vt -> Prop :=
  | WT_B : forall vt d p b ib,
             NatMap.MapsTo ib vt b ->
               wt_gconstructor vt d p b (B _ ib)
  | WT_C : forall vt d p b c,
             wt_gconstructor vt d p b (C _ c)
  | WT_T : forall vt d p b,
             wt_gconstructor vt d p b (T _)
  | WT_F : forall rt d p b ft ip irs ftb fs bs,
             MapsTo ip (P ft rt ftb fs bs) p ->
             wt_fraise_id ft d p b irs ftb ->
               wt_gconstructor rt d p b (F rt ft ip irs)

with wt_fraise_id {tid lib} {MapsTo : MTT} : forall ft, @dsl tid -> lib -> btctxt -> fraiseT rid ft -> ftbool ft -> Prop :=
  | WT_FBaseR : forall d ds p b ir r vt cs (q : bool) l,
                  r = R vt cs ->
                  NatMap.MapsTo ir (l, r) d ->
                  (if q then wf_grule (DSL d ds) r else True) ->
                    wt_fraise_id +[TVal vt] (DSL d ds) p b ir q      
  | WT_FBaseL : forall d ds p b ir r bt rt ib il (q : bool) l,
                  r = L rt ib bt il ->
                  NatMap.MapsTo ir (l, r) d ->
                  (if q then wf_grule (DSL d ds) r else True) ->
                    wt_fraise_id +[TFun bt rt] (DSL d ds) p b ir q
  | WT_FConsR : forall d ds p b ir r vt cs (q : bool) ft' irs qs l,
                  r = R vt cs ->
                  NatMap.MapsTo ir (l, r) d ->
                  (if q then wf_grule (DSL d ds) r else True) ->
                  wt_fraise_id ft' (DSL d ds) p b irs qs ->
                    wt_fraise_id (TVal vt +:: ft') (DSL d ds) p b (ir, irs) (q, qs)
  | WT_FConsL : forall d ds p b ir r bt rt ib il (q : bool) ft' irs qs l,
                  r = L rt ib bt il ->
                  NatMap.MapsTo ir (l, r) d ->
                  (if q then wf_grule (DSL d ds) r else True) ->
                  wt_fraise_id ft' (DSL d ds) p b irs qs ->
                    wt_fraise_id (TFun bt rt +:: ft') (DSL d ds) p b (ir, irs) (q, qs).

Inductive wt_nelist_gconstructor {tid lib} {MapsTo : MTT} : forall vt, @dsl tid -> lib -> btctxt -> nelist (@gconstructor tid vt) -> Prop :=
  | WT_RBase : forall vt d p b c,
                 @wt_gconstructor tid lib MapsTo vt d p b c ->
                   wt_nelist_gconstructor vt d p b +[c]
  | WT_RCons : forall vt d p b c cs,
                 @wt_gconstructor tid lib MapsTo vt d p b c ->
                 wt_nelist_gconstructor vt d p b cs ->
                   wt_nelist_gconstructor vt d p b (c +:: cs).

Inductive wt_grule {tid lib} {MapsTo : MTT} : @dsl tid -> lib -> btctxt -> @grule tid -> type -> Prop :=
  | WT_R : forall d p b vt cs,
             @wt_nelist_gconstructor tid lib MapsTo vt d p b cs ->
               wt_grule d p b (R vt cs) (TVal vt)
  | WT_L : forall d ds d' ds' p b rt ib bt il cs l,
             PolyMap_find il ds = Some (DSL d' ds') ->
             NatMap.MapsTo N0 (l, (R rt cs)) d' ->
             (forall ir l r, NatMap.MapsTo ir (l, r) d' -> exists t, wt_grule (DSL d' ds') p (NatMap.add ib bt b) r t) ->
               wt_grule (DSL d ds) p b (L rt ib bt il) (TFun bt rt).

Inductive wt_dsl {tid lib} {MapsTo : MTT} : @dsl tid -> lib -> btctxt -> vtype -> Prop :=
  | WT_DSL : forall vt cs p b d ds l,
               NatMap.MapsTo N0 (l, (R vt cs)) d ->
               (forall ir l r, NatMap.MapsTo ir (l, r) d -> exists t, @wt_grule tid lib MapsTo (DSL d ds) p b r t) ->
                 wt_dsl (DSL d ds) p b vt.

Inductive derives_gconstructor {tid} : forall vt, @dsl tid -> @gconstructor tid vt -> @exp tid -> Prop :=
  | D_B : forall vt d ib,
            derives_gconstructor vt d (B _ ib) (EB ib)
  | D_C : forall vt d c,
            derives_gconstructor vt d (C _ c) (EC _ c)
  | D_T : forall vt d c,
            derives_gconstructor vt d (T _) (EC vt c)
  | D_F : forall vt d ft ip irs es,
            derives_fraise_id ft d irs es ->
              derives_gconstructor vt d (F _ ft ip irs) (EF ft ip es)

with derives_fraise_id {tid} : forall ft, @dsl tid -> fraiseT rid ft -> @nelist_exp tid -> Prop :=
  | D_Base : forall d ds e t ir b r,
               NatMap.MapsTo ir (b, r) d ->
               derives_grule (DSL d ds) r e ->
                 derives_fraise_id +[t] (DSL d ds) ir (EBase e)
  | D_Cons : forall d ds e es t ts ir irs b r,
               NatMap.MapsTo ir (b, r) d ->
               derives_grule (DSL d ds) r e ->
               derives_fraise_id ts (DSL d ds) irs es ->
                 derives_fraise_id (t +:: ts) (DSL d ds) (ir, irs) (ECons e es)

with derives_grule {tid} : @dsl tid -> @grule tid -> @exp tid -> Prop :=
  | D_R : forall d vt c cs e,
            NEIn c cs ->
            derives_gconstructor vt d c e ->
              derives_grule d (R vt cs) e
  | D_L : forall d ds d' ds' bt rt ib il b r e,
            PolyMap_find il ds = Some (DSL d' ds') ->
            NatMap.MapsTo N0 (b, r) d' ->
            derives_grule (DSL d' ds') r e ->
              derives_grule (DSL d ds) (L rt ib bt il) (EL ib bt e).

Inductive derives_dsl {tid} : @dsl tid -> @exp tid -> Prop :=
  | D_DSL : forall d ds b r e,
              NatMap.MapsTo N0 (b, r) d ->
              derives_grule (DSL d ds) r e ->
                derives_dsl (DSL d ds) e.

Lemma wt_nelist_gconstructor_NEIn :
  forall ti l M,
  forall vt d p b c cs,
    @wt_nelist_gconstructor ti l M vt d p b cs ->
    NEIn c cs ->
      @wt_gconstructor ti l M vt d p b c.
Proof.
Admitted.

Fixpoint wt_gconstructor_sound {ti l M} e {struct e} :
  forall o vt d p b c,
    @wt_dsl ti l M d p b o ->
    @wt_gconstructor ti l M vt d p b c ->
    derives_gconstructor vt d c e ->
      @wt_exp ti l M p b e (TVal vt)
with wt_fraise_id_sound {ti l M} es {struct es} :
  forall ft d p b irs ftb o,
    @wt_dsl ti l M d p b o ->
    @wt_fraise_id ti l M ft d p b irs ftb ->
    derives_fraise_id ft d irs es ->
      @wt_nelist_exp ti l M p b es ft
with wt_grule_sound {ti l M} e {struct e} :
  forall d p b r t o,
    @wt_dsl ti l M d p b o ->
    @wt_grule ti l M d p b r t ->
    derives_grule d r e ->
      @wt_exp ti l M p b e t.
Proof with eauto; subst; cbn.
  - clear wt_gconstructor_sound. intros. depinvert H0. depinvert H1.
    + constructor...
    + depinvert H1. constructor...
    + depinvert H1. constructor...
    + depinvert H2. eapply wt_fraise_id_sound in H1... econstructor...
  - clear wt_fraise_id_sound. intros ft. revert es. induction ft; intros; do 2 depinvert H0;
    invert H; eapply NatMapFacts.MapsTo_fun in H1...
    1-2: inject H1; napply H10 H0; boom; napply wt_grule_sound H4; eauto; invert H4; constructor...
    1-2: inject H1; napply H12 H0; boom; napply wt_grule_sound H6; eauto; depinvert H6; eapply IHft in H3; eauto; constructor...
  - clear wt_grule_sound; intros. depinvert H0.
    + depinvert H1. eapply wt_nelist_gconstructor_NEIn in H1...
    + depinvert H3. rewrite H0 in H3. inject H3.
      constructor. eapply NatMapFacts.MapsTo_fun in H1...
      depinvert H1... depinvert H5. napply H2 H4; boom. depinvert H5.
      eapply wt_nelist_gconstructor_NEIn in H5...
      eapply wt_gconstructor_sound with (o := rt) in H5...
      econstructor...
Admitted.

Lemma wt_dsl_sound :
forall ti l M,
forall d p b o e,
  @wt_dsl ti l M d p b o ->
  derives_dsl d e ->
    @wt_exp ti l M p b e (TVal o).
Proof with eauto; subst; cbn.
  intros. invert H. invert H0. napply NatMapFacts.MapsTo_fun H1...
  apply H2 in H1; boom. invert H1. inject H3. depinject H11. eapply wt_grule_sound in H1...
Qed.

Definition stid := id.
Definition sexp := @exp stid.
Definition nelist_sexp := @nelist_exp stid.
Definition scorpus := @corpus stid.
Definition straise_fw := traise_fw sexp.
Definition sfraise_fw := fraise straise_fw.
Definition slib := IdentMap.t prim.
Definition slib_empty : slib := IdentMap.empty _.
Definition sMapsTo := @IdentMap.MapsTo prim.
Definition sfind := @IdentMap.find prim.
Definition sMapsTo_fun := @IdentMapFacts.MapsTo_fun prim.
Definition sfind_mapsto_iff := @IdentMapFacts.find_mapsto_iff prim.
Definition sdsl := @dsl stid.
Definition srule := @grule stid.
Definition sconstructor := @gconstructor stid.
Definition sdsl_empty : sdsl := DSL (NatMap.empty (bool * srule)) PolyMap_empty.

Definition tc_scorpus : slib -> scorpus -> bool :=
  @tc_corpus stid _ slib sfind.
Definition wt_scorpus : slib -> scorpus -> Prop :=
  @wt_corpus stid slib sMapsTo.

Definition ttid := pid.
(* Definition texp := @exp ttid. *)
Definition nelist_texp := @nelist_exp ttid.
Definition ttraise_fw := traise_fw texp.
Definition tfraise_fw := fraise ttraise_fw.
Definition tlib := NatMap.t prim.
Definition tlib_empty : tlib := NatMap.empty _.
Definition tMapsTo := @NatMap.MapsTo prim.
Definition tfind := @NatMap.find prim.
Definition tMapsTo_fun := @NatMapFacts.MapsTo_fun prim.
Definition tfind_mapsto_iff := @NatMapFacts.find_mapsto_iff prim.
Definition tdsl := @dsl ttid.
Definition trule := @grule ttid.
Definition tconstructor := @gconstructor ttid.
Definition tdsl_empty : tdsl := DSL (NatMap.empty (bool * trule)) PolyMap_empty.

Definition embed_c {vt} (n : rid) (m : lid) (b : bool) (c : sconstructor vt) (d : sdsl) : rid * sdsl * N * N:=
  let 'DSL d' ds' := d in
  (n, DSL (NatMap.add n (b, (R vt +[c])) d') ds', N.succ n, m).

Fixpoint embed_t (p : slib) (e : sexp) (t : type) (d : sdsl) (n : rid) (m : lid) (b : bool) {struct e} : option (rid * sdsl * rid * lid) :=
  match e with
  | EB ib => match t with
             | TVal vt => Some (embed_c n m b (B vt ib) d)
             | _ => None
             end
  | EC vt c => Some (embed_c n m b (C vt c) d)
  | EL ib bt e' => match t with
                  | TFun bt' rt =>
                      let 'DSL d' ds' := d in
                      do ret <- embed_t p e' (TVal rt) (sdsl_empty) N0 N0 b;
                      let '(_, d'', _, _) := ret in
                      Some (n, DSL (NatMap.add n (b, (L rt ib bt m)) d') (PolyMap_add m d'' ds'), N.succ n, N.succ m)
                  | _ => None
                  end
  | EF ft ip es => match t with
                  | TVal vt =>
                      do pr <- IdentMap.find ip p;
                      let '(P ft' _ ftb' _ _):= pr in
                      do ftb <- transfer ftbool ft' ft ftb';
                      do ret <- embed_nes p es ft d n m b ftb;
                      let '(irs, d', n', m') := ret in
                      Some (embed_c n' m' b (F vt ft ip irs) d')
                  | _ => None
                  end
  end
with embed_nes (p : slib) (nes : nelist_sexp) (ft : ftype) (d : sdsl) (n : rid) (m : lid) (b : bool) (ftb : ftbool ft) {struct nes} : option (fraiseT rid ft * sdsl * N * N).
  fork ft.
  - destruct nes; [apply (embed_t p e t d n m (b || ftb)) | apply None].
  - destruct nes; cbn in ftb; scatter; [apply None | forkL (embed_t p e t d n m (b || b0)); scatter].
    forkL (embed_nes p nes f s r l b f0); scatter; cbn.
    apply (Some ((r0, f1), s0, n1, n0)).
Defined.

Fixpoint embed_vt (p : slib) (e : sexp) (vt : vtype) (d : sdsl) (n : rid) (m : lid) : option (sconstructor vt * sdsl * rid * lid) :=
  match e with
  | EB ib => Some ((B vt ib), d, n, m)
  | EC vt' c => do c' <- vtransfer vt' vt c;
                Some ((C vt c'), d, n, m)
  | EF ft ip es => do pr <- IdentMap.find ip p;
                   let '(P ft' _ ftb' _ _):= pr in
                   do ftb <- transfer ftbool ft' ft ftb';
                   do ret <- embed_nes p es ft d n m false ftb;
                   let '(irs, d', n', m') := ret in
                   Some ((F vt ft ip irs), d', n', m')
  | _ => None
  end.

Fixpoint embed_es (p : slib) (es : nelist sexp) (vt : vtype) (d : sdsl) (n : rid) (m : lid) : option (nelist (sconstructor vt) * sdsl) :=
  match es with
  | +[e] => do ret <- (embed_vt p e vt d n m);
            let '(c, d', _, _) := ret in
            Some (+[c], d')
  | e +:: es' => do ret <- embed_vt p e vt d n m;
                 let '(c, d', n', m') := ret in
                 do ret' <- embed_es p es' vt d' n' m';
                 let '(cs, d'') := ret' in
                 Some (c +:: cs, d'')
  end.

Definition embed (p : slib) (c : scorpus) : option sdsl :=
  let '(i, o, es) := c in
  do ret <- embed_es p es o (sdsl_empty) (N.pos 1) N0;
  let '(cs, (DSL d ds)) := ret in
  Some (DSL (NatMap.add N0 (false, (R o cs)) d) ds).

Definition mangler := IdentMap.t pid.
Definition mangle (i : id) (p : prim) (mtn : mangler * tlib * N) : mangler * tlib * N :=
  let '(m, tp, n) := mtn in
  let mn := N.succ n in
  let n' := N.succ mn in
  (IdentMap.add i n m, NatMap.add mn p (NatMap.add n p tp), n').

Definition semantify_c (m : mangler) (tp : tlib) (b : bool) vt (c : sconstructor vt) : tconstructor vt :=
  match c with
  | B _ ib => B _ ib
  | C _ c => C _ c
  | T _ => T _
  | F _ ft i irs => match IdentMap.find i m with
                    | Some ip => let nip := if b then N.succ ip else ip in
                                 F _ ft nip irs
                    | None => T _
                    end
  end. 

Definition semantify_r (m : mangler) (tp : tlib) (ir : rid) (br : bool * srule) (td : rid_ctxt (bool * srule)) : rid_ctxt (bool * srule) :=
  let (b, r) := br in
  match r with
  | R vt cs => NatMap.add ir (b, R vt (nemap (semantify_c m tp b vt) cs)) td
  | L rt ib bt il => NatMap.add ir br td
  end.

Fixpoint dslmap {A B} (f : rid_ctxt (bool * @grule A) -> rid_ctxt (bool * @grule B)) (d : @dsl A) : @dsl B :=
  let (d', ds') := d in
  DSL (f d') (map (fun (kv : lid * @dsl A) => let (k, v) := kv in (k, dslmap f v)) ds').

Definition semantify_d (m : mangler) (tp : tlib) (d : rid_ctxt (bool * srule)) : rid_ctxt (bool * trule) :=
  NatMap.fold (semantify_r m tp) d (NatMap.empty _).

Definition semantify (sp : slib) (sd : sdsl) : tlib * tdsl :=
  let '(m, tp, n) := IdentMap.fold mangle sp (IdentMap.empty _, tlib_empty, N0) in
  (tp, dslmap (semantify_d m tp) sd).

Definition Pinfo := pid_ctxt {ft & fraiseT rid ft}.

Fixpoint build_Pentry' (ft : ftype) (n : rid) : fraiseT rid ft * rid.
  destruct ft.
  - apply (N.succ n, N.succ n).
  - remember (build_Pentry' ft (N.succ n)); scatter.
    apply ((N.succ n, f), r).
Defined.

Definition build_Pentry (ip : pid) (p : prim) (infn : Pinfo * rid) : Pinfo * rid :=
  let (inf, n) := infn in
  let 'P ft rt ftb fs bs := p in
  let (irs, n') := build_Pentry' ft n in
  (NatMap.add ip (ft & irs) inf, n').

Definition next_rid {A} (d : rid_ctxt A) : rid :=
  N.succ (NatMap.fold (fun ir _ m => if N.ltb m ir then ir else m) d N0).

Fixpoint build_Pinfo (tp : tlib) (n : rid) : Pinfo * rid :=
  NatMap.fold build_Pentry tp ((NatMap.empty _), n).

(*Definition Finfo := pid_ctxt {ft & fraiseT (nelist tconstructor) ft}.
Definition Linfo := rid_ctxt (nelist lid).*)

Definition generalize_r (ir : rid) (br : bool * trule) : rid_ctxt (bool * trule). Admitted.
Definition generalize_d (d : rid_ctxt (bool * trule)) : rid_ctxt (bool * trule). Admitted.

Definition generalize (tp : tlib) (td : tdsl) : tdsl :=
  dslmap generalize_d td.

Definition VERSE (sp : slib) (c : scorpus) : option tdsl :=
  if tc_scorpus sp c
  then do sd <- embed sp c;
       let '(tp, td) := semantify sp sd in
       let td' := generalize tp td in
       Some td'
  else None.

Definition appendFT : ftype := +[TVal TStr; TVal TStr].
Definition appendRT : vtype := TStr.
Definition appendFTB : ftbool appendFT := (true, false).
Definition fappend : fsem appendFT appendRT := fun tid oss =>
  match oss with
  | (Some s1, Some s2) => Some (append s1 s2)
  | (_, _) => None
  end.

Fixpoint range (n : nat) : list nat :=
  match n with
  | 0 => [0]
  | S n' => n :: (range n')
  end.
  
Definition bappend : bsem appendFT appendRT appendFTB := fun s f =>
  let len := String.length s in
  map (fun n => (Some (String.substring 0 n s), Some (String.substring n (len-n) s))) (range len).
  
Definition pappend := P appendFT appendRT appendFTB fappend bappend.

Definition appendlib : slib := (IdentMap.add (N.pos 1) pappend (IdentMap.add N0 pappend slib_empty)).
Definition prog1a : sexp := EC TStr "foo"%string.
Definition prog1b : sexp := EC TStr "bar"%string.
Definition prog2a : sexp := EF appendFT (N.pos 1) (ECons (EB N0) (EBase prog1a)).
Definition prog2b : sexp := EF appendFT N0 (ECons (EB N0) (EBase prog1b)).
Definition prog3 : sexp := EF appendFT (N.pos 1) (ECons prog2a (EBase prog2b)).
Definition appendcorp : scorpus := (TStr, TStr, +[ prog1a; prog1b; prog2a; prog2b; prog3 ]).

Definition elms {tid} (od : option (@dsl tid)) := do d <- od; let 'DSL d' ds' := d in Some (NatMap.elements d').

Eval vm_compute in elms (VERSE appendlib appendcorp).



(* -------------------------- BELOW THIS POINT, THE CODE IS BROKEN -------------------------- *)
(* see the file `synthesis.v` for an older version where the type definitions were compatible *)



(* vsa constructor for a particular value of type vt
     in the sum type vid + rid, vid represents a fixed value input spec
     and rid represents an unconstrained input spec following a tdsl rule *)
Inductive vconstructor (vt : vtype) := 
  | VB : bid -> vconstructor vt
  | VC : vraise vt -> vconstructor vt
  | VF ft : pid -> list (fraiseT (vid + rid) ft) -> vconstructor vt.

(* vsa rule for a particular value of type vt 
     or a function on a particular set of examples *)
Inductive vrule :=
  | VR (vt : vtype) : list (vconstructor vt) -> vrule
  | VL (rt : vtype) : bid -> vtype -> sid -> vrule
  | VU : vrule (* unspecified (in queue) *).

(* entry in the map relating rids+values in the dsl grammar
     to rules in the vsa *)
Inductive map_entry :=
  | MR (vt : vtype) : PolyMap (vraise vt) vid _ -> map_entry
  | ML (bt rt : vtype) : PolyMap (examples bt rt) vid _ -> map_entry.

(* mapping to locate rules in the vsa corresponding to
     rules * values in the dsl grammar *)
Inductive mapping :=
| MPG : rid_ctxt map_entry -> PolyMap lid mapping _ -> mapping.

(*
Definition mapping_empty (d : tdsl) : mapping :=
  let 'DSL d' ds := d in
  NatMap.fold (fun i (r : trule) m => NatMap.add i
    match r with
    | R vt _ => MR vt PolyMap_empty
    | L rt x bt ir => ML bt rt PolyMap_empty 
    end m)
    d' (NatMap.empty _).
*)

(* an entry in the BFS queue
   in QR, the rid and vraise vt represent a rule in the dsl grammar outputting a particular value
   in QL, the vid represents a rule in the vsa with a stream to destruct *)
Inductive qentry :=
  | QR (vt : vtype) : rid -> vraise vt -> vid -> qentry
  | QL0 (bt rt : vtype) : rid -> examples bt rt -> vid -> qentry
  | QLn : sid -> qentry.

Definition queue := list qentry.

(* version space algebra (concise representation of synthesizable program set)
   has the shape: VSA vrs niv nis ss
     vrs is a collection of vrules
     ss is a collection of states for recursive synthesis of functions
     niv is the next fresh vid for vrs
     nis is the next fresh sid for ss *)
Inductive vsa :=
| VSA : vid_ctxt vrule -> PolyMap sid (nelist (bctxt * (vsa * mapping * queue))) _ -> vid -> sid -> vsa.

(* unified version space algebra *)
Inductive ivsa :=
| IVSA : vid_ctxt vrule -> PolyMap sid ivsa _ -> ivsa.

Definition vsa_empty (d : tdsl) := VSA (NatMap.add N0 VU (NatMap.empty _)) (PolyMap_empty) (N.pos 1) N0.

Inductive pspace :=
  | PS : vid_ctxt (PolySet texp _) -> PolyMap sid pspace _ -> pspace.

Fixpoint pspace_empty (u : ivsa) : pspace :=
  let '(IVSA vd ss) := u in
  PS (NatMap.fold (fun iv r s => NatMap.add iv PolySet_empty s) vd (NatMap.empty _))
     (map (fun (iu : sid * ivsa) => let (i, u) := iu in (i, pspace_empty u)) ss).

Fixpoint enumerate_tconstructor
  vt (p : tlib) (b : bctxt) (d : tdsl) (c : tconstructor vt) (rs : NatSet.t) : option (PolySet (option (vraise vt)) _ * NatSet.t)
with enumerate_fraise_id
  ft (p : tlib) (b : bctxt) (d : tdsl) (irs : fraiseT rid ft) (rs : NatSet.t) : option (PolySet (fraise_fwt ft) _ * NatSet.t)
with enumerate_trule
  t (p : tlib) (b : bctxt) (d : tdsl) (r : trule) (rs : NatSet.t) : option (PolySet (option (traise_fwt t)) _ * NatSet.t)
with enumerate_tconslist
  vt (p : tlib) (b : bctxt) (d : tdsl) (cs : nelist (tconstructor vt)) (rs : NatSet.t) : option (PolySet (option (vraise vt)) _ * NatSet.t).
Proof.
  - fork c.
    + forkL (NatMap.find b0 b); scatter.
      equate x vt. ret ([Some v], rs).
    + ret ([Some v], rs).
    + fork vt.
      * ret ([Some true; Some false], rs).
      * apply None.
      * apply None.
      * apply None.
      * forkL (enumerate_tconstructor v1 p b d (T _) rs).
        forkL (enumerate_tconstructor v2 p b d (T _) rs).
        scatter. ret (PolySet_option_prod p0 p1, rs).
      * apply None.
    + apply None. (* TODO *)
  - fork ft.
    + forkL (NatMap.find irs d).
      apply (enumerate_trule t p b d g (NatSet.add irs rs)).
    + cbn in *. scatter.
      forkL (NatMap.find r d).
      forkL (enumerate_trule t p b d g (NatSet.add r rs)); scatter.
      forkL (enumerate_fraise_id f p b d f0 t0); scatter.
      ret (PolySet_prod p0 p1, t1).
  - forkL r. forkL t.
    equate v vt.
    apply (enumerate_tconslist vt p b d n rs).
  - fork cs.
    + apply (enumerate_tconstructor vt p b d t rs).
    + forkL (enumerate_tconstructor vt p b d t rs); scatter.
      forkL (enumerate_tconslist vt p b d n t0); scatter.
      ret (PolySet_union p0 p1, t1).
Admitted. (* TODO fix well-foundedness OR (more likely) only allow direct B/C enumeration *)

Definition enumerate t p b d ir : option (PolySet (option (traise_fwt t)) _) :=
  do r <- NatMap.find ir d;
  do srs <- enumerate_trule t p b d r (NatSet.add ir NatSet.empty);
  Some (fst srs).

Fixpoint enumerate_rids (b : bctxt) (p : plib) (d : tdsl) (ft : ftype) ftb (irs : fraiseT rid ft) {struct ft} : list (fraiseb ft ftb).
Proof.
  destruct ft.
  - destruct ftb; cbn in *.
    + destruct (enumerate t p b d irs).
      * apply p0.
      * apply ([]).
    + apply ([tt]).
  - cbn in *; scatter. destruct b0.
    + destruct (enumerate t p b d r).
      * pose proof (enumerate_rids b p d ft f0 f).
        apply (list_prod p0 X).
      * apply ([]).
    + pose proof (enumerate_rids b p d ft f0 f).
      apply (list_prod [tt] X).
Defined.

Fixpoint backpropFm {ft rt ftb} (o : vraise rt) (bs : bsem ft rt ftb) (xs : list (fraiseb ft ftb)) : list (fraise_bw ft) :=
  match xs with
  | [] => []
  | x :: xs' => let is := bs o x in
                (bs o x) ++ (backpropFm o bs xs')
  end.

Definition backpropFv'' {t} (oi : option (traise_bw t)) (ir : rid) (v : vsa) (m : mapping) : option ((vid + rid) * (vsa * mapping * queue)) :=
  match oi with
  | Some i => let '(VSA vd ss niv nis) := v in
              do me <- NatMap.find ir m;
              match me with
              | MR vt pm => do i' <- transfer_bw t (TVal vt) i;
                            match PolyMap_find i' pm with
                            | Some iv => Some (inl iv, (v, m, []))
                            | None => Some (inl niv,
                                        (VSA (NatMap.add niv VU vd) ss (N.succ niv) nis,
                                        NatMap.add ir (MR vt (PolyMap_add i' niv pm)) m,
                                        [QR vt ir i' niv]))
                            end
              | ML bt rt pm => do i' <- transfer_bw t (TFun bt rt) i;
                               match PolyMap_find i' pm with
                               | Some iv => Some (inl iv, (v, m, []))
                               | None => Some (inl niv,
                                           (VSA (NatMap.add niv VU vd) ss (N.succ niv) nis,
                                           NatMap.add ir (ML bt rt (PolyMap_add i' niv pm)) m,
                                           [QL0 bt rt ir i' niv]))
                               end
              end
  | None => Some (inr ir, (v, m, []))
  end.

Fixpoint backpropFv' ft (i : fraise_bw ft) (irs : fraiseT rid ft) (v : vsa) (m : mapping) : option (fraiseT (vid + rid) ft * (vsa * mapping * queue)).
Proof.
  fork ft.
  - apply (backpropFv'' i irs v m).
  - cbn in *. scatter.
    destruct (backpropFv'' o r v m); [scatter | apply None].
    destruct (backpropFv' n f0 f v0 m0); [scatter | apply None].
    apply (Some ((s, f1), (v1, m1, q ++ q0))).
Defined.

Fixpoint backpropFv ft (is : list (fraise_bw ft)) (irs : fraiseT rid ft) (v : vsa) (m : mapping) : option (list (fraiseT (vid + rid) ft) * (vsa * mapping * queue)) :=
  match is with
  | [] => Some ([], (v, m, []))
  | i :: is' => do tvmq <- backpropFv' ft i irs v m;
                let '(t, (v', m', q')) := tvmq in
                do tsvmq <- backpropFv ft is' irs v' m';
                let '(ts, (v'', m'', q'')):= tsvmq in
                Some (t :: ts, (v'', m'', q' ++ q''))
  end.

Definition backpropF' (b : bctxt) (p : plib) (d : tdsl) {ft rt ftb} (o : vraise rt) (bs : bsem ft rt ftb) (irs : fraiseT rid ft) (v : vsa) (m : mapping) : option (list (fraiseT (vid + rid) ft) * (vsa * mapping * queue)) :=
  let xs := enumerate_rids b p d ft ftb irs in
  let is := backpropFm o bs xs in
  backpropFv ft is irs v m.

Definition backpropF (b : bctxt) (p : plib) (d : tdsl) (pr : prim) {O} (o : vraise O) {FT} (irs : fraiseT rid FT) (v : vsa) (m : mapping) : option (list (fraiseT (vid + rid) FT) * (vsa * mapping * queue)).
Proof.
  destruct pr. equate FT ft. equate O rt.
  apply (backpropF' b p d o b0 irs v m).
Defined.

Definition backprop (b : bctxt) (p : plib) (d : tdsl) (m : mapping) {O} (o : vraise O) (v : vsa) (c : tconstructor O) : option (list (vconstructor O) * (vsa * mapping * queue)) :=
  match c with
  | B _ ib => do q <- NatMap.find ib b;         (* the bound id must be in scope *)
              let (T, t) := q in
              do t' <- vtransfer T O t;         (* check well-typedness *)
              if eqb t' o                       (* the bound value must match the output *)
              then Some ([VB _ ib], (v, m, []))
              else Some ([], (v, m, []))
  | C _ c => if eqb c o                         (* the constant value must match the output *)
             then Some ([VC _ o], (v, m, []))
             else Some ([], (v, m, []))
  | T _ => Some ([VC _ o], (v, m, []))          (* use the constant that matches the output *)
  | F _ ft ip irs => do pr <- NatMap.find ip p;
                     do ret <- backpropF b p d pr o irs v m;
                     let '(ivrs, vmq) := ret in
                     Some ([VF _ ft ip ivrs], vmq)
  end.

Fixpoint backprops' (b : bctxt) (p : plib) (d : tdsl) (m : mapping) {O} (o : vraise O) (v : vsa) (cs : @nelist (tconstructor O)) : option (list (vconstructor O) * (vsa * mapping * queue)) :=
  match cs with
  | +[c] => backprop b p d m o v c
  | c +:: cs => do cvmq' <- backprop b p d m o v c;
                 let '(c', (v', m', q')) := cvmq' in
                 do cvmqs' <- backprops' b p d m' o v' cs;
                 let '(cs', (v'', m'', q'')) := cvmqs' in
                 Some (c' ++ cs', (v'', m'', q' ++ q''))
  end.

Fixpoint backprops (b : bctxt) (p : plib) (d : tdsl) (m : mapping) {O} (o : vraise O) (v : vsa) (cs : @nelist (tconstructor O)) (iv : vid): option (vsa * mapping * queue) :=
  do cvmqs' <- backprops' b p d m o v cs;
  let '(cs', (v', m', q')) := cvmqs' in
  let '(VSA vd ss niv nis) := v' in
  Some (VSA (NatMap.add iv (VR O cs') vd) ss niv nis, m', q').

Definition vsa_handle_QR (p : plib) (b : bctxt) (d : tdsl) (m : mapping) (v : vsa) (vt : vtype) (ir : rid) (o : vraise vt) (iv : vid) : option (vsa * mapping * queue) :=
  do r <- NatMap.find ir d;
  match r with
  | R rvt cs => 
      do ro <- vtransfer vt rvt o;
      backprops b p d m ro v cs iv
  | _ => None
  end.

Definition build_state (b : bctxt) (I O : vtype) (ib : bid) (ir : rid) (v : vsa) (m : mapping) (io : vraise I * vraise O) : bctxt * (vsa * mapping * queue) :=
  let (i, o) := io in
  (NatMap.add ib (I & i) b, (v, m, [QR O ir o N0])).

Definition build_states (b : bctxt) (d : tdsl) (bt rt : vtype) (ib : bid) (ir : rid) (ios : examples bt rt) : nelist (bctxt * (vsa * mapping * queue)) :=
  let ev := vsa_empty d in
  let em := mapping_empty d in
  nemap (build_state b bt rt ib ir ev em) ios.

Definition vsa_handle_QL0 (p : plib) (b : bctxt) (d : tdsl) (m : mapping) (v : vsa) (bt rt : vtype) (ib : bid) (ir : rid) (ios : examples bt rt) (iv : vid) : vsa * mapping * queue :=
  let '(VSA vd ss niv nis) := v in
  let ns := build_states b d bt rt ib ir ios in
  let nv := VSA (NatMap.add iv (VL rt ib bt nis) vd) (PolyMap_add nis ns ss) niv (N.succ nis) in
  let nq := [QLn nis] in
  (nv, m, nq).

Fixpoint QLn_done (l : nelist (bctxt * (vsa * mapping * queue))) : bool :=
  let empty x := match x with (_, (_, _, [])) => true | _ => false end in 
  match l with
  | +[x] => empty x
  | x +:: xs => empty x && QLn_done xs
  end.

Inductive step_args :=
  | step_state (p : plib) (d : tdsl) (s : bctxt * (vsa * mapping * queue))
  | nemap_option_step_state (p : plib) (d : tdsl) (s : nelist (bctxt * (vsa * mapping * queue)))
  | vsa_handle_qentry (p : plib) (b : bctxt) (d : tdsl) (m : mapping) (x : qentry) (ov nv : vsa)
  | step (ov nv : vsa) (m : mapping) (q : queue) (p : plib) (b : bctxt) (d : tdsl).

Definition count_s' (cv : vsa -> nat) (s : (bctxt * (vsa * mapping * queue))) : nat :=
  let '(_, (v, _, q)) := s in 1 + cv v + length q.

Definition count_ss' (cv : vsa -> nat) (s : nelist (bctxt * (vsa * mapping * queue))) n :=
  1 + nefold _ _ (fun cum bvmq => cum + count_s' cv bvmq) s n.

Fixpoint count_v (v : vsa) : nat :=
  let '(VSA _ ss _ _) := v in
  fold_left (fun cum s => 1 +
    match s with
    | (k, bvmqs) => count_ss' count_v bvmqs cum
    end) ss 0.

Definition count_ss := count_ss' count_v.
Definition count_s := count_s' count_v.

Fixpoint count_step (args : step_args) : nat :=
  match args with
  | step_state p d s => count_s s
  | nemap_option_step_state p d s => count_ss s 0
  | vsa_handle_qentry p b d m x ov nv => count_v ov
  | step ov nv m q p b d => count_v ov + length q
  end.

Lemma count_ss_0_exp :
  forall s n,
    nefold _ _ (fun cum bvmq => cum + count_s' count_v bvmq) s n = n + nefold _ _ (fun cum bvmq => cum + count_s' count_v bvmq) s 0.
Proof.
  induction s; intros; cbn in *; try omega.
  pose proof IHs. specialize (H (n + count_s' count_v a)). rewrite H.
  specialize (IHs (count_s' count_v a)). omega.
Qed.

Lemma count_ss_0 :
  forall s n,
    count_ss s n = n + count_ss s 0.
Proof. cbn; intros. rewrite count_ss_0_exp. omega. Qed.

Lemma count_ss_preserves :
  forall s n,
    n < count_ss s n.
Proof. intros; rewrite count_ss_0. cbn. omega. Qed.

Lemma count_v_0 :
  forall ss n,
    fold_left (fun (cum : nat) (s : sid * nelist (bctxt * (vsa * mapping * queue))) => 1 + (let (_, bvmqs) := s in count_ss' count_v bvmqs cum)) ss n =
    n + fold_left (fun (cum : nat) (s : sid * nelist (bctxt * (vsa * mapping * queue))) => 1 + (let (_, bvmqs) := s in count_ss' count_v bvmqs cum)) ss 0.
Proof.
  induction ss; intros; cbn in *; auto.
  remember ((fun cum (s : sid * nelist (bctxt * (vsa * mapping * queue))) =>
  S (let (_, bvmqs) := s in S (nefold nat (bctxt * (vsa * mapping * queue))
  (fun (cum0 : nat) bvmq => cum0 + count_s' count_v bvmq) bvmqs cum)))) as foo.
  remember ((S (let (_, bvmqs) := a in S (nefold nat (bctxt * (vsa * mapping * queue))
  (fun cum bvmq => cum + count_s' count_v bvmq) bvmqs n)))) as bar.
  remember ((S (let (_, bvmqs) := a in S (nefold nat (bctxt * (vsa * mapping * queue))
  (fun cum bvmq => cum + count_s' count_v bvmq) bvmqs 0)))) as bar2.
  destruct a. rewrite count_ss_0_exp in Heqbar.
  assert (bar = n + bar2) by omega. rewrite H.
  rewrite IHss. rewrite IHss with (n := bar2). omega.
Qed.

Lemma count_v_v_Cons :
  forall ss vd a niv nis,
    count_v (VSA vd ss niv nis) < count_v (VSA vd (a :: ss) niv nis).
Proof.
  intros; unfold count_v; fold count_v. assert (a :: ss = [a] ++ ss) by auto. rewrite H.
  rewrite fold_left_app. rewrite count_v_0 with (n := (fold_left
  (fun (cum : nat) (s : sid * nelist (bctxt * (vsa * mapping * queue))) =>
   1 + (let (_, bvmqs) := s in count_ss' count_v bvmqs cum)) [a] 0)). cbn. omega.
Qed.

Lemma count_ss_v_Cons :
  forall vd is s ss niv nis,
    count_ss s 0 < count_v (VSA vd ((is, s) :: ss) niv nis).
Proof.
  intros. unfold count_v. fold count_v.
  assert ((is, s) :: ss = [(is, s)] ++ ss) by auto. rewrite H.
  rewrite fold_left_app. rewrite count_v_0. cbn. omega.
Qed.

Lemma count_ss_v :
  forall ss is s vd niv nis,
    In (is, s) ss ->
      count_ss s 0 < count_v (VSA vd ss niv nis).
Proof.
  induction ss; intros. inversion H.
  cbn in H. destruct H.
  - subst. apply count_ss_v_Cons.
  - specialize (IHss is s vd niv nis H).
    specialize (count_v_v_Cons ss vd a niv nis).
    omega.
Qed.

Definition step_ret (fn : step_args) :=
  match fn with
  | step_state _ _ _ => option (bctxt * (vsa * mapping * queue))
  | nemap_option_step_state _ _ _ => option (nelist (bctxt * (vsa * mapping * queue)))
  | vsa_handle_qentry _ _ _ _ _ _ _ => option (vsa * mapping * queue)
  | step _ _ _ _ _ _ _ => option (vsa * mapping * queue)
  end.

Program Fixpoint mut_rec_step (args : step_args) {measure (count_step args)} : step_ret args :=
  match args with
  | step_state p d s => 
      let '(b, (v, m, q)) := s in
      do ret <- mut_rec_step (step v v m q p b d);
      Some (b, ret)
  | nemap_option_step_state p d s =>
      match s with
      | +[x] => do nx <- mut_rec_step (step_state p d x);
                Some +[nx]
      | x +:: xs => do nx <- mut_rec_step (step_state p d x);
                    do nxs <- mut_rec_step (nemap_option_step_state p d xs);
                    Some (nx +:: nxs)
      end
  | vsa_handle_qentry p b d m x ov nv =>
      match x with
      | QR vt ir o iv =>
          vsa_handle_QR p b d m nv vt ir o iv
      | QL0 bt rt ir ios iv =>
          do r <- NatMap.find ir d;
          match r with
          | L _ ib _ ir' => Some (vsa_handle_QL0 p b d m nv bt rt ib ir' ios iv)
          | _ => None
          end
      | QLn is =>
          let '(VSA _ ss _ _) := ov in
          let '(VSA vd ss' niv nis) := nv in
          do spf <- PolyMap_find_pf is ss;
          let (s, _) := spf in
          do ns <- mut_rec_step (nemap_option_step_state p d s);
          let nq := if QLn_done ns then [] else [QLn is] in
          Some ((VSA vd (PolyMap_add is ns ss') niv nis), m, nq)
      end
  | step ov nv m q p b d =>
      match q with
      | [] => Some (nv, m, [])
      | x :: xs => do vmq' <- mut_rec_step (vsa_handle_qentry p b d m x ov nv);
                  let '(v', m', q') := vmq' in
                  do vmq'' <- mut_rec_step (step ov v' m' xs p b d);
                  let '(v'', m'', q'') := vmq'' in
                  Some (v'', m'', q' ++ q'')
      end
  end.
Next Obligation. cbn; apply count_ss_preserves. Defined.
Next Obligation. cbn. rewrite count_ss_0_exp with (n := S (count_v v0 + Datatypes.length q0)). omega. Defined.
Next Obligation. apply PolyMap_find_impl_In in H. eapply count_ss_v; eauto. Defined.
Next Obligation. cbn; omega. Defined.
Next Obligation. cbn; omega. Defined.

Fixpoint unify2 (v1 v2 : vsa) : option vsa := Some v1.

Fixpoint unify' (v : vsa) (vs : nelist vsa) : option vsa :=
  match vs with
  | +[v'] => unify2 v v'
  | v' +:: vs' => do uv <- unify2 v v';
                  unify' uv vs'
  end.

Fixpoint unify (vs : nelist vsa) : option vsa :=
  match vs with
  | +[v] => Some v
  | v +:: vs' => unify' v vs'
  end.

(* do n levels of enumeration, or stop early if the entire space has been explored *)
Fixpoint synthesize'' n vmq p b d : option (vsa * mapping * queue) :=
  let '(v, m, q) := vmq in
  match q with
  | [] => Some vmq
  | x :: xs => match n with
               | 0 => Some vmq
               | S n' => do vmq' <- mut_rec_step (step v v m q p b d);
                         synthesize'' n' vmq' p b d
               end
  end.

Fixpoint synthesize' (n : nat) (p : plib) (d : tdsl) {I O} (ios : examples I O) : option (nelist (vsa * mapping * queue)) :=
  let nv := vsa_empty d in
  let nm := mapping_empty d in
  let nq o := [QR O N0 o N0] in
  let nb i := NatMap.add N0 (I & i) bctxt_empty in
  let synth i o := synthesize'' n (nv, nm, nq o) p (nb i) d in
  match ios with
  | +[(i, o)] => do vmq <- synth i o;
                 Some +[vmq]
  | (i, o) +:: ios' => do vmq <- synth i o;
                       do vmqs <- synthesize' n p d ios';
                       Some (vmq +:: vmqs)
  end.

Definition synthesize (n : nat) (p : plib) (d : tdsl) {I O} (ios : examples I O) : option vsa :=
  do vvqs <- synthesize' n p d ios;
  let nvs := nemap (fun vmq => let '(v, m, q) := vmq in v) vvqs in
  unify nvs.

Definition propagate_ivr (es : vid_ctxt (PolySet texp _)) (ivr : vid + rid) : list texp :=
  match ivr with
  | inl iv => match (NatMap.find iv es) with
              | Some se => se
              | None => []
              end
  | inr ir => [] (* TODO include d : tdsl here, and enumerate all *)
  end.

Definition nelist_texp_base (l : list texp) := map (fun e => EBase e) l.
Definition nelist_texp_prod (l1 : list texp) (l2 : list nelist_texp) : list nelist_texp :=
  fold_left (fun l a => (map (fun b => ECons a b) l2) ++ l) l1 [].

Fixpoint propagate_ivrs (es : vid_ctxt (PolySet texp _)) ft (ivrs : fraiseT (vid + rid) ft) {struct ft} : list nelist_texp.
  destruct ft.
  - apply (nelist_texp_base (propagate_ivr es ivrs)).
  - destruct ivrs.
    apply (nelist_texp_prod (propagate_ivr es s) (propagate_ivrs es ft f)).
Defined.

Fixpoint propagate_ivrsl (es : vid_ctxt (PolySet texp _)) ft (ivrsl : list (fraiseT (vid + rid) ft)) : list nelist_texp :=
  match ivrsl with
  | [] => []
  | ivrs :: ivrsl' => propagate_ivrs es ft ivrs ++ propagate_ivrsl es ft ivrsl'
  end.

Fixpoint propagate_c (es : vid_ctxt (PolySet texp _)) vt (c : vconstructor vt) : PolySet texp _ :=
  match c with
  | VB _ ib => [EB ib]
  | VC _ c => [EC _ c]
  | VF _ ft ip ivrsl => map (fun args => EF ft ip args) (propagate_ivrsl es ft ivrsl)
  end.

Fixpoint propagate_cs (es : vid_ctxt (PolySet texp _)) vt (cs : list (vconstructor vt)) : PolySet texp _ :=
  match cs with
  | [] => []
  | c :: cs' => PolySet_union (propagate_c es _ c) (propagate_cs es _ cs')
  end.

Fixpoint propagate_s (p : pspace) (bt rt : vtype) (ib : bid) (is : sid) : PolySet texp _ :=
  let '(PS es ps) := p in
  match (PolyMap_find is ps) with
  | Some p' => let '(PS es' ps') := p' in
               match (NatMap.find N0 es') with
               | Some se => map (fun e => EL ib bt e) se
               | None => []
               end
  | None => []
  end.

Definition propagate_r (p : pspace) (r : vrule) : PolySet texp _ :=
  let '(PS es ps) := p in
  match r with
  | VR vt cs => propagate_cs es _ cs
  | VL rt ib bt is => propagate_s p bt rt ib is
  | VU => []
  end.

Fixpoint propagate (u : ivsa) (p : pspace) : pspace :=
  let '(IVSA vd us) := u in
  let '(PS es ps) := p in
  let es' := NatMap.map (propagate_r p) vd in
  let ps' := propagate_ss us ps in
  PS es' ps'

(* requires the assoc lists internally to have the same order *)
with propagate_ss (us : PolyMap sid ivsa _) (ps : PolyMap sid pspace _) : PolyMap sid pspace _ :=
  match us, ps with
  | [], [] => []
  | (is1, u) :: us',  (is2, p) :: ps' => (*if eq_dec is1 is2
                                         then (is1, propagate u p) :: propagate_ss us' ps'
                                         else []*) [] (* TODO fix *)
  | _, _ => []
  end.

Fixpoint output' (n : nat) (u : ivsa) (p : pspace) : pspace :=
  match n with
  | 0 => p
  | S n' => output' n' u (propagate u p)
  end.

Definition output (n : nat) (u : ivsa) : option (list texp) :=
  let '(PS es ps) := output' n u (pspace_empty u) in
  NatMap.find N0 es.

Eval compute in interpret plib_empty TBool TBool (EB N0) false.

(* divide by 2 primitive *)

Definition div2FT : ftype := +[TVal TNat].
Definition div2RT : vtype := TNat.
Definition div2FTB : ftbool div2FT := false.

Definition fdiv2 : fsem div2FT div2RT := fun on => match on with Some n => Some (Nat.div n 2) | None => None end.
Definition bdiv2 : bsem div2FT div2RT div2FTB := fun n f => [Some (2*n); Some (2*n+1)].
Definition pdiv := P div2FT div2RT div2FTB fdiv2 bdiv2.
Definition divlib : plib := NatMap.add N0 pdiv plib_empty.

Eval compute in interpret divlib TNat TNat (EF div2FT N0 (EBase (EB N0))) 7.

(* string append primitive *)

Definition appendFT : ftype := +[TVal TStr; TVal TStr].
Definition appendRT : vtype := TStr.
Definition appendFTB : ftbool appendFT := (false, false).

Definition fappend : fsem appendFT appendRT := fun oss =>
  match oss with
  | (Some s1, Some s2) => Some (append s1 s2)
  | (_, _) => None
  end.

Fixpoint range (n : nat) : list nat :=
  match n with
  | 0 => [0]
  | S n' => n :: (range n')
  end.

Definition bappend : bsem appendFT appendRT appendFTB := fun s f =>
  let len := String.length s in
  map (fun n => (Some (String.substring 0 n s), Some (String.substring n (len-n) s))) (range len).

Definition pappend := P appendFT appendRT appendFTB fappend bappend.
Definition appendlib : plib := NatMap.add N0 pappend plib_empty.

Open Scope string.
Eval compute in interpret appendlib TStr TStr (EF appendFT N0 (ECons (EB N0) (EBase (EB N0)))) "hi".

(* function apply primitive *)
Definition applyFT I O : ftype := +[TFun I O; TVal I].
Definition applyRT O : vtype := O.
Definition applyFTB I O : ftbool (applyFT I O) := (false, false).

Definition fapply I O : fsem (applyFT I O) (applyRT O) := fun obtei =>
  match obtei with
  | (Some (b, vt, e), Some i) => None
  | _ => None
  end.

Definition test n p d I O ios :=
  do v <- @synthesize n p d I O ios;
  let '(VSA vd _ _ _) := v in
  output n (IVSA vd []).

Definition ex_dsl1 := NatMap.add N0 (R TNat +[B _ N0; T _; C TNat 4; F div2RT div2FT N0 N0]) tdsl_empty.
Eval vm_compute in test 2 divlib ex_dsl1 TNat TNat +[(6, 3)].

Definition ex_dsl2 := NatMap.add N0 (R TStr +[B _ N0; F appendRT appendFT N0 (N0, N0)]) tdsl_empty.
Eval vm_compute in test 4 appendlib ex_dsl2 TStr TStr +[("hi", "hihihi")]. 
