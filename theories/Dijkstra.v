From mathcomp Require Import all_ssreflect.

Section Dijkstra.
  Import Order.TTheory.

  Variable V : finType.
  Variable C : orderType tt.

  Variable adj : V -> V -> C -> C.
  Hypothesis adj_increase : forall v u c, (c <= adj v u c)%O.
  Hypothesis adj_monotone : forall c c', (c <= c')%O -> forall v u, (adj v u c <= adj v u c')%O.

  Section WithC0.
    Variable c0 : C.

    Fixpoint cost_of_path t p :=
      if p is v :: p
      then adj t v (cost_of_path v p)
      else c0.

    Lemma cost_of_path_cons : forall t v p, cost_of_path t (v :: p) = adj t v (cost_of_path v p).
    Proof. by []. Qed.

    Lemma cost_of_path_increase : forall p t,
      (c0 <= cost_of_path t p)%O.
    Proof.
      elim => //= ? ? ? ?.
      exact /(le_trans (adj_increase _ _ _)) /adj_monotone.
    Qed.

    Definition shortest_path t p :=
      forall p', last t p' = last t p -> (cost_of_path t p <= cost_of_path t p')%O.

    Fixpoint dijkstra_rec n vs ps :=
      if n is n.+1
      then
        if vs is v :: _
        then
          let u := [arg min_(u < v in vs) cost_of_path u (ps u)]%O in
          dijkstra_rec n (rem u vs) (fun v => if (cost_of_path v (ps v) <= adj v u (cost_of_path u (ps u)))%O then ps v else u :: ps u)
        else ps
      else ps.

    Definition dijkstra s :=
      dijkstra_rec (#|V|.-1) (rem s (enum V)) (fun v => if v == s then [::] else [:: s]).
  End WithC0.

  Lemma cost_of_path_rcons s c0 : forall p t,
    cost_of_path c0 t (rcons p s) = cost_of_path (adj (last t p) s c0) t p.
  Proof. by elim => //= ? ? ->. Qed.

  Lemma dijkstra_rec_correct c0 s : forall n vs,
    size vs = n ->
    uniq vs ->
    forall ps,
    (forall u, last u (ps u) = s) ->
    (forall v, { in ps v, forall u, u \notin vs }) ->
    (forall u, u \notin vs -> { in vs, forall v p, last v p = s -> (cost_of_path c0 u (ps u) <= cost_of_path c0 v p)%O }) ->
    (forall v p, { in p, forall u, u \notin vs } \/ v \notin vs -> last v p = s -> (cost_of_path c0 v (ps v) <= cost_of_path c0 v p)%O) ->
    (forall v, last v (dijkstra_rec c0 n vs ps v) = s) /\
    (forall v, shortest_path c0 v (dijkstra_rec c0 n vs ps v)).
  Proof.
    elim => /= [ ? /size0nil -> ? | ? IHn [ | v vs ] //= /succn_inj ? ? ] ps Hs Hps Hsep Hlb.
    - split => // ? ?. rewrite Hs. exact /Hlb /or_intror.
    - set u := [arg min_(u < v in v :: vs) cost_of_path c0 u (ps u)]%O.
      have -> : (if v == u then vs else v :: rem u vs) = rem u (v :: vs) by [].
      have [ Hin Hlb' ] : u \in v :: vs /\ { in v :: vs, forall w, (cost_of_path c0 u (ps u) <= cost_of_path c0 w (ps w))%O }.
      { have /(@Order.TotalTheory.arg_minP _ _ _ v
          (fun u => u \in v :: vs) (fun u => cost_of_path c0 u (ps u)))
        : v \in v :: vs by rewrite in_cons eqxx.
        by inversion 1. }
      have IHp : { in v :: vs, forall x p p',
        { in p', forall u, u \notin v :: vs } ->
        last (last x (rev p)) p' = s ->
        (cost_of_path c0 u (ps u) <= cost_of_path (cost_of_path c0 (last x (rev p)) p') x (rev p))%O }.
      { move => x ?.
        elim => /= [ ? ? ? | y p IHp p' Hnotin ].
        - apply /(@le_trans _ _ (cost_of_path c0 x (ps x))).
          + exact /Hlb'.
          + apply /Hlb; eauto.
        - rewrite rev_cons last_rcons => ?.
          case (boolP (y \in v :: vs)) => ?.
          + apply /(@le_trans _ _ (cost_of_path c0 y (ps y))).
            { exact /Hlb'. }
            apply /(@le_trans _ _ (cost_of_path c0 y p')).
            { by refine (Hlb _ _ (or_introl _) _). }
            exact /cost_of_path_increase.
          + rewrite cost_of_path_rcons.
            apply /(IHp (y :: p')) => // ?.
            by rewrite in_cons => /orP [ /eqP -> | /Hnotin ]. }
      have Hu : { in v :: vs, forall x p,
        last x p = s ->
        (cost_of_path c0 u (ps u) <= cost_of_path c0 x p)%O }.
      { move => ? /IHp IH p. move: (IH (rev p) [::]). rewrite /= revK. by apply. }
      apply /IHn => [ | | ? | w | w | w p ].
      + by rewrite size_rem.
      + exact /rem_uniq.
      + by rewrite !(fun_if (last _)) /= !Hs if_same.
      + case (cost_of_path c0 w (ps w) <= adj w u (cost_of_path c0 u (ps u)))%O => ?;
        rewrite rem_filter // mem_filter negb_and.
        * move => /Hps ->. by rewrite orbT.
        * rewrite in_cons => /orP [ /= -> // | /Hps -> ]. by rewrite orbT.
      + rewrite rem_filter // mem_filter negb_and => /orP [ /negbNE /eqP -> x | ? x ];
        rewrite mem_filter => /andP [ ? ? ] ? ?;
        rewrite (fun_if (cost_of_path _ _)) -minEle le_minl.
        * by rewrite Hu.
        * by rewrite Hsep.
      + rewrite rem_filter // mem_filter negb_and
          (fun_if (cost_of_path _ _)) cost_of_path_cons -minEle le_minl.
        case (boolP (w \in v :: vs)) => [ Hin' | Hnotin ? ? ].
        * rewrite Hin' orbF => [ [ | /negbNE /eqP -> /(Hu _ Hin) -> // ] ].
          { case: p => [ ? ? | x p Hnotin ].
            - rewrite Hlb //. by left.
            - have /Hnotin : x \in x :: p by rewrite in_cons eqxx.
              rewrite mem_filter negb_and => /= /orP [ /negbNE /eqP -> | ? ] ?.
              + exact /orP /or_intror /adj_monotone /Hu.
              + apply /orP /or_introl /(@le_trans _ _ (cost_of_path c0 w (x :: ps x))).
                { apply /Hlb => //=. left => ?. by rewrite in_cons => /orP [ /eqP -> | /Hps ]. }
                apply /adj_monotone /Hlb => //. by right. }
        * apply /orP /or_introl /Hlb; eauto.
  Qed.

  Theorem dijkstra_correct c0 s :
    (forall u, last u (dijkstra c0 s u) = s) /\
    (forall v, shortest_path c0 v (dijkstra c0 s v)).
  Proof.
    apply /dijkstra_rec_correct => [ | | u | v ? | ? | v [ /= ? <- | /= u p ] ].
    - by rewrite size_rem ?cardE ?mem_enum.
    - apply /rem_uniq /enum_uniq.
    - rewrite !(fun_if (last _)) /=. by case (eqVneq u s).
    - case (eqVneq v s) => //.
      by rewrite inE (rem_filter _ (enum_uniq _)) mem_filter negb_and => /= ? ->.
    - rewrite (rem_filter _ (enum_uniq _)) mem_filter negb_and mem_enum orbF => /= /negbNE -> ? ? ? ?.
      exact /cost_of_path_increase.
    - by rewrite eqxx lexx.
    - rewrite (fun_if (cost_of_path _ _)) /= (rem_filter _ (enum_uniq _)) mem_filter negb_and mem_enum orbF /=.
      case (eqVneq v s) => /= [ -> ? ? | ? [ ] // Hnotin ].
      + exact /(le_trans (adj_increase _ _ _)) /adj_monotone /cost_of_path_increase.
      + have /Hnotin : u \in u :: p by rewrite in_cons eqxx.
        rewrite mem_filter negb_and mem_enum orbF => /negbNE /eqP -> ?.
        exact /adj_monotone /cost_of_path_increase.
  Qed.
End Dijkstra.
