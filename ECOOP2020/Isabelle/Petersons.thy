theory Petersons
imports OpSem
begin

datatype PC =
  L1
| L2
| L3
| L4
| L5
| L6
| L7

consts t1 :: T 
consts t2 :: T
consts flag1 :: L
consts flag2 :: L
consts turn :: L


definition "thrdsvars \<equiv>  t1 \<noteq> 0 \<and> t2 \<noteq> 0 \<and> t1 \<noteq> t2 \<and>
                         flag1 \<noteq> flag2 \<and>
                         flag1 \<noteq> turn \<and>
                         flag2 \<noteq> turn"



record mp_state =
  pc :: "T \<Rightarrow> PC"
  state :: surrey_state
  r1 :: "T \<Rightarrow> V"
  r2 :: "T \<Rightarrow> V"
  (* auxiliary *)
  after :: "T \<Rightarrow> V"

(*
  tv1 :: V
  tv2 :: V
*)
definition 
  "update_loc t nv pcf \<equiv> pcf (t := nv)"

(*
definition 
  "tv_id s s' \<equiv> tv1 s' = tv1 s \<and> tv2 s' = tv2 s"

definition 
  "after_id s s' \<equiv> after1 s' = after1 s \<and> after2 s' = after2 s"
*)

definition 
  "aux_id s s' \<equiv>  after s = after s'"
(* tv_id s s' \<and>*)

definition 
  "locals_id s s' \<equiv> r1 s' = r1 s \<and> r2 s' = r2 s  \<and> aux_id s s'"



lemmas mp_simps [simp] = 
  locals_id_def
  aux_id_def
  update_loc_def 
  thrdsvars_def
(*  tv_id_def*)

(*\<and> (\<exists> v. (state s) RMW[turn, v, t']\<^sub>t (state s'))*)
definition prog :: "T \<Rightarrow>  mp_state \<Rightarrow> mp_state \<Rightarrow> bool " where
"prog t s s' \<equiv> 
(
if t = t1
then let t' = t2 in 
  if (pc s) t = L1
    then
      pc s' = update_loc t L2 (pc s) \<and>
      ((state s) [flag1 := 1]\<^sub>t (state s')) \<and> 
      locals_id s s' 
   else
  if (pc s) t = L2
    then
      pc s' = update_loc t L3 (pc s) \<and>
      (state s) SWAP[turn, t']\<^sub>t (state s')  
      \<and> after s' = update_loc t 1 (after s)  \<and>
      r1 s' = r1 s \<and> r2 s' = r2 s 
  else
  if (pc s) t = L3
    then
      pc s' = update_loc t L4 (pc s) \<and>
      ((state s) [r1 s' t \<leftarrow>\<^sup>A flag2]\<^sub>t (state s')) \<and>
      r1 s t' = r1 s' t' \<and> r2 s' = r2 s \<and> aux_id s s'
  else
  if (pc s) t = L4
    then
      pc s' = update_loc t L5 (pc s) \<and>
      ((state s) [r2 s' t \<leftarrow> turn]\<^sub>t (state s')) \<and> 
      r1 s' = r1 s \<and> r2 s' t' = r2 s t' \<and> aux_id s s'
  else
  if (pc s) t = L5
    then
      (if r1 s t = 0 \<or> r2 s t = t 
       then pc s' = update_loc t L6 (pc s)
       else pc s' = update_loc t L3 (pc s)) 
      \<and>  locals_id s s' \<and> state s = state s'
  else
  if (pc s) t = L6
    then
      pc s' = update_loc t L7 (pc s) 
      \<and> ((state s) [flag1 :=\<^sup>R 0]\<^sub>t (state s')) 
      \<and> after s' = update_loc t 0 (after s) 
      \<and> r1 s' = r1 s \<and> r2 s' = r2 s 
  else 
  False
else
if t = t2
then let t' = t1 in  
  if (pc s) t = L1
    then
      pc s' = update_loc t L2 (pc s) \<and>
      ((state s) [flag2 := 1]\<^sub>t (state s')) \<and>
      locals_id s s'
  else
  if (pc s) t = L2
    then
      pc s' = update_loc t L3 (pc s) \<and>
      (((state s) SWAP[turn, t']\<^sub>t (state s'))) 
      \<and> after s' = update_loc t 1 (after s) \<and>
      r1 s' = r1 s \<and> r2 s' = r2 s 
  else
  if (pc s) t = L3
    then
      pc s' = update_loc t L4 (pc s) \<and>
      ((state s) [r1 s' t \<leftarrow>\<^sup>A flag1]\<^sub>t (state s')) \<and> 
      r1 s' t' = r1 s t' \<and> r2 s' = r2 s \<and> aux_id s s'
  else
  if (pc s) t = L4
    then
      pc s' = update_loc t L5 (pc s) \<and>
      ((state s) [r2 s' t \<leftarrow> turn]\<^sub>t (state s')) \<and> 
      r1 s' = r1 s \<and> r2 s' t' = r2 s t' \<and> aux_id s s'
  else
  if (pc s) t = L5
    then
      (if (r1 s t = 0 \<or> r2 s t = t) 
      then pc s' = update_loc t L6 (pc s)
      else pc s' = update_loc t L3 (pc s)) 
      \<and> locals_id s s' \<and> state s = state s'
  else
  if (pc s) t = L6
    then
      pc s' = update_loc t L7 (pc s) \<and>
      ((state s) [flag2 :=\<^sup>R 0]\<^sub>t (state s')) \<and> after s' = update_loc t 0 (after s) \<and>
      r1 s' = r1 s \<and> r2 s' = r2 s 
  else
  False
else
False
)"



definition prog_inv :: "T \<Rightarrow> PC \<Rightarrow> mp_state \<Rightarrow> bool " where
"prog_inv t p s \<equiv> 
  if t = t1
  then let t' = t2 in 
    (case p of
          L1 \<Rightarrow> after s t = 0 \<and> [flag1 =\<^sub>t 0] (state s) \<and> (cvd[turn, 0] (state s) \<or> cvd[turn, t1] (state s))
                \<and> (after s t' = 1 \<longrightarrow> cvd[turn, t1] (state s) \<and> [turn = t]\<^sub>t\<lparr>flag2 = 1\<rparr> (state s))
                \<and>  \<not> [turn \<approx>\<^sub>t' t'] (state s)
\<comment> \<open>[flag1 := 1]t\<close>
        | L2 \<Rightarrow> after s t = 0 \<and> [flag1 =\<^sub>t 1] (state s) 
                \<and> (after s t' = 1 \<longrightarrow> cvd[turn, t1] (state s) \<and> [turn = t]\<^sub>t\<lparr>flag2 = 1\<rparr> (state s)) 
                \<and>  \<not> [turn \<approx>\<^sub>t' t'] (state s)
\<comment> \<open>RMW[turn, v, t2]t\<close>
        | L3 \<Rightarrow> after s t = 1 \<and> [flag1 =\<^sub>t 1] (state s)
                \<and> (after s t' = 1 \<and> ([flag2 \<approx>\<^sub>t 0] (state s) \<or> [turn \<approx>\<^sub>t t] (state s)) \<longrightarrow>  [turn =\<^sub>t' t] (state s))
                
\<comment> \<open>[r1 s' \<leftarrow>A flag2]t\<close>
        | L4 \<Rightarrow> after s t = 1 \<and> [flag1 =\<^sub>t 1] (state s)
                \<and> (after s t' = 1 \<and> (r1 s t = 0 \<or> [turn \<approx>\<^sub>t t] (state s) \<or> [flag2 \<approx>\<^sub>t 0] (state s)) \<longrightarrow>  [turn =\<^sub>t' t] (state s))
\<comment> \<open>[r2 s' \<leftarrow> turn]t\<close>
        | L5 \<Rightarrow> after s t = 1 \<and> [flag1 =\<^sub>t 1] (state s)
                \<and> (after s t' = 1 \<and> (r1 s t = 0 \<or> r2 s t = t \<or> [turn \<approx>\<^sub>t t] (state s) \<or> [flag2 \<approx>\<^sub>t 0] (state s)) \<longrightarrow>  [turn =\<^sub>t' t] (state s))
\<comment> \<open>r1 s = 0 \<or> r2 s = t1\<close>
        | L6 \<Rightarrow> after s t = 1 \<and> [flag1 =\<^sub>t 1] (state s) 
                \<and> (after s t' = 1 \<longrightarrow> [turn =\<^sub>t' t] (state s))
\<comment> \<open>[flag1 :=R 0]t\<close>
        | _ \<Rightarrow> True
    )
  else 
    if t = t2 then let t' = t1 in
      (case p of
          L1 \<Rightarrow> after s t = 0 \<and> [flag2 =\<^sub>t 0] (state s) \<and> (cvd[turn, 0] (state s) \<or> cvd[turn, t] (state s))
                \<and> (after s t' = 1 \<longrightarrow> cvd[turn, t2] (state s) \<and> [turn = t]\<^sub>t\<lparr>flag1 = 1\<rparr> (state s))
                \<and> \<not> [turn \<approx>\<^sub>t' t'] (state s)
        | L2 \<Rightarrow> after s t = 0 \<and> [flag2 =\<^sub>t 1] (state s) 
                \<and> (after s t' = 1 \<longrightarrow> cvd[turn, t2] (state s) \<and> [turn = t]\<^sub>t\<lparr>flag1 = 1\<rparr> (state s))  
                \<and> \<not> [turn \<approx>\<^sub>t' t'] (state s)
\<comment> \<open>test ok to enter\<close>
        | L3 \<Rightarrow> after s t = 1 \<and> [flag2 =\<^sub>t 1] (state s)
                \<and> (after s t' = 1 \<and> ([flag1 \<approx>\<^sub>t 0] (state s) \<or> [turn \<approx>\<^sub>t t] (state s)) \<longrightarrow>  [turn =\<^sub>t' t] (state s))
        | L4 \<Rightarrow> after s t = 1 \<and> [flag2 =\<^sub>t 1] (state s)
                \<and> (after s t' = 1 \<and> (r1 s t = 0 \<or> [turn \<approx>\<^sub>t t] (state s) \<or> [flag1 \<approx>\<^sub>t 0] (state s)) \<longrightarrow>  [turn =\<^sub>t' t] (state s)) 
        | L5 \<Rightarrow> after s t = 1 \<and> [flag2 =\<^sub>t 1] (state s)   
                \<and> (after s t' = 1 \<and> (r1 s t = 0 \<or> r2 s t = t \<or> [turn \<approx>\<^sub>t t] (state s) \<or> [flag1 \<approx>\<^sub>t 0] (state s)) \<longrightarrow>  [turn =\<^sub>t' t] (state s))
\<comment> \<open>critical section\<close>
        | L6 \<Rightarrow> after s t = 1 \<and> [flag2 =\<^sub>t 1] (state s) 
                \<and> (after s t' = 1 \<longrightarrow> [turn =\<^sub>t' t] (state s))
        | _ \<Rightarrow> True
      )
  else
    False
"

lemma mutex:
  "thrdsvars \<Longrightarrow> 
    prog_inv t1 L6 s \<Longrightarrow> prog_inv t2 L6 s \<Longrightarrow> False"
  by (simp add: prog_inv_def d_obs_def d_obs_t_def)



(*initial_state \<sigma> I*)
definition init_map  :: "(L \<Rightarrow> V) \<Rightarrow> bool" where
  "init_map \<phi> \<equiv> \<phi> flag1 = 0 \<and> \<phi> flag2 = 0 \<and> \<phi> turn = 0" 

definition init_s  :: "surrey_state  \<Rightarrow> bool"
  where
    "init_s ss \<equiv> \<exists> \<phi>. initial_state ss \<phi> \<and> init_map \<phi>"

definition init  :: "mp_state  \<Rightarrow> bool"
  where
    "init s \<equiv> 
        (\<forall> t. t \<in> {t1, t2} \<longrightarrow> (pc s) t = L1 \<and> (r1 s) t = 0 \<and> (r2 s) t = 0 \<and> after s t = 0)
      \<and> init_s (state s) \<and> thrdsvars"



definition "global_inital_vals s \<equiv> init_val (state s) flag1 0
                                \<and>  init_val (state s) flag2 0
                                \<and>  init_val (state s) turn 0"

definition "global_covered s \<equiv> cvd[turn, 0] (state s) 
                             \<or> cvd[turn, t1] (state s)
                             \<or> cvd[turn, t2] (state s)"

definition "global_covered_turn_0 s \<equiv> cvd[turn, 0] (state s) \<longrightarrow> after s t1 = 0 \<and> after s t2 = 0"


definition "global_after_values s \<equiv> (after s t1 = 0 \<or> after s t1 = 1) \<and>  (after s t2 = 0 \<or> after s t2 = 1)"


(*add proved global invariants here*)
definition "global_invs s \<equiv> global_inital_vals s 
                          \<and> global_covered s"


lemmas global_simp [simp] = 
  global_covered_def
  global_inital_vals_def
  global_covered_turn_0_def
  global_after_values_def


lemmas prog_simp  =
  prog_def
  prog_inv_def
  init_def
  init_s_def
  init_map_def


(***************** Global Invariant *************************)



lemma init_hold_global_after_values: "init s\<Longrightarrow> thrdsvars  \<Longrightarrow> global_after_values s"
  using global_after_values_def init_def by blast


lemma global_hold_global_after_values:
  assumes "global_after_values s"
   and "prog t s s'"
   and "t\<in>{t1,t2}"
   and "thrdsvars"
 shows "global_after_values s'"
  using assms
  apply (simp_all add:  prog_def)
  apply(elim disjE)
     apply(cases "pc s t1", simp_all)
   by(cases "pc s t2", simp_all)


lemma init_hold_global_inital_vals: "init s\<Longrightarrow> thrdsvars  \<Longrightarrow> global_inital_vals s"
  apply (simp add: init_val_def prog_simp)
  apply (elim conjE, intro conjI)
  apply(unfold writes_on_def value_def initial_state_def mo_def, simp)
  by auto[3]



lemma global_hold_global_inital_vals:
  assumes "global_inital_vals s"
   and "prog t s s'"
   and "t\<in>{t1,t2}"
   and "thrdsvars"
 shows "global_inital_vals s'"
  using assms
  apply (simp_all add:  prog_def)
  apply(elim conjE disjE)
   apply(intro conjI)
     apply clarsimp 
  apply (cases "pc s t1", simp_all)
  using init_val_pres apply blast+
  apply (cases "pc s t1", simp_all)
  using init_val_pres apply blast+
  apply (cases "pc s t1", simp_all)
  using init_val_pres apply blast+
  apply (cases "pc s t2", simp_all)
  using init_val_pres by blast+


lemma init_hold_global_covered: "init s\<Longrightarrow> thrdsvars  \<Longrightarrow> global_covered s"
  apply (simp add:  prog_simp)
  apply (elim conjE)
  by (metis init_covered_v)

lemma global_hold_global_covered:
  assumes "global_covered s"
   and "wfs (state s)"
   and "prog t s s'"
   and "t\<in>{t1,t2}"
   and "thrdsvars"
 shows "global_covered s'"
  using assms
  apply (simp_all add:  prog_def)
  apply(elim disjE)
  apply(cases "pc s t1", simp_all)
  apply(elim conjE)
  using covered_diff_var_pres
  apply (metis cvd_WrX_other_var_pres, metis cvd_RMW_pres, metis cvd_RdA_pres, metis cvd_Rdx_pres, metis cvd_WrR_other_var_pres)
  apply (cases "pc s t2", simp_all)
  apply (metis cvd_WrX_other_var_pres, metis cvd_RMW_pres, metis cvd_RdA_pres, metis cvd_Rdx_pres, metis cvd_WrR_other_var_pres)
  apply (cases "pc s t1", simp_all)
  apply (metis cvd_WrX_other_var_pres, metis cvd_RMW_pres, metis cvd_RdA_pres, metis cvd_Rdx_pres, metis cvd_WrR_other_var_pres)
  apply (cases "pc s t1", simp_all)
  apply (metis cvd_WrX_other_var_pres, metis cvd_RMW_pres, metis cvd_RdA_pres, metis cvd_Rdx_pres, metis cvd_WrR_other_var_pres)
  apply (cases "pc s t2", simp_all)
  apply (metis cvd_WrX_other_var_pres, metis cvd_RMW_pres, metis cvd_RdA_pres, metis cvd_Rdx_pres, metis cvd_WrR_other_var_pres)
  apply (cases "pc s t2", simp_all)
  by (metis cvd_WrX_other_var_pres, metis cvd_RMW_pres, metis cvd_RdA_pres, metis cvd_Rdx_pres, metis cvd_WrR_other_var_pres)


lemma init_hold_global_covered_turn_0: "init s\<Longrightarrow> thrdsvars  \<Longrightarrow> global_covered_turn_0 s"
  by (simp add:  prog_simp)


lemma global_hold_global_covered_turn_0:
  assumes "global_covered_turn_0 s"
   and "wfs (state s)"
   and "prog_inv t (pc s t) s"
   and "prog t s s'"
   and "t\<in>{t1,t2}"
   and "thrdsvars"
 shows "global_covered_turn_0 s'"
  using assms
  apply (simp_all add:  prog_def  prog_inv_def)
  apply(elim disjE)
   apply(cases "pc s t1", simp_all)
             apply(elim conjE, intro impI conjI)
       apply(case_tac "cvd[turn, 0] (state s)")
        apply blast
  using cvd_backwards_WrX apply blast
      apply(elim conjE)
      defer
  using cvd_backwards_RdA apply blast
  defer
  using cvd_backwards_WrR apply blast
   apply(cases "pc s t2", simp_all)
   using cvd_backwards_WrX apply blast
        defer
   using cvd_backwards_RdA apply blast
   defer
   using cvd_backwards_WrR apply blast
      apply(case_tac "cvd[turn, 0] (state s)")
       apply simp
       apply(case_tac "cvd[turn, t2] (state s')")
   using cvd_u_not_cvd_v
   defer
   using cvd_RMW_new_cvd apply blast
       apply simp
       apply(case_tac "after s t2 = Suc 0")
        defer     apply simp
   using RMW_exist_w_in_post
   apply (metis assms(6) covered_v_def thrdsvars_def)
   using not_cvd_RdX_pres apply blast
   using RMW_exist_w_in_post
   apply (metis assms(6) covered_v_def thrdsvars_def)
   using not_cvd_RdX_pres apply blast
   using RMW_exist_w_in_post
   using cvd_u_not_cvd_v apply blast
    using RMW_exist_w_in_post
  by (metis assms(6) cvd_RMW_new_cvd cvd_u_not_cvd_v thrdsvars_def)



(***************** Initialisation *************************)


lemma init_inv : "init s \<Longrightarrow> global_invs s \<Longrightarrow> thrdsvars \<Longrightarrow> t\<in>{t1,t2} \<Longrightarrow> prog_inv t L1 s"
  apply (simp add: prog_simp global_invs_def) 
  apply (intro conjI, elim conjE exE)
  using init_d_obs
   apply clarsimp
  apply (metis d_obs_p_obs_agree init_covered_v initial_wfs less_numeral_extra(3))
  by (metis d_obs_p_obs_agree gr_implies_not0 init_covered_v init_d_obs initial_wfs)


(********************* Thread 1 ************************)


lemma local:
  assumes "wfs (state s)" 
  and "prog_inv t (pc s t) s"
  and "global_invs s"
  and "thrdsvars"
  and "prog t s s'"
  and "t \<in> {t1, t2}"
shows  "prog_inv t ((pc s') t) s'"
  using assms apply (simp add: prog_inv_def prog_def)
  apply (cases "t = t1", simp_all)
  apply (cases "pc s t1", simp_all)
  apply (metis assms(1) c_obs_WrX_pres cvd_WrX_other_var_pres d_obs_WrX_set not_p_obs_WrX_pres)
  apply (metis Up_reads_cvd_v avar.simps(3) c_obs_UpRA_d_obs covered_v_RMW_d_obs d_obs_RMW_other d_obs_p_obs_agree isUp.simps(3) n_not_Suc_n wfs_preserved wr_val.simps(2)) 
  apply (metis assms(1) d_obs_RdA_other dobs_RdA_pres not_pobs_RdA_pres p_obs_RdA_intro)
  apply (metis assms(1) d_obs_RdX_other dobs_RdX_pres not_pobs_RdX_pres p_obs_RdX_intro)
  apply (cases "r1 s t = 0 \<or> r2 s t = t", auto) 
  apply (cases "pc s t2", simp_all)
  apply (metis assms(1) c_obs_WrX_pres cvd_WrX_other_var_pres d_obs_WrX_set not_p_obs_WrX_pres)
  apply (metis Up_reads_cvd_v c_obs_UpRA_d_obs cvd_RMW_d_obs d_obs_RMW_other d_obs_p_obs_agree n_not_Suc_n wfs_preserved)
  apply (metis assms(1) d_obs_RdA_other dobs_RdA_pres not_pobs_RdA_pres p_obs_RdA_intro)
  apply (metis assms(1) d_obs_RdX_other dobs_RdX_pres not_pobs_RdX_pres p_obs_RdX_intro)
  by (cases "r1 s t = 0 \<or> r2 s t = t", auto) 



  (* Global proofs *) 

lemma global_L1 :
  assumes "wfs (state s)" 
  and "pc s t = L1"
  and "prog_inv t (pc s t) s"
  and "prog_inv t' (pc s t') s"
  and "global_invs s"
  and "thrdsvars"
  and "prog t' s s'"
  and "t \<in> {t1, t2}"
  and "t' \<in> {t1, t2}"
  and "t \<noteq> t'"
shows  "prog_inv t (pc s t) s'"
  using assms apply (simp add: prog_inv_def prog_def )
  apply (cases "t = t1", simp_all)
  apply (cases "pc s t", simp_all)
  apply (cases "pc s t'", simp_all)
  apply (metis cvd_WrX_other_var_pres dobs_WrX_pres not_p_obs_WrX_diff_var_pres)
  apply (metis c_obs_RMW_intro cvd_RMW_new_cvd dobs_RMW_pres not_p_obs_RMW_val_pres)
  apply (metis cobs_RdA_diff_var_pres cvd_RdA_pres dobs_RdA_pres not_pobs_RdA_pres)
  apply (metis c_obs_RdX_pres cvd_Rdx_pres dobs_RdX_pres not_pobs_RdX_pres)
  apply (metis assms(6) cvd_WrR_other_var_pres dobs_WrR_pres not_p_obs_WrR_val_pres thrdsvars_def)
  apply (cases "pc s t'", simp_all)
  apply (metis cvd_WrX_other_var_pres dobs_WrX_pres not_p_obs_WrX_diff_var_pres)
  apply (metis c_obs_RMW_intro cvd_RMW_new_cvd dobs_RMW_pres not_p_obs_RMW_val_pres)
  apply (metis cobs_RdA_diff_var_pres cvd_RdA_pres dobs_RdA_pres not_pobs_RdA_pres)
  apply (metis c_obs_RdX_pres cvd_Rdx_pres dobs_RdX_pres not_pobs_RdX_pres)
  by (metis assms(6) cvd_WrR_other_var_pres dobs_WrR_pres not_p_obs_WrR_val_pres thrdsvars_def)

lemma global_L2 :
  assumes "wfs (state s)" 
  and "pc s t = L2"
  and "prog_inv t (pc s t) s"
  and "prog_inv t' (pc s t') s"
  and "global_invs s"
  and "thrdsvars"
  and "prog t' s s'"
  and "t \<in> {t1, t2}"
  and "t' \<in> {t1, t2}"
  and "t \<noteq> t'"
shows  "prog_inv t (pc s t) s'"
  using assms apply (simp add: prog_inv_def prog_def )
  apply (cases "t = t1", simp_all)
  apply (cases "pc s t", simp_all)
  apply (cases "pc s t'", simp_all)
  apply (metis dobs_WrX_pres not_p_obs_WrX_diff_var_pres)
  apply (metis c_obs_RMW_intro cvd_RMW_new_cvd dobs_RMW_pres global_covered_def global_invs_def not_p_obs_RMW_val_pres)
  apply (metis cobs_RdA_diff_var_pres cvd_RdA_pres dobs_RdA_pres not_pobs_RdA_pres)
  apply (metis c_obs_RdX_pres cvd_Rdx_pres dobs_RdX_pres not_pobs_RdX_pres)
  apply (metis assms(10) dobs_WrR_pres not_p_obs_WrA_diff_var_pres)
  apply (cases "pc s t'", simp_all)
  apply (metis dobs_WrX_pres not_p_obs_WrX_diff_var_pres)
  apply (metis c_obs_RMW_intro cvd_RMW_new_cvd dobs_RMW_pres global_covered_def global_invs_def not_p_obs_RMW_val_pres)
  apply (metis cobs_RdA_diff_var_pres cvd_RdA_pres dobs_RdA_pres not_pobs_RdA_pres)
  apply (metis c_obs_RdX_pres cvd_Rdx_pres dobs_RdX_pres not_pobs_RdX_pres)
  by (metis assms(10) dobs_WrR_pres not_p_obs_WrA_diff_var_pres)

lemma global_L3 :
  assumes "wfs (state s)" 
  and "pc s t = L3"
  and "prog_inv t (pc s t) s"
  and "prog_inv t' (pc s t') s"
  and "global_invs s"
  and "thrdsvars"
  and "prog t' s s'"
  and "t \<in> {t1, t2}"
  and "t' \<in> {t1, t2}"
  and "t \<noteq> t'"
shows  "prog_inv t (pc s t) s'"
  using assms apply (simp add: prog_inv_def prog_def )
  apply (cases "t = t1", simp_all)
  apply (cases "pc s t", simp_all)
  apply (cases "pc s t'", simp_all)
  apply (metis dobs_WrX_pres)
  using cvd_RMW_d_obs dobs_RMW_pres apply blast
  apply (metis d_obs_RdA_other dobs_RdA_pres not_pobs_RdA_pres)
  apply (metis d_obs_RdX_pres dobs_RdX_pres not_pobs_RdX_pres)
  apply (metis dobs_WrR_pres)
  apply (cases "pc s t'", simp_all)
  apply (metis dobs_WrX_pres)
  apply (metis cvd_RMW_d_obs dobs_RMW_pres)
  apply (metis d_obs_RdA_other dobs_RdA_pres not_pobs_RdA_pres)
  apply (metis d_obs_RdX_pres dobs_RdX_pres not_pobs_RdX_pres)
  by (metis dobs_WrR_pres)
  
lemma global_L4 :
  assumes "wfs (state s)" 
  and "pc s t = L4"
  and "prog_inv t (pc s t) s"
  and "prog_inv t' (pc s t') s"
  and "global_invs s"
  and "thrdsvars"
  and "prog t' s s'"
  and "t \<in> {t1, t2}"
  and "t' \<in> {t1, t2}"
  and "t \<noteq> t'"
shows  "prog_inv t (pc s t) s'"
  using assms apply (simp add: prog_inv_def prog_def )
  apply (cases "t = t1", simp_all)
  apply (cases "pc s t", simp_all)
  apply (cases "pc s t'", simp_all)
  apply (metis dobs_WrX_pres)
  using cvd_RMW_d_obs dobs_RMW_pres apply blast
  apply (metis d_obs_RdA_other dobs_RdA_pres not_pobs_RdA_pres)
  apply (metis d_obs_RdX_pres dobs_RdX_pres not_pobs_RdX_pres)
  apply (metis dobs_WrR_pres)
  apply (cases "pc s t'", simp_all)
  apply (metis dobs_WrX_pres)
  apply (metis cvd_RMW_d_obs dobs_RMW_pres)
  apply (metis d_obs_RdA_other dobs_RdA_pres not_pobs_RdA_pres)
  apply (metis d_obs_RdX_pres dobs_RdX_pres not_pobs_RdX_pres)
  by (metis dobs_WrR_pres)

lemma global_L5 :
  assumes "wfs (state s)" 
  and "pc s t = L5"
  and "prog_inv t (pc s t) s"
  and "prog_inv t' (pc s t') s"
  and "global_invs s"
  and "thrdsvars"
  and "prog t' s s'"
  and "t \<in> {t1, t2}"
  and "t' \<in> {t1, t2}"
  and "t \<noteq> t'"
shows  "prog_inv t (pc s t) s'"
  using assms apply (simp add: prog_inv_def prog_def )
  apply (cases "t = t1", simp_all)
  apply (cases "pc s t", simp_all)
  apply (cases "pc s t'", simp_all)
  apply (metis dobs_WrX_pres)
  using cvd_RMW_d_obs dobs_RMW_pres apply blast
  apply (metis d_obs_RdA_other dobs_RdA_pres not_pobs_RdA_pres)
  apply (metis d_obs_RdX_pres dobs_RdX_pres not_pobs_RdX_pres)
  apply (metis dobs_WrR_pres)
  apply (cases "pc s t'", simp_all)
      apply (metis dobs_WrX_pres)
  apply (metis cvd_RMW_d_obs dobs_RMW_pres)
  apply (metis d_obs_RdA_other dobs_RdA_pres not_pobs_RdA_pres)
  apply (metis d_obs_RdX_pres dobs_RdX_pres not_pobs_RdX_pres)
  by (metis dobs_WrR_pres)

lemma global_L6 :
  assumes "wfs (state s)" 
  and "pc s t = L6"
  and "prog_inv t (pc s t) s"
  and "prog_inv t' (pc s t') s"
  and "global_invs s"
  and "thrdsvars"
  and "prog t' s s'"
  and "t \<in> {t1, t2}"
  and "t' \<in> {t1, t2}"
  and "t \<noteq> t'"
shows  "prog_inv t (pc s t) s'"
  using assms apply (simp add: prog_inv_def prog_def )
  apply (cases "t = t1", simp_all)
  apply (cases "pc s t", simp_all)
  apply (cases "pc s t'", simp_all)
  apply (metis dobs_WrX_pres)
  using cvd_RMW_d_obs dobs_RMW_pres apply blast
  apply (metis d_obs_RdA_other dobs_RdA_pres)
  apply (metis d_obs_RdX_pres dobs_RdX_pres)
  apply (metis dobs_WrR_pres)
  apply (cases "pc s t'", simp_all)
  apply (metis dobs_WrX_pres)
  apply (metis cvd_RMW_d_obs dobs_RMW_pres)
  apply (metis d_obs_RdA_other dobs_RdA_pres)
  apply (metis d_obs_RdX_pres dobs_RdX_pres)
  by (metis dobs_WrR_pres)




lemma global :
  assumes "wfs (state s)" 
  and "prog_inv t (pc s t) s"
  and "prog_inv t' (pc s t') s"
  and "global_invs s"
  and "thrdsvars"
  and "prog t' s s'"
  and "t \<in> {t1, t2}"
  and "t' \<in> {t1, t2}"
  and "t \<noteq> t'"
shows  "prog_inv t (pc s t) s'"
  using assms apply (cases "pc s t") 
  using global_L1 apply blast
  using global_L2 apply blast
  using global_L3 apply blast
  using global_L4 apply blast
  using global_L5 apply blast
  using global_L6 apply blast
  using prog_simp(2) by auto

end