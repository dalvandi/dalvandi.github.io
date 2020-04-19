theory MPA
imports OpSem
begin

datatype PC =
  L1
| L2
| L3

consts t1 :: T 
consts t2 :: T
consts d :: L
consts f :: L

definition "thrdsvars \<equiv> t1 \<noteq> t2 \<and> 
                        d \<noteq> f"


record mp_state =
  pc :: "T \<Rightarrow> PC"
  state :: surrey_state
  r :: V 

definition 
  "update_pc t nv pcf \<equiv> pcf (t := nv)"


lemmas mp_sis [simp] = 
  update_pc_def 
  thrdsvars_def


definition prog :: "T \<Rightarrow>  mp_state \<Rightarrow> mp_state \<Rightarrow> bool " where
"prog t s s' \<equiv> 
(
  if t = t1
    then
      if (pc s) t = L1
        then
           pc s'  = update_pc t L2 (pc s) \<and>
           (state s) [d:=5]\<^sub>t (state s') \<and>
           r s = r s'
        else
          if (pc s) t = L2
            then
              pc s' = update_pc t L3 (pc s) \<and>
              (state s) [f:=\<^sup>R 1]\<^sub>t (state s') \<and>
              r s = r s'
            else
              False
  else
    if t = t2
      then
        if (pc s) t = L1
          then
            (pc s' = update_pc t L2 (pc s) \<and>
            ((state s) [1 \<leftarrow>\<^sup>A f]\<^sub>t (state s')))
            \<or>
            (pc s'  = pc s \<and>
            (\<exists> v . v \<noteq> 1 \<and> ((state s) [v \<leftarrow>\<^sup>A f]\<^sub>t (state s'))))
         else
          if (pc s) t = L2
            then
              pc s' = update_pc t L3 (pc s) \<and>
              ((state s) [r s' \<leftarrow> d]\<^sub>t (state s'))
            else
              False
   else
    False
)"

definition prog_inv :: "T \<Rightarrow> PC \<Rightarrow> mp_state \<Rightarrow> bool " where
"prog_inv t p s \<equiv> let t' = t2 in
  if t = t1
    then
      (case p of
          L1 \<Rightarrow> (\<not> [f \<approx>\<^sub>t' 1] (state s)) \<and> [d =\<^sub>t 0] (state s) 
        | L2 \<Rightarrow> (\<not> [f \<approx>\<^sub>t' 1] (state s)) \<and> [d =\<^sub>t 5] (state s)
        | L3 \<Rightarrow> [d =\<^sub>t 5] (state s)
      )
  else 
     if t = t2 then
      (case p of
          L1 \<Rightarrow> [f = 1]\<^sub>t \<lparr>d = 5\<rparr> (state s)
        | L2 \<Rightarrow> [d =\<^sub>t 5] (state s)
        | L3 \<Rightarrow> r s = 5 
      )
  else False
"


(*initial_state \<sigma> I*)
definition init_map  :: "(L \<Rightarrow> V) \<Rightarrow> bool" where
  "init_map \<phi> \<equiv> \<phi> d = 0 \<and> \<phi> f = 0" 

definition init_s  :: "surrey_state  \<Rightarrow> bool"
  where
    "init_s ss \<equiv> \<exists> \<phi>. initial_state ss \<phi> \<and> init_map \<phi>"

definition init  :: "mp_state  \<Rightarrow> bool"
  where
    "init s \<equiv> (pc s) t1 = L1 
      \<and> (pc s) t2 = L1
    \<and> init_s (state s)"


lemma [simp]: "initial_state \<sigma>  \<phi> \<Longrightarrow> \<phi> x = v \<Longrightarrow> value \<sigma> (lastWr \<sigma> x) = v"
  apply (unfold initial_state_def value_def lastWr_def)
  using initial_state_def by auto

lemma init_only_one_write : "initial_state \<sigma>  \<phi> \<Longrightarrow>  w1 \<in> (writes_on \<sigma> x) \<Longrightarrow>  w2 \<in> (writes_on \<sigma> x) \<Longrightarrow> tst w1 = tst w2 \<and> w1 = w2"
  apply (unfold initial_state_def value_def lastWr_def writes_on_def)
  apply simp
  apply clarify by auto

lemma thrdView_of_init : "initial_state \<sigma> \<phi> \<Longrightarrow> (x, ts) \<in> writes \<sigma> \<Longrightarrow>  thrView \<sigma> t x = (x, ts) "
  apply (unfold initial_state_def)
  apply simp
  using init_only_one_write
  by clarsimp


lemma init_writes_write_on [simp]: "initial_state \<sigma> \<phi> \<Longrightarrow> (x, ts) \<in> writes \<sigma> \<Longrightarrow> (x, ts) \<in> writes_on \<sigma> x"
  apply (unfold initial_state_def writes_on_def)
  by simp

  

lemma [simp]: "initial_state \<sigma>  \<phi> \<Longrightarrow>  thrView \<sigma> t x = lastWr \<sigma> x"
  apply (unfold lastWr_def)
  apply (case_tac "\<exists> x ts . (x, ts) \<in> writes \<sigma>") 
  defer
  apply (metis (full_types) initial_wfs initially_write_unique lastWr_def last_write_write_on wfs_def)
  apply clarsimp
  apply (case_tac "xa = x") defer 
   apply (metis init_only_one_write initial_wfs lastWr_def last_write_write_on wfs_def)
 apply clarsimp
  apply (case_tac "(x, ts) \<in> writes_on \<sigma> x") defer 
   apply simp
  by (metis init_only_one_write initial_wfs lastWr_def last_write_write_on thrdView_of_init)

lemma init_post_inv : "init s \<Longrightarrow>  d_obs_t (state s) t f 0 \<and>  d_obs_t (state s) t d 0"
  apply (unfold init_def init_s_def  init_map_def d_obs_t_def d_obs_def) 
  by clarsimp

lemma t1_local:
  assumes "thrdsvars"
      and "wfs (state s)"
      and "prog_inv t1 ((pc s) t1) s" 
      and "prog t1 s s'"
    shows "prog_inv t1 ((pc s') t1) s'"
  using assms 
  apply (simp add: prog_def prog_inv_def)
  apply (cases "pc s t1", auto)
  apply (metis One_nat_def not_p_obs_WrX_val_pres numeral_eq_one_iff semiring_norm(86))
  using d_obs_WrX_set apply blast
  using d_obs_WrR_other  by blast

lemma t1_global :
  assumes "prog_inv t1 ((pc s) t1) s"
   and "prog_inv t2 ((pc s) t2) s"
  and "thrdsvars"
  and "prog t2 s s'"
shows  "prog_inv t1 ((pc s') t1) s'"
  using assms 
  apply (simp add: prog_inv_def prog_def)
  apply (cases "(pc s) t1", auto)
  apply (cases "(pc s) t2", auto)
  using not_pobs_RdA_pres apply blast
  using dobs_RdA_pres apply blast
  using not_pobs_RdA_pres apply blast
  using dobs_RdA_pres apply blast
  using not_pobs_RdX_pres apply blast
  using dobs_RdX_pres apply blast
  apply (cases "(pc s) t2", auto)
  using not_pobs_RdA_pres apply blast
  using dobs_RdA_pres apply blast
  using not_pobs_RdA_pres apply blast
  using dobs_RdA_pres apply blast
  using not_pobs_RdX_pres apply blast
  using dobs_RdX_pres apply blast
  apply (cases "(pc s) t2", auto)
  using dobs_RdA_pres apply blast
  using dobs_RdA_pres apply blast
  using dobs_RdX_pres by blast

(*
lemma t1_global:
  assumes "thrdsvars"
      and "prog_inv t1 ((pc s) t2) s" 
      and "prog t2 s s'"
    shows "prog_inv t1 ((pc s') t2) s'"
  using assms 
  apply (simp add: prog_inv_def prog_def)
  apply (case_tac "pc s t2", auto)
  using not_pobs_RdA_pres apply blast+
  apply (simp add: RdA_def p_obs_Rd_intro2)
  using not_pobs_RdA_pres apply blast
  using dobs_RdA_pres apply blast
  using dobs_RdX_pres by blast
*)

lemma t2_local:
  assumes "thrdsvars"
      and "wfs (state s)"
      and "prog_inv t2 ((pc s) t2) s" 
      and "prog t2 s s'"
    shows "prog_inv t2 ((pc s') t2) s'"
  using assms 
  apply (simp add: prog_def prog_inv_def)
  apply (cases "pc s t2", auto)
  using c_obs_RdA_d_obs apply blast
  using cobs_RdA_pres apply auto[1]
  using RdX_def d_obs_p_obs_agree p_obs_Rd_intro2 by fastforce


lemma t2_global :
  assumes "wfs (state s)" 
    and "prog_inv t2 ((pc s) t2) s"
   and "prog_inv t1 ((pc s) t1) s"
  and "thrdsvars"
  and "prog t1 s s'"
shows  "prog_inv t2 ((pc s') t2) s'"
  using assms 
  apply (simp add: prog_inv_def prog_def)
  apply (cases "(pc s) t2", auto)
  apply (cases "(pc s) t1", auto)
  apply (metis not_p_obs_WrX_pres not_p_obs_implies_c_obs)
  apply (metis c_obs_WrR_intro)
  apply (cases "(pc s) t1", auto)
  apply (simp add: d_obs_def d_obs_t_def)
  apply (metis dobs_WrR_pres)
  by (metis (full_types) PC.simps(9) fun_upd_other update_pc_def)



theorem final_inv:
  assumes "wfs (state s)"   
  and "thrdsvars"
  and "t \<in> {t1, t2}"
  and "t' \<in> {t1, t2}"
  and "prog_inv t ((pc s) t) s"
  and "prog_inv t' ((pc s) t') s" 
  and "prog t' s s'"
shows "prog_inv t ((pc s') t) s'"
  using assms apply (simp del: thrdsvars_def) 
  using t1_global t1_local t2_global t2_local by blast
    
end

(*
\<comment> \<open>Don't need the following two lemmas anymore\<close>
lemma init_wfs :  "init s \<Longrightarrow> wfs (state s)"
  apply (unfold init_def wfs_def init_s_def)
  using initial_wfs wfs_def by blast

lemma wfs_inv: "wfs (state s) \<Longrightarrow> prog t s s' \<Longrightarrow> wfs (state s')"
  apply (unfold wfs_def prog_def)
  apply clarsimp
  apply (case_tac "t = t1")
  apply (cases "(pc s) t")
  apply clarsimp 
  apply (metis fst_conv prod.exhaust_sel var_def wfs_def wfs_preserved)
    apply clarsimp
  apply (metis fst_conv prod.exhaust_sel var_def wfs_def wfs_preserved)
  apply clarsimp
  by (metis fst_conv prod.exhaust_sel var_def wfs_def wfs_preserved)
*)