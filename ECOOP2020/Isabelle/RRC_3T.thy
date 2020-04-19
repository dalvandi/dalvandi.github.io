theory RRC_3T
imports OpSem
begin

datatype PC =
  L1
| L2
| L3

consts t1 :: T 
consts t2 :: T
consts t3 :: T
consts x :: L
consts y :: L


definition "thrdsvars \<equiv>  y \<noteq> x \<and> t1 \<noteq> t2 \<and>
                         t1 \<noteq> t3 \<and>
                         t2 \<noteq> t3 "


record mp_state =
  pc :: "T \<Rightarrow> PC"
  state :: surrey_state
  a :: V
  b :: V
  r1 :: V
 




definition 
  "update_pc t nv pcf \<equiv> pcf (t := nv)"

definition 
  "locals_id s s' \<equiv> a s = a s' \<and> b s = b s' \<and> r1 s = r1 s'"



definition prog :: "T \<Rightarrow>  mp_state \<Rightarrow> mp_state \<Rightarrow> bool " where
"prog t s s' \<equiv> 
(
if t = t1
then
  if (pc s) t = L1
    then
      pc s' = update_pc t L2 (pc s) \<and>
      ((state s) [x := 1]\<^sub>t (state s')) \<and>
      locals_id s s'
  else
if (pc s) t = L2
then
      pc s' = update_pc t L3 (pc s) \<and>
      ((state s) [y :=\<^sup>R 1]\<^sub>t (state s')) \<and>
      locals_id s s'
else
    False
else
if t = t2
then
  if (pc s) t = L1
    then
      pc s' = update_pc t L2 (pc s) \<and>
      ((state s) [r1 s' \<leftarrow>\<^sup>A y]\<^sub>t (state s')) \<and>
      a s' = a s \<and> b s' = b s
  else
  if (pc s) t = L2
    then
      pc s' = update_pc t L3 (pc s) \<and>
      ((state s) [x := 2]\<^sub>t (state s')) \<and>
      locals_id s s'
  else
    False
else
if t = t3
then 
  if (pc s) t = L1
    then
      pc s' = update_pc t L2 (pc s) \<and>
      ((state s) [a s' \<leftarrow> x]\<^sub>t (state s')) \<and>
      r1 s' = r1 s \<and> b s' = b s
  else                                                                   
  if (pc s) t = L2
    then
      pc s' = update_pc t L3 (pc s) \<and>
      ((state s) [b s' \<leftarrow> x]\<^sub>t (state s')) \<and>
      r1 s' = r1 s \<and> a s' = a s
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
          L1 \<Rightarrow> [\<zero>\<^sub>x 1]\<^sub>0 (state s) \<and> \<not>[y \<approx>\<^sub>t' 1] (state s) \<and> ([\<zero>\<^sub>x 2]\<^sub>0  (state s) \<longrightarrow> [x =\<^sub>t 0] (state s))
        | L2 \<Rightarrow> \<not>[y \<approx>\<^sub>t' 1] (state s) \<and> ([\<zero>\<^sub>x 2]\<^sub>0  (state s) \<longrightarrow> [x =\<^sub>t 1] (state s))
        | L3 \<Rightarrow> True
    )
  else 
    if t = t2 then
      (case p of
          L1 \<Rightarrow> [\<zero>\<^sub>x 2]\<^sub>0 (state s) \<and>  [y = 1]\<^sub>t\<lparr>x = 1\<rparr> (state s)
        | L2 \<Rightarrow> (r1 s = 1 \<longrightarrow> [x =\<^sub>t 1](state s) \<and> enc_t (state s) t x 1) \<and> [\<zero>\<^sub>x 2]\<^sub>0 (state s)
        | L3 \<Rightarrow> (r1 s = 1 \<longrightarrow> [1 \<hookrightarrow>\<^sub>x 2](state s))
      )
  else 
    if t = t3 then
      (case p of
          L1 \<Rightarrow> True
        | L2 \<Rightarrow> enc_t (state s) t x (a s)
        | L3 \<Rightarrow> ((a s) \<noteq> (b s) \<longrightarrow> [(a s) \<leadsto>\<^sub>x (b s)](state s))
      )
  else
    False
"


(*initial_state \<sigma> I*)
definition init_map  :: "(L \<Rightarrow> V) \<Rightarrow> bool" where
  "init_map \<phi> \<equiv> \<phi> x = 0 \<and> \<phi> y = 0" 

definition init_s  :: "surrey_state  \<Rightarrow> bool"
  where
    "init_s ss \<equiv> \<exists> \<phi>. initial_state ss \<phi> \<and> init_map \<phi>"

definition init  :: "mp_state  \<Rightarrow> bool"
  where
    "init s \<equiv> (pc s) t1 = L1 
      \<and> (pc s) t2 = L1 \<and> (pc s) t3 = L1  \<and>
      a s = 0  \<and> b s = 0  \<and> r1 s = 0
    \<and> init_s (state s) \<and> thrdsvars"



definition "global s \<equiv> init_val (state s) x 0 \<and> init_val (state s) y 0 \<and> wfs (state s) \<and> [\<one>\<^sub>x 1] (state s) \<and> [\<one>\<^sub>x 2] (state s)"


lemmas prog_simp  =
  prog_def
  prog_inv_def
  init_def
  init_s_def
  init_map_def

lemmas mp_simps [simp]  = 
  locals_id_def
  update_pc_def 
  thrdsvars_def

lemma goal:
  assumes "prog_inv t1 L3 s"
  and "prog_inv t2 L3 s"
  and "prog_inv t3 L3 s"
  and "global s"
  and "thrdsvars"
shows "r1 s = 1 \<and> a s = 2 \<longrightarrow> b s \<noteq> 1"
  using assms
  apply(simp add: prog_inv_def global_def)
  using d_vorder_one_way pvord_to_dvord by fastforce



lemma init_global : "init s  \<Longrightarrow>  thrdsvars \<Longrightarrow> global s"
  apply (simp add: global_def init_val_def prog_simp)
  apply (elim conjE, intro conjI)
  apply(unfold writes_on_def value_def initial_state_def mo_def, simp)
    apply auto[2]
  using initial_state_def initial_wfs 
  apply blast
  apply (metis (no_types, lifting) amo_def n_not_Suc_n p_vorder_def value_def write_record.ext_inject write_record.surjective writes_on_var)
  using p_vorder_def value_def write_record.ext_inject write_record.surjective writes_on_var
  by (metis amo_def zero_neq_numeral)


lemma init_inv : "init s  \<Longrightarrow>  thrdsvars \<Longrightarrow> prog_inv t1 L1 s \<and>
                                             prog_inv t2 L1 s \<and>
                                             prog_inv t3 L1 s"
  apply(frule_tac init_global[where s=s], simp)
  apply(simp add: init_def global_def prog_inv_def init_s_def init_map_def initial_state_def)
  apply(simp_all add: value_def initial_state_def init_map_def init_val_def opsem_def)
  apply(elim conjE, intro conjI)
  apply(unfold writes_on_def)
      apply simp+
  apply safe
  apply auto[2]
      apply(simp add: c_obs_def visible_writes_def value_def p_obs_def)
  apply(unfold writes_on_def d_obs_def)
     apply(simp add: c_obs_def visible_writes_def value_def)
    apply auto
  apply(simp add: c_obs_def d_obs_t_def d_obs_def value_def lastWr_def visible_writes_def)
  apply(unfold writes_on_def)
    apply auto 
  apply (smt Collect_cong lastWr_def last_write_write_on mem_Collect_eq own_ModView snd_conv writes_on_def)
  by (metis One_nat_def null_def not_p_obs_implies_c_obs old.prod.exhaust p_obs_def prod.collapse value_def var_def visible_var write_record.select_convs(1) zero_neq_one)


lemma global_inv:
  assumes "global s"
   and "thrdsvars"
   and "prog_inv t ((pc s) t) s"
   and "prog t s s'"
   and "t = t1 \<or> t = t2 \<or> t = t3"
 shows "global s'"
  using assms
  apply(unfold global_def prog_def prog_inv_def thrdsvars_def)
  apply (elim disjE)
   apply simp+
    apply(cases "pc s t1", simp+)
  apply(intro conjI)
  using init_val_pres apply blast
  using init_val_pres apply auto[1]
  using wfs_preserved apply blast
       apply(elim conjE)
       apply (simp add: amo_intro_step no_val_def)
  apply (metis amo_Wr_diff_val_pres n_not_Suc_n numeral_2_eq_2)
    apply(cases "pc s t1", simp+)
        apply(elim conjE)
  apply(intro conjI)
  using init_val_pres apply blast
  using init_val_pres apply blast
  using wfs_preserved apply blast
  apply (metis amo_WrR_pres)
  apply (metis amo_WrR_pres)
     apply simp+
  apply (smt PC.simps(8) amo_RdA_pres amo_Wr_diff_val_pres amo_intro_step global_def init_val_pres locals_id_def n_not_Suc_n no_val_def wfs_preserved zero_neq_numeral)
  by (metis amo_RdX_pres init_val_pres wfs_preserved)




lemma t1_local :
  assumes "prog_inv t1 ((pc s) t1) s"
    and "global s"
  and "thrdsvars"
  and "prog t1 s s'"
shows  "prog_inv t1 ((pc s') t1) s'"
  using assms
  apply (simp add: prog_simp global_def)
  apply(elim conjE)
  apply(cases "pc s t1")
    apply simp+
    apply(elim conjE, intro conjI)
  using not_p_obs_WrX_diff_var_pres
  using d_obs_WrX_set  apply blast
    apply clarsimp
    apply (meson d_obs_WrX_set no_val_def p_vorder_WrX_p_vorder)
    by simp+


lemma t1_global :
  assumes "prog_inv t1 ((pc s) t1) s"
   and "global s"
   and "t = t2 \<or> t = t3"
   and "prog_inv t ((pc s) t) s"
  and "thrdsvars"
  and "prog t s s'"
shows  "prog_inv t1 ((pc s') t1) s'"
  using assms
  apply(elim disjE)
  apply(simp add: prog_simp global_def)
   apply(cases "pc s t2")
  apply(cases "pc s t1", simp)
  apply (metis no_val_RdA_pres dobs_RdA_pres not_pobs_RdA_pres)
      apply simp+
      apply(cases "pc s t1", simp)
  using dobs_RdA_pres not_pobs_RdA_pres apply blast
      apply simp
      apply(cases "pc s t1", simp)
      apply simp+
    apply(cases "pc s t1", simp)
  apply (intro conjI)
  apply (metis One_nat_def nat.inject no_val_WrX_diff_val_pres numeral_2_eq_2 zero_neq_one)
  using not_p_obs_WrX_diff_var_pres apply blast
      apply clarsimp
      apply auto
  using WrX_no_val   apply auto[2]
  using not_p_obs_WrX_diff_var_pres apply blast
  using WrX_no_val apply blast
   using not_p_obs_WrX_diff_var_pres apply blast
   using WrX_no_val apply auto[1]
  apply(simp add: prog_simp global_def)
   apply(cases "pc s t3")
     apply(cases "pc s t1", simp)
  apply (meson dobs_RdX_pres no_val_Rdx_pres no_val_def not_pobs_RdX_pres p_vorder_RdX_p_vorder)
    apply(cases "pc s t1")
        apply simp+
  apply (meson dobs_RdX_pres no_val_def not_pobs_RdX_pres p_vorder_RdX_p_vorder)
  apply auto[2]
    apply(cases "pc s t1", simp_all)
   apply (meson dobs_RdX_pres no_val_Rdx_pres no_val_def not_pobs_RdX_pres p_vorder_RdX_p_vorder)
    apply(cases "pc s t1", simp)
   apply (smt PC.simps(8) dobs_RdX_pres fun_upd_other mp_simps(2) no_val_def not_pobs_RdX_pres p_vorder_RdX_p_vorder)
   by simp+
   


lemma t2_local :
  assumes "prog_inv t2 ((pc s) t2) s"
  and "global s"
  and "thrdsvars"
  and "prog t2 s s'"
shows  "prog_inv t2 ((pc s') t2) s'"
  using assms
  apply (simp add: prog_simp global_def)
  apply(case_tac "pc s t2")
    apply simp+
    apply(elim conjE, intro conjI)
     apply(intro impI conjI)
      apply simp
  using c_obs_RdA_d_obs
  apply blast
     apply simp
  using c_obs_RdA_d_obs d_obs_enc wfs_preserved apply blast
  using amo_def amo_intro_step no_val_def zero_neq_numeral 
  using no_val_RdA_pres apply auto[1]
   apply (simp add: amo_intro_step no_val_def)
  using WrX_d_vorder no_val_def apply fastforce
  by simp




lemma t2_global :
  assumes "prog_inv t2 ((pc s) t2) s"
  and "global s" 
   and "t = t1 \<or> t = t3"
   and "prog_inv t ((pc s) t) s"
  and "thrdsvars"
  and "prog t s s'"
shows  "prog_inv t2 ((pc s') t2) s'"
  using assms
  apply(elim disjE)
    apply (simp add: prog_simp global_def)
  apply(elim conjE)
  apply(cases "pc s t2")
    apply simp+
   apply(cases "pc s t1")
      apply(cases "pc s t2", simp)
         apply(elim conjE, intro conjI)
  apply (metis One_nat_def nat.inject no_val_WrX_diff_val_pres numeral_2_eq_2 zero_neq_one)
  using amo_Wr_diff_val_pres
  using not_p_obs_WrX_diff_var_pres not_p_obs_implies_c_obs apply auto[1]
  apply simp_all
  apply (metis c_obs_WrR_intro no_val_WrR_diff_var_pres)
    apply(cases "pc s t1", simp)
  apply (metis d_obs_def d_obs_t_def n_not_Suc_n no_val_WrX_diff_val_pres numeral_2_eq_2)
   apply(cases "pc s t1", auto)
  using no_val_WrR_diff_var_pres apply force
  apply (metis dobs_WrR_pres)
  using enc_pres apply blast
  using no_val_WrR_diff_var_pres apply force
   apply(cases "pc s t1", auto)
   apply(cases "pc s t1", auto)
  apply (metis WrX_def amo_Wr_diff_val_pres amo_intro_step isWr.simps(2) no_val_def numeral_2_eq_2 opsem_def(3) p_vorder_write_pres pvord_to_dvord)
  apply (metis assms(4) assms(6) global_def global_inv numeral_1_eq_Suc_0 numeral_One opsem_def(3) p_vorder_WrX_p_vorder pvord_to_dvord thrdsvars_def)
  apply (metis amo_WrR_pres opsem_def(3) p_vorder_WrR_p_vorder pvord_to_dvord)
  apply (metis amo_WrR_pres opsem_def(3) p_vorder_WrR_p_vorder pvord_to_dvord)  
  apply (simp add: prog_simp global_def)
  apply(elim conjE)
  apply(cases "pc s t3")
    apply simp+
   apply(cases "pc s t1")
      apply(cases "pc s t2", simp)
        apply(elim conjE, intro conjI)
  using no_val_Rdx_pres apply blast
  using cobs_RdX_diff_var_pres apply blast
  apply (metis PC.simps(8) RdX_def dobs_Rd_pres enc_pres isRd.simps(1) no_val_Rdx_pres)
  using d_vorder_RdX_pres apply auto[1]
  apply(cases "pc s t2", auto)
  using no_val_Rdx_pres apply blast
  using cobs_RdX_diff_var_pres apply blast
  using no_val_Rdx_pres apply blast
  using dobs_RdX_pres apply blast
  using enc_pres apply blast
  using no_val_Rdx_pres apply blast
  using d_vorder_RdX_pres apply blast
  apply(cases "pc s t2", simp)
  using cobs_RdX_diff_var_pres no_val_Rdx_pres apply auto[1]
  apply (metis PC.simps(8) RdX_def dobs_Rd_pres enc_pres isRd.simps(1) no_val_Rdx_pres)
  using d_vorder_RdX_pres apply auto[1]
  apply(cases "pc s t2", simp)
  using cobs_RdX_diff_var_pres no_val_Rdx_pres apply auto[1]
  apply (metis PC.simps(8) RdX_def dobs_Rd_pres enc_pres isRd.simps(1) no_val_Rdx_pres)
  using d_vorder_RdX_pres by auto



lemma t3_local :
  assumes "prog_inv t3 ((pc s) t3) s"
  and "global s"
  and "thrdsvars"
  and "prog t3 s s'"
shows  "prog_inv t3 ((pc s') t3) s'"
  using assms
  apply (simp add: prog_simp global_def)
  apply(case_tac "pc s t3")
    apply simp+
  using enc_RdX_intro apply blast
   apply simp
   apply(elim conjE)
  defer
   apply simp
    using enc_Rdx_p_vorder
    by blast

lemma t3_global:
  assumes "prog_inv t3 ((pc s) t3) s"
   and "t = t1 \<or> t = t2"
   and "prog_inv t ((pc s) t) s"
  and "thrdsvars"
  and "prog t s s'"
shows  "prog_inv t3 ((pc s') t3) s'"
  using assms
  apply(elim disjE)
   apply (simp_all add: prog_simp global_def)
   apply(case_tac "pc s t1")
   apply(case_tac "pc s t3")
  apply simp+
  using enc_pres apply blast
  apply clarsimp
  using p_vorder_WrX_p_vorder
  apply blast
   apply(case_tac "pc s t3")
      apply simp+
  using enc_pres apply blast
    apply simp+
  apply(elim conjE, intro impI, simp)
  using p_vorder_WrR_p_vorder apply blast
  apply simp
   apply(case_tac "pc s t2")
   apply(case_tac "pc s t3")
  apply simp+
  using enc_pres apply blast
  apply clarsimp
  using p_vorder_RdA_p_vorder apply blast
   apply(case_tac "pc s t3")
     apply simp+
  using enc_pres apply blast
  apply simp
  using p_vorder_WrX_p_vorder apply blast
  by simp



theorem final_inv:
  assumes "wfs (state s)"   
  and "global s"
  and "thrdsvars"
  and "t \<in> {t1, t2, t3}"
  and "t' \<in> {t1, t2, t3}"
  and "prog_inv t ((pc s) t) s"
  and "prog_inv t' ((pc s) t') s" 
  and "prog t' s s'"
shows "prog_inv t ((pc s') t) s'"
  using assms apply (simp del: thrdsvars_def) 
  by (meson t1_global t1_local t2_global t2_local t3_global t3_local)



end