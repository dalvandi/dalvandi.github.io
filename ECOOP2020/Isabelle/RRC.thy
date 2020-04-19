theory RRC
imports OpSem
begin

datatype PC =
  L1
| L2
| L3

consts t1 :: T 
consts t2 :: T
consts t3 :: T
consts t4 :: T
consts x :: L


definition "thrdsvars \<equiv>  t1 \<noteq> t2 \<and>
                         t1 \<noteq> t3 \<and>
                         t1 \<noteq> t4 \<and>
                         t2 \<noteq> t3 \<and>
                         t2 \<noteq> t4 \<and>
                         t3 \<noteq> t4"


record mp_state =
  pc :: "T \<Rightarrow> PC"
  state :: surrey_state
  a :: V
  b :: V
  c :: V
  d :: V





definition 
  "update_pc t nv pcf \<equiv> pcf (t := nv)"

definition 
  "locals_id s s' \<equiv> a s = a s' \<and> b s = b s' \<and> c s = c s' \<and> d s = d s'"


lemmas mp_simps [simp] = 
  locals_id_def
  update_pc_def 
  thrdsvars_def


definition prog :: "T \<Rightarrow>  mp_state \<Rightarrow> mp_state \<Rightarrow> bool " where
"prog t s s' \<equiv> 
(
if t = t1
then
  if (pc s) t = L1
    then
      pc s = update_pc t L2 (pc s) \<and>
      ((state s) [x := 1]\<^sub>t (state s')) \<and> 
      locals_id s s'
  else
    False
else
if t = t2
then
  if (pc s) t = L1
    then
      pc s' = update_pc t L2 (pc s) \<and>
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
      (state s) [a s' \<leftarrow> x]\<^sub>t (state s')  \<and>
      b s' = b s \<and> c s' = c s \<and> d s' = d s 
  else                                                                   
  if (pc s) t = L2
    then
      pc s' = update_pc t L3 (pc s) \<and>                     
      (state s) [b s' \<leftarrow> x]\<^sub>t (state s') \<and>
      a s' = a s \<and> c s' = c s \<and> d s' = d s 
  else                                                                   
    False                                                                   
else                                                                    
if t = t4
then 
  if (pc s) t = L1
    then
      pc s' = update_pc t L2 (pc s) \<and>                     
      (state s) [c s' \<leftarrow> x]\<^sub>t (state s') \<and>
      a s' = a s \<and> b s' = b s \<and> d s' = d s 
  else                                                                   
  if (pc s) t = L2
    then
      pc s' = update_pc t L3 (pc s) \<and>                     
      (state s) [d s' \<leftarrow> x]\<^sub>t (state s') \<and>
      a s' = a s \<and> b s' = b s \<and> c s' = c s
  else                                                                   
    False  
else
  False
)"


definition prog_inv :: "T \<Rightarrow> PC \<Rightarrow> mp_state \<Rightarrow> bool " where
"prog_inv t p s \<equiv> 
  if t = t1
  then
    (case p of
          L1 \<Rightarrow> [\<zero>\<^sub>x 1]\<^sub>0 (state s) \<and> [\<one>\<^sub>x 1] (state s)  \<comment> \<open>\<not> p_vorder (state s) 0 x 1\<close>  
        | _ \<Rightarrow> True

    )
  else 
    if t = t2 then
      (case p of
          L1 \<Rightarrow> [\<zero>\<^sub>x 2]\<^sub>0 (state s) \<and> [\<one>\<^sub>x 2] (state s)
        | _ \<Rightarrow> True
      )
  else 
    if t = t3 then
      (case p of
          L1 \<Rightarrow> init_val (state s) x 0 \<and>  [\<one>\<^sub>x 1] (state s) \<and> [\<one>\<^sub>x 2] (state s)
        | L2 \<Rightarrow> init_val (state s) x 0 \<and> enc_t (state s) t x (a s) \<and>  (a s = 1 \<longrightarrow> [\<one>\<^sub>x (a s)] (state s)) \<and> [\<one>\<^sub>x 2] (state s)
        | L3 \<Rightarrow> (a s \<noteq> b s \<longrightarrow> [(a s) \<leadsto>\<^sub>x (b s)] (state s)) \<and>  (a s = 1 \<longrightarrow> [\<one>\<^sub>x (a s)] (state s)) \<and> (b s = 2 \<longrightarrow> [\<one>\<^sub>x (b s)] (state s))
      )
  else
    if t = t4 then
      (case p of
          L1 \<Rightarrow> init_val (state s) x 0 \<and>  [\<one>\<^sub>x 1] (state s) \<and> [\<one>\<^sub>x 2] (state s)
        | L2 \<Rightarrow> init_val (state s) x 0 \<and>  enc_t (state s) t x (c s) \<and>  (c s = 2 \<longrightarrow> [\<one>\<^sub>x (c s)] (state s)) \<and> [\<one>\<^sub>x 1] (state s)
        | L3 \<Rightarrow> (c s \<noteq> d s \<longrightarrow> [(c s) \<leadsto>\<^sub>x (d s)] (state s)) \<and>  (c s = 2 \<longrightarrow> [\<one>\<^sub>x (c s)] (state s)) \<and> (d s = 1 \<longrightarrow> [\<one>\<^sub>x (d s)] (state s))
      )
  else
    False
"



(*initial_state \<sigma> I*)
definition init_map  :: "(L \<Rightarrow> V) \<Rightarrow> bool" where
  "init_map \<phi> \<equiv> \<phi> x = 0" 

definition init_s  :: "surrey_state  \<Rightarrow> bool"
  where
    "init_s ss \<equiv> \<exists> \<phi>. initial_state ss \<phi> \<and> init_map \<phi>"

definition init  :: "mp_state  \<Rightarrow> bool"
  where
    "init s \<equiv> (pc s) t1 = L1 
      \<and> (pc s) t2 = L1 \<and> (pc s) t3 = L1 \<and> (pc s) t4 = L1  \<and>
      a s = 0  \<and> b s = 0  \<and> c s = 0 \<and> d s = 0 
    \<and> init_s (state s) \<and> thrdsvars"

lemma init_inv : "init s \<Longrightarrow> thrdsvars \<Longrightarrow> prog_inv t1 L1 s \<and>
                                           prog_inv t2 L1 s \<and>
                                           prog_inv t3 L1 s \<and>
                                           prog_inv t4 L1 s"
  apply(intro conjI)
  apply(unfold init_def prog_inv_def thrdsvars_def init_val_def init_s_def writes_on_def)
  apply(simp_all add: value_def initial_state_def init_map_def init_val_def opsem_def)
  apply(unfold writes_on_def)
  by auto


lemma t1_local :
  assumes "prog_inv t1 ((pc s) t1) s"
  and "thrdsvars"
  and "prog t1 s s'"
shows  "prog_inv t1 ((pc s') t1) s'"
  using assms
  apply(simp add: prog_def)
  by (metis PC.distinct(1) fun_upd_same update_pc_def)


lemma t1_global :
  assumes "prog_inv t1 ((pc s) t1) s"
   and "t = t2 \<or> t = t3 \<or> t = t4"
   and "prog_inv t ((pc s) t) s"
  and "thrdsvars"
  and "prog t s s'"
shows  "prog_inv t1 ((pc s') t1) s'"
  using assms
  apply(elim disjE, simp)
  apply(unfold prog_inv_def prog_def thrdsvars_def  update_pc_def)
    apply(cases "pc s t2", auto)
  apply(cases "pc s t1", auto)
  apply (metis One_nat_def nat.inject no_val_WrX_diff_val_pres numeral_2_eq_2 zero_neq_one)
  apply (metis amo_Wr_diff_val_pres n_not_Suc_n numeral_2_eq_2)
  apply(cases "pc s t1", auto)
  apply(cases "pc s t3", auto)
  apply (metis RdX_def init_val_pres isRd.simps(1) no_val_def read_pres_not_p_vorder)
  using amo_intro_step no_val_def apply blast
  apply (metis RdX_def init_val_pres isRd.simps(1) no_val_def read_pres_not_p_vorder)
  using amo_intro_step no_val_def apply blast
  apply(cases "pc s t3", auto)+
  apply(cases "pc s t1", auto)
  apply(cases "pc s t4", auto)
  apply (metis RdX_def init_val_pres isRd.simps(1) no_val_def read_pres_not_p_vorder)
  using amo_intro_step no_val_def apply blast
  apply (metis RdX_def init_val_pres isRd.simps(1) no_val_def read_pres_not_p_vorder)
  using amo_intro_step no_val_def apply blast
  apply (metis RdX_def init_val_pres isRd.simps(1) no_val_def read_pres_not_p_vorder)
  using amo_intro_step no_val_def apply blast
  apply (metis PC.simps(8) fun_upd_def)
  by (metis PC.simps(9) fun_upd_def)+


lemma t2_local :
  assumes "prog_inv t2 ((pc s) t2) s"
  and "thrdsvars"
  and "prog t2 s s'"
shows  "prog_inv t2 ((pc s') t2) s'"
  using assms
  apply(unfold prog_inv_def prog_def thrdsvars_def update_pc_def)
  apply(cases "pc s t2") 
    apply simp
   apply(elim conjE)
  apply simp
  by auto


lemma t2_global :
  assumes "prog_inv t2 ((pc s) t2) s"
   and "t = t1 \<or> t = t3 \<or> t = t4"
   and "prog_inv t ((pc s) t) s"
  and "thrdsvars"
  and "prog t s s'"
shows  "prog_inv t2 ((pc s') t2) s'"
  using assms
  apply(elim disjE, simp)
  apply(unfold prog_inv_def prog_def thrdsvars_def  update_pc_def)
  apply clarsimp+
  apply(cases "pc s t1", auto)
  apply(cases "pc s t2", simp)
  apply (metis PC.distinct(1) fun_upd_same)
  apply simp+
  apply (metis PC.distinct(1) fun_upd_same)
    apply (metis PC.distinct(1) fun_upd_same)
    apply(cases "pc s t3", auto)
      apply(cases "pc s t2", simp)
       apply (intro conjI)
  apply (metis RdX_def init_val_pres isRd.simps(1) no_val_def read_pres_not_p_vorder)
  using amo_intro_step no_val_def zero_neq_numeral apply blast
  apply (simp add: amo_intro_step)
  using read_pres_not_p_vorder  
  apply simp
      apply(cases "pc s t2", simp_all)
    apply (intro conjI)
  apply (metis RdX_def init_val_pres isRd.simps(1) no_val_def read_pres_not_p_vorder)
  using amo_intro_step no_val_def zero_neq_numeral apply blast
      apply(cases "pc s t2", simp_all)
    apply (intro conjI)
  apply (metis RdX_def init_val_pres isRd.simps(1) no_val_def read_pres_not_p_vorder)
  using amo_intro_step no_val_def zero_neq_numeral apply blast
   apply(cases "pc s t2", simp)
    apply(cases "pc s t4", auto)
  apply (metis RdX_def init_val_pres isRd.simps(1) no_val_def read_pres_not_p_vorder)
  using amo_intro_step no_val_def zero_neq_numeral apply blast
  apply (metis RdX_def init_val_pres isRd.simps(1) no_val_def read_pres_not_p_vorder)
  using amo_intro_step no_val_def zero_neq_numeral apply blast
  apply (metis PC.simps(8) Suc_1 fun_upd_def)
  by (metis PC.simps(9) Suc_1 fun_upd_def)


lemma t3_local :
  assumes "prog_inv t3 ((pc s) t3) s"
  and "thrdsvars"
  and "prog t3 s s'"
shows  "prog_inv t3 ((pc s') t3) s'"
  using assms
  apply(unfold prog_inv_def prog_def thrdsvars_def update_pc_def)
  apply(cases " pc s t3")
    apply simp
  apply(elim conjE)
    apply(intro conjI)
  using init_val_pres apply blast
  using enc_RdX_intro apply blast
  apply (metis RdX_def amo_def isRd.simps(1) read_pres_not_p_vorder)
  apply (metis RdX_def amo_def isRd.simps(1) read_pres_not_p_vorder)
   apply simp
   apply(elim conjE)
    apply(intro conjI)
  using enc_read_p_vorder 
  apply (metis RdX_def avar.simps(1) enc_pvord_step isRd.simps(1) rd_val.simps(1))
 using amo_read_pres
  apply (metis RdX_def isRd.simps(1))
  apply (metis RdX_def amo_read_pres isRd.simps(1))
  by auto


lemma t3_global:
  assumes "prog_inv t3 ((pc s) t3) s"
   and "t = t1 \<or> t = t2 \<or> t = t4"
   and "prog_inv t ((pc s) t) s"
  and "thrdsvars"
  and "prog t s s'"
shows  "prog_inv t3 ((pc s') t3) s'"
  using assms
  apply(elim disjE, simp)
  apply(unfold prog_inv_def prog_def thrdsvars_def  update_pc_def)
  apply clarsimp
    apply(cases "pc s t1", auto)
    apply(cases "pc s t3")
      apply simp
      apply(case_tac "pc s' t3 \<noteq> pc s t3")
  apply (metis PC.distinct(1) fun_upd_def)
      apply simp
      apply(intro conjI)
  using init_val_pres apply blast 
  apply (metis PC.distinct(1) fun_upd_def)
        apply (metis PC.distinct(1) fun_upd_same)
        apply (metis PC.distinct(1) fun_upd_def)
        apply (metis PC.distinct(1) fun_upd_same update_pc_def)
    apply(cases "pc s t2", auto)
    apply(cases "pc s t3")
      apply simp
          apply(case_tac "pc s' t3 \<noteq> pc s t3")
       apply simp+
      apply(intro conjI)
  using init_val_pres apply blast
  using amo_pres_step_wr 
      apply (metis WrX_def isWr.simps(2) n_not_Suc_n numeral_2_eq_2 option.inject wr_val.simps(1))
  using amo_intro_step no_val_def zero_neq_numeral apply blast
    apply (simp add: amo_intro_step)
  apply (metis WrX_def amo_intro_step amo_pres_step_wr enc_pres init_val_pres isWr.simps(2) no_val_def option.inject wr_val.simps(1) zero_neq_numeral)
  apply (metis (no_types, lifting) PC.simps(9) WrX_def amo_intro_step amo_pres_step_wr isWr.simps(2) no_val_def option.inject p_vorder_write_pres wr_val.simps(1) zero_neq_numeral)
  apply(cases "pc s t3", auto)
  apply(cases "pc s t4", auto)
  apply (meson amo_def init_val_pres isRd.simps(1) read_pres_not_p_vorder)
  apply(cases "pc s t4", auto)
  apply (metis RdX_def amo_read_pres isRd.simps(1))
  apply (metis RdX_def amo_def isRd.simps(1) read_pres_not_p_vorder)
  using init_val_pres apply blast
  apply (metis RdX_def amo_read_pres isRd.simps(1))
  apply (metis RdX_def amo_def isRd.simps(1) read_pres_not_p_vorder)
  apply(cases "pc s t4", auto)
  using init_val_pres apply blast
  using enc_pres apply blast
  apply (metis RdX_def amo_def isRd.simps(1) read_pres_not_p_vorder)
  using init_val_pres apply blast
  using enc_pres apply blast
  apply (metis RdX_def amo_def isRd.simps(1) read_pres_not_p_vorder)
  apply(cases "pc s t4", auto)
  using init_val_pres apply blast
  using enc_pres apply blast
  apply (metis RdX_def amo_def isRd.simps(1) read_pres_not_p_vorder)
  apply (metis RdX_def amo_def isRd.simps(1) read_pres_not_p_vorder)
  using init_val_pres apply blast
  using enc_pres apply blast
  apply (metis RdX_def amo_def isRd.simps(1) read_pres_not_p_vorder)
  apply (metis RdX_def amo_def isRd.simps(1) read_pres_not_p_vorder)
  apply(cases "pc s t4", auto)
  apply(cases "pc s t4", auto)
  apply (metis RdX_def amo_def isRd.simps(1) read_pres_not_p_vorder)
  apply (metis RdX_def amo_def isRd.simps(1) read_pres_not_p_vorder)
  apply(cases "pc s t4", auto)
  apply (metis RdX_def amo_def isRd.simps(1) read_pres_not_p_vorder)
  apply (metis RdX_def amo_def isRd.simps(1) read_pres_not_p_vorder)
  apply(cases "pc s t4", auto)
  apply (metis RdX_def amo_def isRd.simps(1) read_pres_not_p_vorder)
  apply(cases "pc s t4", auto)
  apply (metis RdX_def amo_def isRd.simps(1) read_pres_not_p_vorder)
  apply (metis RdX_def amo_def isRd.simps(1) read_pres_not_p_vorder)
  apply(cases "pc s t4", auto)
  apply (metis RdX_def amo_def isRd.simps(1) read_pres_not_p_vorder)
  apply (metis RdX_def amo_def isRd.simps(1) read_pres_not_p_vorder)
  apply(cases "pc s t4", auto)
  apply (metis RdX_def isRd.simps(1) read_pres_p_vorder)
  apply (metis RdX_def isRd.simps(1) read_pres_p_vorder)
  apply (metis RdX_def isRd.simps(1) read_pres_p_vorder)
    apply(cases "pc s t4", auto)
  apply (metis RdX_def isRd.simps(1) read_pres_p_vorder)
  apply (metis RdX_def amo_read_pres isRd.simps(1))
  apply (metis RdX_def isRd.simps(1) read_pres_p_vorder)
  apply (metis RdX_def amo_read_pres isRd.simps(1))
    apply(cases "pc s t4", auto)
  apply (metis RdX_def isRd.simps(1) read_pres_p_vorder)
  apply (metis RdX_def amo_read_pres isRd.simps(1))
  apply (metis RdX_def isRd.simps(1) read_pres_p_vorder)
  apply (metis RdX_def amo_read_pres isRd.simps(1))
  apply (metis RdX_def isRd.simps(1) read_pres_p_vorder)
  apply (metis RdX_def amo_read_pres isRd.simps(1))
  apply(cases "pc s t4", auto)
  apply (metis RdX_def isRd.simps(1) read_pres_p_vorder)
  apply (metis RdX_def amo_read_pres isRd.simps(1))
  apply (metis RdX_def amo_read_pres isRd.simps(1))
  apply (metis RdX_def isRd.simps(1) read_pres_p_vorder)
  apply (metis RdX_def amo_read_pres isRd.simps(1))
  by (metis RdX_def amo_read_pres isRd.simps(1))  
  


lemma t4_local :
  assumes "prog_inv t4 ((pc s) t4) s"
  and "thrdsvars"
  and "prog t4 s s'"
shows  "prog_inv t4 ((pc s') t4) s'"
  using assms
  apply(unfold prog_inv_def prog_def thrdsvars_def update_pc_def)
  apply(cases " pc s t4")
    apply simp
  apply(elim conjE)
    apply(intro conjI)
  using init_val_pres apply blast
  using enc_RdX_intro apply blast
    apply (metis RdX_def amo_read_pres isRd.simps(1))
    apply (metis RdX_def amo_read_pres isRd.simps(1))
   apply simp
  apply(elim conjE)
   apply(intro conjI impI)
  apply (metis RdX_def avar.simps(1) enc_pvord_step isRd.simps(1) rd_val.simps(1))
  apply (metis RdX_def amo_read_pres isRd.simps(1))
  apply (metis RdX_def amo_read_pres isRd.simps(1))
  by auto


lemma t4_global:
  assumes "prog_inv t4 ((pc s) t4) s"
   and "t = t1 \<or> t = t2 \<or> t = t3"
   and "prog_inv t ((pc s) t) s"
  and "thrdsvars"
  and "prog t s s'"
shows  "prog_inv t4 ((pc s') t4) s'"
  using assms
  apply(elim disjE, simp)
  apply(unfold prog_inv_def prog_def thrdsvars_def  update_pc_def)
  apply clarsimp
    apply(cases "pc s t1", auto)
    apply(cases "pc s t4")
      apply simp
      apply(case_tac "pc s' t4 \<noteq> pc s t4")
  apply (metis PC.distinct(1) fun_upd_def)
      apply simp
      apply(intro conjI)
  using init_val_pres apply blast
  apply (metis PC.distinct(1) fun_upd_same)
        apply (metis PC.distinct(1) fun_upd_same)
        apply (metis PC.distinct(1) fun_upd_def)
        apply (metis PC.distinct(1) fun_upd_same update_pc_def)
    apply(cases "pc s t2", auto)
    apply(cases "pc s t4")
      apply simp
          apply(case_tac "pc s' t4 \<noteq> pc s t4")
       apply simp+
      apply(intro conjI)
  using init_val_pres apply blast
  using amo_pres_step_wr 
  apply (metis WrX_def isWr.simps(2) n_not_Suc_n numeral_2_eq_2 option.inject wr_val.simps(1))
  using amo_intro_step no_val_def zero_neq_numeral apply blast
     apply (simp add: amo_intro_step)
  using enc_pres init_val_pres apply auto[1]
  apply (simp add: amo_intro_step no_val_def)
  apply (metis WrX_def amo_pres_step_wr isWr.simps(2) n_not_Suc_n numeral_2_eq_2 option.inject wr_val.simps(1))
   apply (simp add: amo_intro_step)+
   apply(case_tac "pc s t4", auto)
  using amo_intro_step no_val_def zero_neq_numeral apply blast+
  apply (metis WrX_def amo_pres_step_wr isWr.simps(2) n_not_Suc_n numeral_2_eq_2 option.inject wr_val.simps(1))
  apply (metis WrX_def isWr.simps(2) p_vorder_write_pres)
  using amo_intro_step no_val_def zero_neq_numeral apply blast
  apply (metis WrX_def isWr.simps(2) p_vorder_write_pres)
  using amo_intro_step no_val_def zero_neq_numeral apply blast
  apply (metis WrX_def amo_pres_step_wr isWr.simps(2) n_not_Suc_n numeral_2_eq_2 option.inject wr_val.simps(1))
  apply(case_tac "pc s t4", auto)
  apply(case_tac "pc s t3", auto)
  using init_val_pres apply blast
  apply (metis RdX_def amo_def isRd.simps(1) read_pres_not_p_vorder)
  apply (metis RdX_def amo_def isRd.simps(1) read_pres_not_p_vorder)
  using init_val_pres apply blast
  apply (metis RdX_def amo_read_pres isRd.simps(1))
  apply (metis RdX_def amo_read_pres isRd.simps(1))
  apply(case_tac "pc s t3", auto)
  using init_val_pres apply blast
  using enc_pres apply blast
  apply (metis RdX_def amo_def isRd.simps(1) read_pres_not_p_vorder)
  using init_val_pres apply blast
  using enc_pres apply blast
  apply (metis RdX_def amo_read_pres isRd.simps(1))
  apply(case_tac "pc s t3", auto)
  using init_val_pres apply blast
  using enc_pres apply blast
  apply (metis RdX_def amo_def isRd.simps(1) read_pres_not_p_vorder)
  apply (metis RdX_def amo_def isRd.simps(1) read_pres_not_p_vorder)
  using init_val_pres apply blast
  using enc_pres apply blast
  apply (metis RdX_def amo_read_pres isRd.simps(1))
  apply (metis RdX_def amo_read_pres isRd.simps(1))
  apply(case_tac "pc s t3", auto)
  apply(case_tac "pc s t3", auto)
  apply (metis RdX_def amo_def isRd.simps(1) read_pres_not_p_vorder)
  apply (metis RdX_def amo_read_pres isRd.simps(1))
  apply(case_tac "pc s t3", auto)
  apply (metis RdX_def amo_def isRd.simps(1) read_pres_not_p_vorder)
  apply (metis RdX_def amo_read_pres isRd.simps(1))
  apply (metis RdX_def amo_read_pres isRd.simps(1))
  apply(case_tac "pc s t3", auto)
  apply (metis RdX_def amo_def isRd.simps(1) read_pres_not_p_vorder)
  apply (metis RdX_def amo_def isRd.simps(1) read_pres_not_p_vorder)
  apply (metis RdX_def amo_read_pres isRd.simps(1))
  apply (metis RdX_def amo_read_pres isRd.simps(1))
  apply(case_tac "pc s t3", auto)
  apply (metis RdX_def isRd.simps(1) read_pres_p_vorder)
  apply (metis RdX_def isRd.simps(1) read_pres_p_vorder)
  apply (metis RdX_def isRd.simps(1) read_pres_p_vorder)
  apply(case_tac "pc s t3", auto)
  apply (metis RdX_def isRd.simps(1) read_pres_p_vorder)
  apply (metis RdX_def amo_def isRd.simps(1) read_pres_not_p_vorder)
  apply (metis RdX_def isRd.simps(1) read_pres_p_vorder)
  apply (metis RdX_def amo_def isRd.simps(1) read_pres_not_p_vorder)
  apply(case_tac "pc s t3", auto)
  apply (metis RdX_def isRd.simps(1) read_pres_p_vorder)
  apply (metis RdX_def amo_def isRd.simps(1) read_pres_not_p_vorder)
  apply (metis RdX_def isRd.simps(1) read_pres_p_vorder)
  apply (metis RdX_def amo_def isRd.simps(1) read_pres_not_p_vorder)
  apply (metis RdX_def isRd.simps(1) read_pres_p_vorder)
  apply (metis RdX_def amo_def isRd.simps(1) read_pres_not_p_vorder)
  apply(case_tac "pc s t3", auto)
  apply (metis RdX_def isRd.simps(1) read_pres_p_vorder)
  apply (metis RdX_def amo_def isRd.simps(1) read_pres_not_p_vorder)
  apply (metis RdX_def amo_def isRd.simps(1) read_pres_not_p_vorder)
  apply (metis RdX_def isRd.simps(1) read_pres_p_vorder)
  apply (metis RdX_def amo_def isRd.simps(1) read_pres_not_p_vorder)
  by (metis RdX_def amo_def isRd.simps(1) read_pres_not_p_vorder)






lemma sub_goal_t3:
  assumes "prog_inv t3 L3 s"
  and "thrdsvars"
  shows "(a s) = 1 \<and> (b s) = 2 \<longrightarrow> d_vorder (state s) (a s) x (b s)"
  using assms
  apply(simp add: prog_inv_def)
  using pvord_to_dvord
  by fastforce
 

lemma sub_goal_t4:
  assumes "prog_inv t4 L3 s"
  and "thrdsvars"
  shows "(c s) = 2 \<and> (d s) = 1 \<longrightarrow> d_vorder (state s) (c s) x (d s)"
  using assms
  apply(simp add: prog_inv_def)
  using pvord_to_dvord
  by fastforce



lemma goal:
  assumes "prog_inv t1 L3 s"
  and "prog_inv t2 L3 s"
  and "prog_inv t3 L3 s"
  and "prog_inv t4 L3 s"
  and "thrdsvars"
shows "a s = 1 \<and> b s = 2 \<and> c s = 2 \<longrightarrow> d s \<noteq> 1"
  using assms apply simp
  apply(frule_tac sub_goal_t3[where s=s], simp)
  apply(drule_tac sub_goal_t4[where s=s])
  apply(simp add: prog_inv_def)
  using d_vorder_one_way by auto


theorem final_inv:
  assumes "wfs (state s)"   
  and "thrdsvars"
  and "t \<in> {t1, t2, t3, t4}"
  and "t' \<in> {t1, t2, t3, t4}"
  and "prog_inv t ((pc s) t) s"
  and "prog_inv t' ((pc s) t') s" 
  and "prog t' s s'"
shows "prog_inv t ((pc s') t) s'"
  using assms apply (simp del: thrdsvars_def) 
  by (meson t1_global t1_local t2_global t2_local t3_global t3_local t4_global t4_local)

end