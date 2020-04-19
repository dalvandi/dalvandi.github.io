theory RRC_2T
imports OpSem
begin

datatype PC =
  L1
| L2
| L3

consts t1 :: T 
consts t2 :: T
consts x :: L


definition "thrdsvars \<equiv>  t1 \<noteq> t2 "


record mp_state =
  pc :: "T \<Rightarrow> PC"
  state :: surrey_state
  a :: V
  b :: V






definition 
  "update_pc t nv pcf \<equiv> pcf (t := nv)"




definition prog :: "T \<Rightarrow>  mp_state \<Rightarrow> mp_state \<Rightarrow> bool " where
"prog t s s' \<equiv> 
(
if t = t1
then
  if (pc s) t = L1
    then
      pc s' = update_pc t L2 (pc s) \<and>
      (state s) [x := 1]\<^sub>t (state s') \<and>
      a s' = a s \<and> b s' = b s 
  
else
if (pc s) t = L2
then
      pc s' = update_pc t L3 (pc s) \<and>
      (state s) [x := 2]\<^sub>t (state s') \<and>
      a s' = a s \<and> b s' = b s 
else
    False
else
if t = t2
then
  if (pc s) t = L1
    then
      pc s' = update_pc t L2 (pc s) \<and>
      (state s) [a s' \<leftarrow> x]\<^sub>t (state s') \<and>
      b s' = b s 
  else
  if (pc s) t = L2
    then
      pc s' = update_pc t L3 (pc s) \<and>
      (state s) [b s' \<leftarrow> x]\<^sub>t (state s') \<and>
      a s' = a s 
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
          L1 \<Rightarrow> [\<zero>\<^sub>x 1]\<^sub>0 (state s) \<and> [\<one>\<^sub>x 1] (state s) \<and> [\<zero>\<^sub>x 2]\<^sub>0 (state s) \<and>  [\<one>\<^sub>x 2] (state s)  
        | L2 \<Rightarrow> [\<zero>\<^sub>x 2]\<^sub>0 (state s) \<and> enc_t (state s) t x 1 \<and> [\<one>\<^sub>x 1] (state s) \<and> [\<one>\<^sub>x 2] (state s)
        | L3 \<Rightarrow> [\<one>\<^sub>x 1] (state s) \<and> [\<one>\<^sub>x 2] (state s) \<and>  [1 \<hookrightarrow>\<^sub>x 2] (state s)

    )
  else 
    if t = t2 then
      (case p of
          L1 \<Rightarrow> init_val (state s) x 0 \<and> [\<one>\<^sub>x 1] (state s) \<and>  [\<one>\<^sub>x 2] (state s)
        | L2 \<Rightarrow> init_val (state s) x 0 \<and> enc_t (state s) t x (a s)
        | L3 \<Rightarrow> (a s \<noteq> b s \<longrightarrow> [(a s) \<leadsto>\<^sub>x (b s)] (state s))
      )
  else 
    False
"


lemma goal:
  assumes "prog_inv t1 L3 s"
  and "prog_inv t2 L3 s"
  and "thrdsvars"
shows "a s = 2 \<longrightarrow> b s \<noteq> 1"
  using assms
  apply(simp add: prog_inv_def thrdsvars_def)
  apply(elim conjE)
  apply(case_tac " a s = 2", simp)
   defer
  apply simp
  apply(case_tac "b s \<noteq> 0")
  apply(case_tac "b s \<noteq> Suc 0")
  apply(case_tac "b s \<noteq> 2")
     apply simp
    apply simp
  apply(elim impE)
    apply simp
  apply(unfold opsem_def)
  apply (metis diff_self diff_strict_mono less_numeral_extra(3))
  by linarith


(*initial_state \<sigma> I*)
definition init_map  :: "(L \<Rightarrow> V) \<Rightarrow> bool" where
  "init_map \<phi> \<equiv> \<phi> x = 0" 

definition init_s  :: "surrey_state  \<Rightarrow> bool"
  where
    "init_s ss \<equiv> \<exists> \<phi>. initial_state ss \<phi> \<and> init_map \<phi>"

definition init  :: "mp_state  \<Rightarrow> bool"
  where
    "init s \<equiv> (pc s) t1 = L1 
      \<and> (pc s) t2 = L1 \<and> 
      a s = 0  \<and> b s = 0  
    \<and> init_s (state s) \<and> thrdsvars"


lemma init_inv : "init s \<Longrightarrow> thrdsvars \<Longrightarrow> prog_inv t1 L1 s \<and>
                                           prog_inv t2 L1 s"
  apply(simp add: init_def prog_inv_def thrdsvars_def opsem_def)
  apply(cases "pc s t1")
  apply simp
  apply(elim conjE)
  apply (intro conjI)
  apply(unfold  value_def init_s_def init_map_def initial_state_def writes_on_def init_val_def)
  by clarsimp+  


lemma t1_local :
  assumes "prog_inv t1 ((pc s) t1) s"
  and "thrdsvars"
  and "prog t1 s s'"
shows  "prog_inv t1 ((pc s') t1) s'"
  using assms
  apply(unfold prog_inv_def prog_def thrdsvars_def  update_pc_def)
  apply simp
  apply(cases "(pc s) t1")
    apply simp
  apply(intro conjI, elim conjE)
  using enc_write_intro
  apply (metis WrX_def init_val_pres isWr.simps(2) n_not_Suc_n no_val_def not_pvorder_pres_step_wr numeral_2_eq_2 option.inject wr_val.simps(1))
  apply(elim conjE)
  apply (metis WrX_def avar.simps(2) enc_write_intro isWr.simps(2) wr_val.simps(1))
  apply (elim conjE)
  using amo_intro_step no_val_def apply blast
    apply (elim conjE)
  using amo_intro_step no_val_def zero_neq_numeral apply blast  
  apply (simp add: amo_intro_step)
   apply(cases "(pc s) t1", auto)
  apply (metis One_nat_def amo_Wr_diff_val_pres nat.inject numeral_2_eq_2 zero_neq_one)
  using amo_intro_step no_val_def zero_neq_numeral apply blast
  by (metis WrX_def avar.simps(2) d_vorder_intro_w isWr.simps(2) n_not_Suc_n no_val_def numeral_2_eq_2 wr_val.simps(1) zero_neq_numeral)

 
lemma t1_global :
  assumes "prog_inv t1 ((pc s) t1) s"
      and "prog_inv t2 ((pc s) t2) s"
      and "thrdsvars"
      and "prog t2 s s'"
    shows "prog_inv t1 ((pc s') t1) s'"
  using assms
  apply(unfold prog_inv_def prog_def thrdsvars_def  update_pc_def)
  apply clarsimp
  apply(cases "pc s t2", auto)
   apply(cases "pc s t1")
  apply simp
     apply (intro conjI)
  apply (metis RdX_def init_val_pres isRd.simps(1) no_val_def read_pres_not_p_vorder)
  using amo_intro_step no_val_def apply blast
  apply (metis RdX_def init_val_pres isRd.simps(1) no_val_def read_pres_not_p_vorder)
  apply (simp add: amo_intro_step no_val_def)
  apply(cases "pc s t1", auto)
  apply (metis RdX_def init_val_pres isRd.simps(1) no_val_def read_pres_not_p_vorder)
  using enc_pres apply blast
  apply (metis RdX_def amo_read_pres isRd.simps(1))
  using amo_intro_step no_val_def zero_neq_numeral apply blast
  apply (metis RdX_def amo_read_pres isRd.simps(1))
    apply (metis RdX_def amo_def isRd.simps(1) read_pres_not_p_vorder)
  using d_vorder_RdX_pres apply blast
  apply(cases "pc s t1", auto)
  apply (metis RdX_def init_val_pres isRd.simps(1) no_val_def read_pres_not_p_vorder)
  using amo_intro_step no_val_def apply blast
  apply (metis RdX_def init_val_pres isRd.simps(1) no_val_def read_pres_not_p_vorder)
  using amo_intro_step no_val_def zero_neq_numeral apply blast
  apply (metis RdX_def init_val_pres isRd.simps(1) no_val_def read_pres_not_p_vorder)
  using enc_pres apply blast
  apply (metis RdX_def amo_read_pres isRd.simps(1))
  apply (metis RdX_def amo_def isRd.simps(1) read_pres_not_p_vorder)
  apply (metis RdX_def amo_read_pres isRd.simps(1))
   apply (metis RdX_def amo_def isRd.simps(1) read_pres_not_p_vorder)
  using d_vorder_RdX_pres by blast

  

lemma t2_local :
  assumes "prog_inv t2 ((pc s) t2) s"
  and "thrdsvars"
  and "prog t2 s s'"
shows  "prog_inv t2 ((pc s') t2) s'"
  using assms
  apply(unfold prog_inv_def prog_def thrdsvars_def update_pc_def, simp)
  apply(cases "pc s t2", auto)
  using init_val_pres apply blast
  using enc_RdX_intro apply blast
  apply(simp add: prog_inv_def prog_def update_pc_def) 
  using enc_pvord_step 
  by (metis RdX_def avar.simps(1) isRd.simps(1) rd_val.simps(1))



lemma t2_global :
  assumes "prog_inv t2 ((pc s) t2) s"
  and "prog_inv t1 ((pc s) t1) s"
  and "thrdsvars"
  and "prog t1 s s'"
shows  "prog_inv t2 ((pc s') t2) s'"
  using assms
  apply(unfold prog_inv_def prog_def thrdsvars_def  update_pc_def)
  apply clarsimp
  apply(cases "pc s t1", auto)
   apply(cases "pc s t2", simp_all)
     apply(intro conjI)
  using init_val_pres apply blast
  using amo_intro_step no_val_def apply blast
  apply (simp add: amo_intro_step no_val_def)
    using assms(3) assms(4) prog_inv_def t1_local
  apply (simp add: enc_pres init_val_pres)
   apply(cases "pc s t2", simp_all)
  using enc_pres init_val_pres apply blast
    apply (metis WrX_def  isWr.simps(2) p_vorder_write_pres)
     apply(cases "pc s t2", simp)
  apply (smt One_nat_def PC.simps(9) assms(2) assms(3) assms(4) fun_upd_same init_val_pres prog_inv_def t1_local)
  apply simp
  using enc_pres init_val_pres apply blast
   apply simp
   apply (intro impI)
   apply simp 
  using p_vorder_write_pres
  by (metis WrX_def isWr.simps(2))

end