theory LB
  imports  OpSem
begin
datatype PC =
  L1
| L2
| L3

consts t1 :: T 
consts t2 :: T
consts x :: L
consts y :: L


definition "thrdsvars \<equiv>  t1 \<noteq> t2 \<and> x \<noteq> y"


record prog_state =
  pc :: "T \<Rightarrow> PC"
  state :: surrey_state
  r1 :: V
  r2 :: V

definition 
  "update_pc t nv pcf \<equiv> pcf (t := nv)"


definition prog :: "T \<Rightarrow> prog_state \<Rightarrow> prog_state \<Rightarrow> bool " where
"prog t s s' \<equiv> 
(
  if t = t1
    then
      if (pc s) t = L1
      then
        pc s' = update_pc t L2 (pc s) \<and>                     
        (state s) [r1 s' \<leftarrow> x]\<^sub>t (state s') \<and> r2 s = r2 s'
  else
      if (pc s) t = L2
      then
        pc s' = update_pc t L3 (pc s) \<and>  
        (state s) [y := 1]\<^sub>t (state s') 
         \<and> r1 s = r1 s'  \<and> r2 s = r2 s'               
      else
        False
else
  if t = t2
    then
      if (pc s) t = L1
        then
          pc s' = update_pc t L2 (pc s) \<and>    
          (state s) [r2 s' \<leftarrow> y]\<^sub>t (state s')                 
          \<and> r1 s = r1 s'
      else
        if (pc s) t = L2
          then
            pc s' = update_pc t L3 (pc s) \<and>  
            (state s) [x := 1]\<^sub>t (state s') \<and> r1 s = r1 s'  \<and> r2 s = r2 s'                   
          else
            False
  else
    False
)"

definition prog_inv :: "T \<Rightarrow> PC \<Rightarrow> prog_state \<Rightarrow> bool " where
"prog_inv t p s \<equiv> 
  if t = t1 
  then
    let t' = t2 in 
    (case p of
        L1 \<Rightarrow> [y =\<^sub>t' 0] (state s) \<and>  r2 s = 0
      | L2 \<Rightarrow> [y =\<^sub>t' 0] (state s) \<and>  r2 s = 0
      | L3 \<Rightarrow>  r1 s = 0 \<or> r2 s = 0 
    )
  else 
    if t = t2 then
      let t' = t1 in 
      (case p of
          L1 \<Rightarrow> [x =\<^sub>t' 0] (state s) \<and>  r1 s = 0
        | L2 \<Rightarrow> [x =\<^sub>t' 0] (state s) \<and>  r1 s = 0
        | L3 \<Rightarrow>  r1 s = 0 \<or> r2 s = 0
      )

  else
    False
"




definition init_map  :: "(L \<Rightarrow> V) \<Rightarrow> bool" where
  "init_map \<phi> \<equiv> \<phi> x = 0 \<and> \<phi> y = 0" 

definition init_mps  :: "surrey_state  \<Rightarrow> bool"
  where
    "init_mps ss \<equiv> \<exists> \<phi>. initial_state ss \<phi> \<and> init_map \<phi>"

definition init  :: "prog_state  \<Rightarrow> bool"
  where
    "init mps \<equiv> (pc mps) t1 = L1 
      \<and> (pc mps) t2 = L1 \<and> r1 mps = 0 \<and> r2 mps = 0
    \<and> init_mps (state mps) \<and> thrdsvars"

definition global_inv ::"prog_state \<Rightarrow> bool"
  where "global_inv s \<equiv> thrdsvars \<and> wfs (state s)"

lemma init_wfs :  "init mps \<Longrightarrow> wfs (state mps)"
  apply (unfold init_def wfs_def init_mps_def)
  using initial_wfs wfs_def by blast



lemma init_inv : " init s \<Longrightarrow> prog_inv t1 L1 s \<and> prog_inv t2 L1 s"
  apply(unfold init_def init_mps_def init_map_def prog_inv_def  d_obs_def d_obs_t_def thrdsvars_def)
  apply clarsimp
  apply safe
  using initial_wfs initially_write_unique last_write_write_on wfs_def apply blast
     apply(simp add: initial_state_def lastWr_def value_def) 
     apply clarsimp
 using initial_wfs initially_write_unique last_write_write_on wfs_def apply blast
     apply(simp add: initial_state_def lastWr_def value_def) 
  by auto
 


lemma t1_local:
  assumes "global_inv s"
      and "prog_inv t1 ((pc s) t1) s" 
      and "prog t1 s s'"
    shows "prog_inv t1 ((pc s') t1) s'"
  using assms 
  apply(simp add: prog_def prog_inv_def thrdsvars_def)
    apply (cases "pc s t1", auto)
   apply (simp_all add: update_pc_def)
  by (metis dobs_RdX_pres global_inv_def thrdsvars_def)
  


lemma t1_global:
  assumes "global_inv s"
      and "prog_inv t1 ((pc s) t1)  s" 
      and "prog_inv t2 ((pc s) t2)  s" 
      and "prog t2 s s'"
    shows "prog_inv t1 ((pc s') t1) s'"
  using assms 
  apply(simp add: prog_def prog_inv_def thrdsvars_def global_inv_def)
  apply (cases "pc s t2", auto)
   apply (simp_all add: update_pc_def)
   apply (cases "pc s t1", auto)
  using d_obs_RdX_pres apply blast
  apply (metis null_def RdX_def d_obs_p_obs_agree p_obs_Rd_intro2)
  using d_obs_RdX_pres apply blast
  apply (metis null_def RdX_def d_obs_p_obs_agree p_obs_Rd_intro2)
  apply (cases "pc s t1", auto)
  by (metis d_obs_WrX_other)+


lemma t2_local:
  assumes "global_inv s"
      and "prog_inv t2 ((pc s) t2) s" 
      and "prog t2 s s'"
    shows "prog_inv t2 ((pc s') t2) s'"
  using assms 
  apply(simp add: prog_def prog_inv_def thrdsvars_def)
    apply (cases "pc s t2", auto)
     apply (simp_all add: update_pc_def)
   apply (simp add: global_inv_def thrdsvars_def)
  by (metis dobs_RdX_pres)
  


lemma t2_global:
  assumes "global_inv s"
      and "prog_inv t1 ((pc s) t1)  s" 
      and "prog_inv t2 ((pc s) t2)  s" 
      and "prog t1 s s'"
    shows "prog_inv t2 ((pc s') t2) s'"
  using assms 
  apply(simp add: prog_def prog_inv_def thrdsvars_def global_inv_def)
    apply (cases "pc s t1", auto)
   apply (simp_all add: update_pc_def)
   apply (cases "pc s t2", auto)
  using d_obs_RdX_pres apply blast
  apply (metis null_def RdX_def d_obs_p_obs_agree p_obs_Rd_intro2)
  using d_obs_RdX_pres apply blast
  apply (metis null_def RdX_def d_obs_p_obs_agree p_obs_Rd_intro2)
  by (metis (mono_tags, lifting) PC.exhaust PC.simps(7) PC.simps(8) PC.simps(9) d_obs_WrX_other)

theorem final_inv:
  assumes "wfs (state s)"   
  and "thrdsvars"
  and "t \<in> {t1, t2}"
  and "t' \<in> {t1, t2}"
  and "prog_inv t ((pc s) t) s"
  and "prog_inv t' ((pc s) t') s" 
  and "prog t' s s'"
shows "prog_inv t ((pc s') t) s'"
  using assms 
  using global_inv_def t1_global t1_local t2_global t2_local by blast

end
