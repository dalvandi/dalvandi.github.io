#include <iostream> 
#include "uds.h"
#include "util.h"
#include "prime_api_rtm.h"
#include "uds.h"
#include "prime_api_t.h"
#include "prime_api_app_t.h"
#include "prime_api_dev_t.h"


namespace assertion{


void assert_PRIME_API_APP_REG(std::vector<std::pair<pid_t, std::shared_ptr<prime::uds>>> app_sockets, pid_t proc_id)
{
 //rule 1 
 if(std::find_if(app_sockets.begin(),app_sockets.end(), [=](std::pair<pid_t, std::shared_ptr<prime::uds>> x) {return x.first == proc_id;}) != app_sockets.end()) throw std::runtime_error("ensure the application is not registred when registering the application (grd1@PRIME_API_APP_REG)"); 
}



void assert_PRIME_API_APP_DEREG(std::vector<std::pair<pid_t, std::shared_ptr<prime::uds>>> app_sockets, pid_t proc_id, std::vector<prime::api::app::knob_disc_t> app_knobs_disc, std::vector<prime::api::app::knob_cont_t> app_knobs_cont, std::vector<prime::api::app::mon_disc_t> app_mons_disc, std::vector<prime::api::app::mon_cont_t> app_mons_cont)
{
 //rule 2 
 if(std::find_if(app_sockets.begin(),app_sockets.end(), [=](std::pair<pid_t, std::shared_ptr<prime::uds>> x) {return x.first == proc_id;}) == app_sockets.end())throw std::runtime_error("ensure the application is registered when deregistering the application (grd1@PRIME_API_APP_DEREG)");
//rule 3 
 if(std::find_if(app_knobs_disc.begin(),app_knobs_disc.end(), [=](prime::api::app::knob_disc_t x) {return x.proc_id == proc_id;}) != app_knobs_disc.end())throw std::runtime_error("ensure the application knobs are deregistered when deregistering the application (grd2@PRIME_API_APP_DEREG)");
//rule 3 
 if(std::find_if(app_knobs_cont.begin(),app_knobs_cont.end(), [=](prime::api::app::knob_cont_t x) {return x.proc_id == proc_id;}) != app_knobs_cont.end())throw std::runtime_error("ensure the application knobs are deregistered when deregistering the application (grd3@PRIME_API_APP_DEREG)");
//rule 3 
 if(std::find_if(app_mons_disc.begin(),app_mons_disc.end(), [=](prime::api::app::mon_disc_t x) {return x.proc_id == proc_id;}) != app_mons_disc.end())throw std::runtime_error("ensure the application monitors are deregistered when deregistering the application (grd4@PRIME_API_APP_DEREG)");
//rule 3 
 if(std::find_if(app_mons_cont.begin(),app_mons_cont.end(), [=](prime::api::app::mon_cont_t x) {return x.proc_id == proc_id;}) != app_mons_cont.end())throw std::runtime_error("ensure the application monitors are deregistered when deregistering the application (grd5@PRIME_API_APP_DEREG)"); 
}



void assert_PRIME_API_APP_KNOB_DISC_REG(std::vector<std::pair<pid_t, std::shared_ptr<prime::uds>>> app_sockets, pid_t proc_id, std::vector<prime::api::app::knob_disc_t> app_knobs_disc, prime::api::app::knob_disc_t knob)
{
 //rule 2 
 if(std::find_if(app_sockets.begin(),app_sockets.end(), [=](std::pair<pid_t, std::shared_ptr<prime::uds>> x) {return x.first == proc_id;}) == app_sockets.end())throw std::runtime_error("ensure the application is registred when registering the application knob (grd1@PRIME_API_APP_KNOB_DISC_REG)");
//rule 4 
 if(std::find_if(app_knobs_disc.begin(),app_knobs_disc.end(), [=](prime::api::app::knob_disc_t x) {return x.id == knob.id && x.proc_id == knob.proc_id;})!= app_knobs_disc.end())throw std::runtime_error("ensure the application konb is not registred when registering the application knob  (grd2@PRIME_API_APP_KNOB_DISC_REG)");
//rule 5 
 if(knob.min > knob.max) throw std::runtime_error("ensure min<max when registering the application knob (grd3@PRIME_API_APP_KNOB_DISC_REG)"); 
}



void assert_PRIME_API_APP_KNOB_DISC_DEREG(std::vector<prime::api::app::knob_disc_t> app_knobs_disc, pid_t proc_id, int id)
{
 //rule 6 
 if(std::find_if(app_knobs_disc.begin(),app_knobs_disc.end(), [=](prime::api::app::knob_disc_t x) {return x.id == id && x.proc_id == proc_id;}) == app_knobs_disc.end()) throw std::runtime_error("ensure the application is registred when deregistering the application knob (grd1@PRIME_API_APP_KNOB_DISC_DEREG)"); 
}



void assert_PRIME_API_APP_KNOB_DISC_MIN(std::vector<prime::api::app::knob_disc_t> app_knobs_disc, pid_t proc_id, int id, int min)
{
 //rule 6 
 if(std::find_if(app_knobs_disc.begin(),app_knobs_disc.end(), [=](prime::api::app::knob_disc_t x) {return x.id == id && x.proc_id == proc_id;}) == app_knobs_disc.end()) throw std::runtime_error("ensure the application is registred when changing the min for the application knob (grd1@PRIME_API_APP_KNOB_DISC_MIN)");
//rule 7 
 if(min >= (*std::find_if(app_knobs_disc.begin(), app_knobs_disc.end(), [=](prime::api::app::knob_disc_t x) {return x.id == id && x.proc_id == proc_id;})).max) throw std::runtime_error("ensure min<max when changing the min for the application knob (grd2@PRIME_API_APP_KNOB_DISC_MIN)");
//rule 8 
 if(min > (*std::find_if(app_knobs_disc.begin(), app_knobs_disc.end(), [=](prime::api::app::knob_disc_t x) {return x.id == id && x.proc_id == proc_id;})).val) throw std::runtime_error("ensure min<=value when changing the min for the application knob (grd3@PRIME_API_APP_KNOB_DISC_MIN)"); 
}



void assert_PRIME_API_APP_KNOB_DISC_MAX(std::vector<prime::api::app::knob_disc_t> app_knobs_disc, pid_t proc_id, int id, int max)
{
 //rule 6 
 if(std::find_if(app_knobs_disc.begin(),app_knobs_disc.end(), [=](prime::api::app::knob_disc_t x) {return x.id == id && x.proc_id == proc_id;}) == app_knobs_disc.end()) throw std::runtime_error("ensure the application is registred when changing the max for the application knob (grd1@PRIME_API_APP_KNOB_DISC_MAX)");
//rule 9 
 if(max <= (*std::find_if(app_knobs_disc.begin(), app_knobs_disc.end(), [=](prime::api::app::knob_disc_t x) {return x.id == id && x.proc_id == proc_id;})).min) throw std::runtime_error("ensure max>min  when changing the max for the application knob (grd2@PRIME_API_APP_KNOB_DISC_MAX)");
//rule 10 
 if(max <= (*std::find_if(app_knobs_disc.begin(), app_knobs_disc.end(), [=](prime::api::app::knob_disc_t x) {return x.id == id && x.proc_id == proc_id;})).val) throw std::runtime_error("ensure max>=value  when changing the max for the application knob (grd3@PRIME_API_APP_KNOB_DISC_MAX)"); 
}



void assert_PRIME_API_APP_KNOB_CONT_MIN(std::vector<prime::api::app::knob_cont_t> app_knobs_cont, pid_t proc_id, int id, int min)
{
 //rule 6 
 if(std::find_if(app_knobs_cont.begin(),app_knobs_cont.end(), [=](prime::api::app::knob_cont_t x) {return x.id == id && x.proc_id == proc_id;}) == app_knobs_cont.end()) throw std::runtime_error("ensure the application is registred when changing the min for the application knob (grd1@PRIME_API_APP_KNOB_CONT_MIN)");
//rule 7 
 if(min >= (*std::find_if(app_knobs_cont.begin(), app_knobs_cont.end(), [=](prime::api::app::knob_cont_t x) {return x.id == id && x.proc_id == proc_id;})).max) throw std::runtime_error("ensure min<max when changing the min for the application knob (grd2@PRIME_API_APP_KNOB_CONT_MIN)");
//rule 8 
 if(min > (*std::find_if(app_knobs_cont.begin(), app_knobs_cont.end(), [=](prime::api::app::knob_cont_t x) {return x.id == id && x.proc_id == proc_id;})).val) throw std::runtime_error("ensure min<=value when changing the min for the application knob (grd3@PRIME_API_APP_KNOB_CONT_MIN)"); 
}



void assert_PRIME_API_APP_KNOB_CONT_MAX(std::vector<prime::api::app::knob_cont_t> app_knobs_cont, pid_t proc_id, int id, int max)
{
 //rule 6 
 if(std::find_if(app_knobs_cont.begin(),app_knobs_cont.end(), [=](prime::api::app::knob_cont_t x) {return x.id == id && x.proc_id == proc_id;}) == app_knobs_cont.end()) throw std::runtime_error("ensure the application is registred when changing the max for the application knob (grd1@PRIME_API_APP_KNOB_CONT_MAX)");
//rule 9 
 if(max <= (*std::find_if(app_knobs_cont.begin(), app_knobs_cont.end(), [=](prime::api::app::knob_cont_t x) {return x.id == id && x.proc_id == proc_id;})).min) throw std::runtime_error("ensure max>min  when changing the max for the application knob (grd2@PRIME_API_APP_KNOB_CONT_MAX)");
//rule 10 
 if(max <= (*std::find_if(app_knobs_cont.begin(), app_knobs_cont.end(), [=](prime::api::app::knob_cont_t x) {return x.id == id && x.proc_id == proc_id;})).val) throw std::runtime_error("ensure max>=value  when changing the max for the application knob (grd3@PRIME_API_APP_KNOB_CONT_MAX)"); 
}



void assert_PRIME_API_APP_KNOB_DISC_GET(std::vector<prime::api::app::knob_disc_t> app_knobs_disc, pid_t proc_id, int id, int val)
{
 //rule 6 
 if(std::find_if(app_knobs_disc.begin(),app_knobs_disc.end(), [=](prime::api::app::knob_disc_t x) {return x.id == id && x.proc_id == proc_id;}) == app_knobs_disc.end()) throw std::runtime_error("ensure the application is registred when changing the value for the application knob (grd1@PRIME_API_APP_KNOB_DISC_GET)");
//rule 11 
 if(val < (*std::find_if(app_knobs_disc.begin(), app_knobs_disc.end(), [=](prime::api::app::knob_disc_t x) {return x.id == id && x.proc_id == proc_id;})).min) throw std::runtime_error("ensure min<=value when changing the value for the application knob (grd2@PRIME_API_APP_KNOB_DISC_GET)");
//rule 12 
 if(val >= (*std::find_if(app_knobs_disc.begin(), app_knobs_disc.end(), [=](prime::api::app::knob_disc_t x) {return x.id == id && x.proc_id == proc_id;})).max) throw std::runtime_error("ensure max>=value when changing the value for the application knob (grd3@PRIME_API_APP_KNOB_DISC_GET)"); 
}



void assert_PRIME_API_APP_KNOB_CONT_GET(std::vector<prime::api::app::knob_cont_t> app_knobs_cont, pid_t proc_id, int id, int val)
{
 //rule 6 
 if(std::find_if(app_knobs_cont.begin(),app_knobs_cont.end(), [=](prime::api::app::knob_cont_t x) {return x.id == id && x.proc_id == proc_id;}) == app_knobs_cont.end()) throw std::runtime_error("ensure the application is registred when changing the value for the application knob (grd1@PRIME_API_APP_KNOB_CONT_GET)");
//rule 11 
 if(val < (*std::find_if(app_knobs_cont.begin(), app_knobs_cont.end(), [=](prime::api::app::knob_cont_t x) {return x.id == id && x.proc_id == proc_id;})).min) throw std::runtime_error("ensure min<=value when changing the value for the application knob (grd2@PRIME_API_APP_KNOB_CONT_GET)");
//rule 12 
 if(val >= (*std::find_if(app_knobs_cont.begin(), app_knobs_cont.end(), [=](prime::api::app::knob_cont_t x) {return x.id == id && x.proc_id == proc_id;})).max) throw std::runtime_error("ensure max>=value when changing the value for the application knob (grd3@PRIME_API_APP_KNOB_CONT_GET)"); 
}



void assert_PRIME_API_APP_MON_DISC_MIN(std::vector<prime::api::app::mon_disc_t> app_mons_disc, pid_t proc_id, int id, int min)
{
 //rule 6 
 if(std::find_if(app_mons_disc.begin(),app_mons_disc.end(), [=](prime::api::app::mon_disc_t x) {return x.id == id && x.proc_id == proc_id;}) == app_mons_disc.end()) throw std::runtime_error("ensure the application is registred when chanigng the min for the application monitor (grd1@PRIME_API_APP_MON_DISC_MIN)");
//rule 7 
 if(min >= (*std::find_if(app_mons_disc.begin(), app_mons_disc.end(), [=](prime::api::app::mon_disc_t x) {return x.id == id && x.proc_id == proc_id;})).max) throw std::runtime_error("ensure min<max when chanigng the min for the application monitor (grd2@PRIME_API_APP_MON_DISC_MIN)");
//rule 8 
 if(min > (*std::find_if(app_mons_disc.begin(), app_mons_disc.end(), [=](prime::api::app::mon_disc_t x) {return x.id == id && x.proc_id == proc_id;})).val) throw std::runtime_error("ensure min<=value when chanigng the min for the application monitor (grd3@PRIME_API_APP_MON_DISC_MIN)"); 
}



void assert_PRIME_API_APP_MON_DISC_MAX(std::vector<prime::api::app::mon_disc_t> app_mons_disc, pid_t proc_id, int id, int max)
{
 //rule 6 
 if(std::find_if(app_mons_disc.begin(),app_mons_disc.end(), [=](prime::api::app::mon_disc_t x) {return x.id == id && x.proc_id == proc_id;}) == app_mons_disc.end()) throw std::runtime_error("ensure the application is registred when chanigng the max for the application monitor (grd1@PRIME_API_APP_MON_DISC_MAX)");
//rule 9 
 if(max <= (*std::find_if(app_mons_disc.begin(), app_mons_disc.end(), [=](prime::api::app::mon_disc_t x) {return x.id == id && x.proc_id == proc_id;})).min) throw std::runtime_error("ensure max>min when chanigng the max for the application monitor (grd2@PRIME_API_APP_MON_DISC_MAX)");
//rule 10 
 if(max <= (*std::find_if(app_mons_disc.begin(), app_mons_disc.end(), [=](prime::api::app::mon_disc_t x) {return x.id == id && x.proc_id == proc_id;})).val) throw std::runtime_error("ensure max>=value when chanigng the max for the application monitor (grd3@PRIME_API_APP_MON_DISC_MAX)"); 
}



void assert_PRIME_API_APP_MON_CONT_MIN(std::vector<prime::api::app::mon_cont_t> app_mons_cont, pid_t proc_id, int id, int min)
{
 //rule 6 
 if(std::find_if(app_mons_cont.begin(),app_mons_cont.end(), [=](prime::api::app::mon_cont_t x) {return x.id == id && x.proc_id == proc_id;}) == app_mons_cont.end()) throw std::runtime_error("ensure the application is registred when chanigng the min for the application monitor (grd1@PRIME_API_APP_MON_CONT_MIN)");
//rule 7 
 if(min >= (*std::find_if(app_mons_cont.begin(), app_mons_cont.end(), [=](prime::api::app::mon_cont_t x) {return x.id == id && x.proc_id == proc_id;})).max) throw std::runtime_error("ensure min<max when chanigng the min for the application monitor (grd2@PRIME_API_APP_MON_CONT_MIN)");
//rule 8 
 if(min > (*std::find_if(app_mons_cont.begin(), app_mons_cont.end(), [=](prime::api::app::mon_cont_t x) {return x.id == id && x.proc_id == proc_id;})).val) throw std::runtime_error("ensure min<=value when chanigng the min for the application monitor (grd3@PRIME_API_APP_MON_CONT_MIN)"); 
}



void assert_PRIME_API_APP_MON_CONT_MAX(std::vector<prime::api::app::mon_cont_t> app_mons_cont, pid_t proc_id, int id, int max)
{
 //rule 6 
 if(std::find_if(app_mons_cont.begin(),app_mons_cont.end(), [=](prime::api::app::mon_cont_t x) {return x.id == id && x.proc_id == proc_id;}) == app_mons_cont.end()) throw std::runtime_error("ensure the application is registred when chanigng the max for the application monitor (grd1@PRIME_API_APP_MON_CONT_MAX)");
//rule 9 
 if(max <= (*std::find_if(app_mons_cont.begin(), app_mons_cont.end(), [=](prime::api::app::mon_cont_t x) {return x.id == id && x.proc_id == proc_id;})).min) throw std::runtime_error("ensure max>min when chanigng the max for the application monitor (grd2@PRIME_API_APP_MON_CONT_MAX)");
//rule 10 
 if(max <= (*std::find_if(app_mons_cont.begin(), app_mons_cont.end(), [=](prime::api::app::mon_cont_t x) {return x.id == id && x.proc_id == proc_id;})).val) throw std::runtime_error("ensure max>=value when chanigng the max for the application monitor (grd3@PRIME_API_APP_MON_CONT_MAX)"); 
}



void assert_PRIME_API_APP_MON_DISC_SET(std::vector<prime::api::app::mon_disc_t> app_mons_disc, pid_t proc_id, int id, int val)
{
 //rule 6 
 if(std::find_if(app_mons_disc.begin(),app_mons_disc.end(), [=](prime::api::app::mon_disc_t x) {return x.id == id && x.proc_id == proc_id;}) == app_mons_disc.end()) throw std::runtime_error("ensure the application is registred when chanigng the value for the application monitor (grd1@PRIME_API_APP_MON_DISC_SET)");
//rule 11 
 if(val < (*std::find_if(app_mons_disc.begin(), app_mons_disc.end(), [=](prime::api::app::mon_disc_t x) {return x.id == id && x.proc_id == proc_id;})).min) throw std::runtime_error("esnure min<=value when chanigng the value for the application monitor (grd2@PRIME_API_APP_MON_DISC_SET)");
//rule 12 
 if(val >= (*std::find_if(app_mons_disc.begin(), app_mons_disc.end(), [=](prime::api::app::mon_disc_t x) {return x.id == id && x.proc_id == proc_id;})).max) throw std::runtime_error("ensure max>=value when chanigng the value for the application monitor (grd3@PRIME_API_APP_MON_DISC_SET)"); 
}



void assert_PRIME_API_APP_MON_CONT_SET(std::vector<prime::api::app::mon_cont_t> app_mons_cont, pid_t proc_id, int id, int val)
{
 //rule 6 
 if(std::find_if(app_mons_cont.begin(),app_mons_cont.end(), [=](prime::api::app::mon_cont_t x) {return x.id == id && x.proc_id == proc_id;}) == app_mons_cont.end()) throw std::runtime_error("ensure the application is registred when chanigng the value for the application monitor (grd1@PRIME_API_APP_MON_CONT_SET)");
//rule 11 
 if(val < (*std::find_if(app_mons_cont.begin(), app_mons_cont.end(), [=](prime::api::app::mon_cont_t x) {return x.id == id && x.proc_id == proc_id;})).min) throw std::runtime_error("esnure min<=value when chanigng the value for the application monitor (grd2@PRIME_API_APP_MON_CONT_SET)");
//rule 12 
 if(val >= (*std::find_if(app_mons_cont.begin(), app_mons_cont.end(), [=](prime::api::app::mon_cont_t x) {return x.id == id && x.proc_id == proc_id;})).max) throw std::runtime_error("ensure max>=value when chanigng the value for the application monitor (grd3@PRIME_API_APP_MON_CONT_SET)"); 
}



void assert_PRIME_API_APP_KNOB_CONT_REG(std::vector<std::pair<pid_t, std::shared_ptr<prime::uds>>> app_sockets, pid_t proc_id, std::vector<prime::api::app::knob_cont_t> app_knobs_cont, prime::api::app::knob_cont_t knob)
{
 //rule 2 
 if(std::find_if(app_sockets.begin(),app_sockets.end(), [=](std::pair<pid_t, std::shared_ptr<prime::uds>> x) {return x.first == proc_id;}) == app_sockets.end())throw std::runtime_error("ensure the application is registred when registering the application knob (grd1@PRIME_API_APP_KNOB_CONT_REG)");
//rule 4 
 if(std::find_if(app_knobs_cont.begin(),app_knobs_cont.end(), [=](prime::api::app::knob_cont_t x) {return x.id == knob.id && x.proc_id == knob.proc_id;})!= app_knobs_cont.end())throw std::runtime_error("ensure the application knob is not registred when registering the application knob  (grd2@PRIME_API_APP_KNOB_CONT_REG)");
//rule 5 
 if(knob.min > knob.max) throw std::runtime_error("ensure min<max when registering the application knob (grd3@PRIME_API_APP_KNOB_CONT_REG)"); 
}



void assert_PRIME_API_APP_KNOB_CONT_DEREG(std::vector<prime::api::app::knob_cont_t> app_knobs_cont, pid_t proc_id, int id)
{
 //rule 6 
 if(std::find_if(app_knobs_cont.begin(),app_knobs_cont.end(), [=](prime::api::app::knob_cont_t x) {return x.id == id && x.proc_id == proc_id;}) == app_knobs_cont.end()) throw std::runtime_error("ensure the application is registred when deregistering the application knob (grd1@PRIME_API_APP_KNOB_CONT_DEREG)"); 
}



void assert_PRIME_API_APP_MON_DISC_REG(std::vector<std::pair<pid_t, std::shared_ptr<prime::uds>>> app_sockets, pid_t proc_id, std::vector<prime::api::app::mon_disc_t> app_mons_disc, prime::api::app::mon_disc_t mon)
{
 //rule 2 
 if(std::find_if(app_sockets.begin(),app_sockets.end(), [=](std::pair<pid_t, std::shared_ptr<prime::uds>> x) {return x.first == proc_id;}) == app_sockets.end())throw std::runtime_error("ensure the application is registred when registering the application monitor (grd1@PRIME_API_APP_MON_DISC_REG)");
//rule 4 
 if(std::find_if(app_mons_disc.begin(),app_mons_disc.end(), [=](prime::api::app::mon_disc_t x) {return x.id == mon.id && x.proc_id == mon.proc_id;})!= app_mons_disc.end())throw std::runtime_error("ensure the application monitor is not registered before when registering the application monitor (grd2@PRIME_API_APP_MON_DISC_REG)");
//rule 5 
 if(mon.min > mon.max) throw std::runtime_error("ensure min<max when registering the application monitor (grd3@PRIME_API_APP_MON_DISC_REG)"); 
}



void assert_PRIME_API_APP_MON_CONT_REG(std::vector<std::pair<pid_t, std::shared_ptr<prime::uds>>> app_sockets, pid_t proc_id, std::vector<prime::api::app::mon_cont_t> app_mons_cont, prime::api::app::mon_cont_t mon)
{
 //rule 2 
 if(std::find_if(app_sockets.begin(),app_sockets.end(), [=](std::pair<pid_t, std::shared_ptr<prime::uds>> x) {return x.first == proc_id;}) == app_sockets.end())throw std::runtime_error("ensure the application is registred when registering the application monitor (grd1@PRIME_API_APP_MON_CONT_REG)");
//rule 4 
 if(std::find_if(app_mons_cont.begin(),app_mons_cont.end(), [=](prime::api::app::mon_cont_t x) {return x.id == mon.id && x.proc_id == mon.proc_id;})!= app_mons_cont.end())throw std::runtime_error("ensure the application monitor is not registered before when registering the application monitor (grd2@PRIME_API_APP_MON_CONT_REG)");
//rule 5 
 if(mon.min > mon.max) throw std::runtime_error("ensure min<max when registering the application monitor (grd3@PRIME_API_APP_MON_CONT_REG)"); 
}



void assert_PRIME_API_APP_MON_DISC_DEREG(std::vector<prime::api::app::mon_disc_t> app_mons_disc, pid_t proc_id, int id)
{
 //rule 6 
 if(std::find_if(app_mons_disc.begin(),app_mons_disc.end(), [=](prime::api::app::mon_disc_t x) {return x.id == id && x.proc_id == proc_id;}) == app_mons_disc.end()) throw std::runtime_error("ensure the application is registred when deregistering the application monitor (grd1@PRIME_API_APP_MON_DISC_DEREG)"); 
}



void assert_PRIME_API_APP_MON_CONT_DEREG(std::vector<prime::api::app::mon_cont_t> app_mons_cont, pid_t proc_id, int id)
{
 //rule 6 
 if(std::find_if(app_mons_cont.begin(),app_mons_cont.end(), [=](prime::api::app::mon_cont_t x) {return x.id == id && x.proc_id == proc_id;}) == app_mons_cont.end()) throw std::runtime_error("ensure the application is registred when deregistering the application monitor (grd1@PRIME_API_APP_MON_CONT_DEREG)"); 
}





}

