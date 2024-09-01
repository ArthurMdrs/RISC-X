gui_open_db -design V1 -file vcdplus.vpd -nosource
gui_set_radix -radix {decimal} -signals {V1:top.in.a}
gui_set_radix -radix {decimal} -signals {V1:top.out.a}
set TopLevel.1 TopLevel.1

set Wave.1 [gui_create_window -type {Wave}  -parent ${TopLevel.1}]

set _session_group_1 transaction
gui_sg_create "$_session_group_1"
set transaction "$_session_group_1"
gui_sg_addsignal -group "$_session_group_1" { {uvm_test_top$env_h$agent_in_h$sequencer_h}
                                              top.in.clock top.in.reset top.in.valid top.in.a
                                              {uvm_test_top_env_h_agent_in_h_monitor_h_tr}
                                              top.out.valid top.out.a
                                              {uvm_test_top_env_h_agent_out_h_monitor_h_tr}
                                              {uvm_test_top_env_h_refmod_h_tr_out} }   -objtype stream
gui_list_add_group -id ${Wave.1} -after {New Group} {transaction}
gui_list_set_height -id ${Wave.1} -height 131  -name {V1:uvm_test_top$env_h$agent_in_h$sequencer_h} -occurrence 1 -group ${transaction}
gui_list_set_height -id ${Wave.1} -height 80  -name {V1:uvm_test_top_env_h_agent_in_h_monitor_h_tr} -occurrence 1 -group ${transaction}
gui_list_set_height -id ${Wave.1} -height 80  -name {V1:uvm_test_top_env_h_agent_out_h_monitor_h_tr} -occurrence 1 -group ${transaction}
gui_list_set_height -id ${Wave.1} -height 80  -name {V1:uvm_test_top_env_h_refmod_h_tr_out} -occurrence 1 -group ${transaction}

gui_close_window -type HSPane
gui_close_window -type DLPane
gui_close_window -type Transaction
gui_close_window -type Source
gui_close_window -type Console

gui_wv_zoom_timerange -id ${Wave.1} 0 160

