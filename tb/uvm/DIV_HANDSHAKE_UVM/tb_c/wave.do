onerror {resume}
noview .main_pane.structure .main_pane.library .main_pane.objects .main_pane.process
quietly WaveActivateNextPane {} 0
add wave -noupdate -height 30 -expand -subitemconfig {/uvm_root/uvm_test_top/env_h/agent_in_h/sequencer_h/seq.s1 {-childformat {{/uvm_root/uvm_test_top/env_h/agent_in_h/sequencer_h/seq.s1.a -radix decimal}} -expand} /uvm_root/uvm_test_top/env_h/agent_in_h/sequencer_h/seq.s1.a {-height 16 -radix decimal}} /uvm_root/uvm_test_top/env_h/agent_in_h/sequencer_h/seq
add wave -noupdate /top/in/clock
add wave -noupdate /top/in/reset
add wave -noupdate /top/in/valid
add wave -noupdate -radix decimal /top/in/a
add wave -noupdate -childformat {{/uvm_root/uvm_test_top/env_h/agent_in_h/monitor_h/tr.t0.a -radix decimal}} -expand -subitemconfig {/uvm_root/uvm_test_top/env_h/agent_in_h/monitor_h/tr.t0.a {-radix decimal}} /uvm_root/uvm_test_top/env_h/agent_in_h/monitor_h/tr
add wave -noupdate /top/out/valid
add wave -noupdate -radix decimal /top/out/a
add wave -noupdate -childformat {{/uvm_root/uvm_test_top/env_h/agent_out_h/monitor_h/tr.t0.a -radix decimal}} -expand -subitemconfig {/uvm_root/uvm_test_top/env_h/agent_out_h/monitor_h/tr.t0.a {-radix decimal}} /uvm_root/uvm_test_top/env_h/agent_out_h/monitor_h/tr
add wave -noupdate -childformat {{/uvm_root/uvm_test_top/env_h/refmod_h/tr_out.t0.a -radix decimal}} -expand -subitemconfig {/uvm_root/uvm_test_top/env_h/refmod_h/tr_out.t0.a {-radix decimal}} /uvm_root/uvm_test_top/env_h/refmod_h/tr_out
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {5 ns} 0}
quietly wave cursor active 1
configure wave -namecolwidth 400
configure wave -valuecolwidth 100
configure wave -justifyvalue left
configure wave -signalnamewidth 0
configure wave -snapdistance 10
configure wave -datasetprefix 0
configure wave -rowmargin 4
configure wave -childrowmargin 2
configure wave -gridoffset 0
configure wave -gridperiod 1
configure wave -griddelta 40
configure wave -timeline 0
configure wave -timelineunits ns
update
WaveRestoreZoom {0 ns} {250 ns}
