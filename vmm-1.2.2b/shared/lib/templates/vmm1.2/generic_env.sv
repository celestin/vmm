//
// Template for VMM-compliant verification environment
// <VNAME>     Name of Environment/VIP 
// <ENV>       Name of env class
// <TR>        Name of the transaction descriptor
// <XACT>      Name of the master driver
// <MON>       Name of the monitor class
// [filename]  ENV
//

`ifndef ENV__SV
`define ENV__SV

class ENV extends vmm_group;

   XACT drv;
   MON mon;
   TR_channel TR_chan;
	// ToDo: Add more channel if required
   vmm_ms_scenario_gen ms_gen;
   VNAME_ms_scen ms_scn;
	// ToDo: Add more scenario if required

   typedef enum {GEN_MODE, REPLAY_MODE, MONITOR_ONLY} mode_e;
   rand mode_e mode;
   // ToDo: Add other environment class property if required

   MACRO_START
   `vmm_unit_config_begin(ENV)
      //ToDo: Add macros for required config variables to get the configuration 
   `vmm_unit_config_end(ENV)
   MACRO_END

   extern function new(string name, vmm_group parent=null);
   extern virtual function void build_ph();
   NORMAL_START
   extern virtual function void configure_ph();
   NORMAL_END
   extern virtual function void connect_ph();
   extern function void start_of_sim_ph();
   extern virtual task reset_ph();
   extern virtual task config_dut_ph();
   extern virtual task start_ph();
   extern virtual task run_ph();
   extern virtual task shutdown_ph();
   extern virtual task cleanup_ph();
   extern virtual function void report_ph();
   extern task record(vmm_channel TR_chan, int i);
   extern task replay(vmm_channel TR_chan, int i);
endclass:ENV

function ENV::new(string name, vmm_group parent=null);
   super.new(name,"env",parent);
   vmm_ver = new();
   vmm_ver.display("**** Note : ");
   $timeformat(-9, 0, "ns", 1);
endfunction: new

function void ENV::build_ph();
   int mode_opt;
   super.build_ph();
   mode_opt = vmm_opts::get_int("mode", 0, "Configuration value for Environment mode");

   case(mode_opt)
      0: mode = GEN_MODE;
      1: mode = REPLAY_MODE;
      2: mode = MONITOR_ONLY;
   endcase

   if (mode == GEN_MODE) begin
      TR_chan   = new("TR_channel","channel", 1, 0, 0, this);
      drv    = new("Driver","drv", 1, this);
      ms_gen    = new("gen", 1, , this);
      ms_scn    = VNAME_ms_scen::create_instance(this,"ms_scn");
      ms_gen.register_channel("TR_scenario_channel", TR_chan);
		// ToDo: Register more channel if added later
      ms_gen.register_ms_scenario("scenario_0", ms_scn);
		// ToDo: Register more ms_scenario if added later
   end

   if (mode == REPLAY_MODE) begin
      TR_chan   = new("TR_channel","channel", 1, 0, 0, this);
		// ToDo: New more channel if added later
      drv    = new("Driver","drv", 1, this);
   end
   mon   = new("Monitor","mon", 1, this);
   //ToDo : new other component if added later

endfunction: build_ph

NORMAL_START
function void ENV::configure_ph();
   super.configure_ph();
   //ToDo : functional configuration if needed
endfunction: configure_ph
NORMAL_END

function void ENV::connect_ph();
   super.connect_ph();
   if (cfg.mode != MONITOR_ONLY) TR_chan = drv.in_chan;
endfunction: connect_ph

function void ENV::start_of_sim_ph();
   super.start_of_sim_ph();
	//ToDo: Configure generator to stop_after_n_insts/scenarios
endfunction: start_of_sim_ph

task ENV::reset_ph();
   super.reset_ph();
   //ToDo: Reset DUT
endtask:reset_ph

task ENV::config_dut_ph();
   super.config_dut_ph();
   //ToDo: Configure the DUT

endtask: config_dut_ph

task ENV::start_ph();
   super.start_ph();

   //ToDo: Start the other components if added later
   vote.register_xactor(mon);
   if (cfg.mode == GEN_MODE) begin
      vote.register_xactor(gen_ms);
      vote.register_xactor(drv);
   end
   if (cfg.mode == REPLAY_MODE) begin
      vote.register_xactor(drv);
   end
   //ToDo: Register other components,channels and notifications if added by user

endtask: start_ph

task ENV::run_ph();
   super.run_ph();
   if (cfg.mode == GEN_MODE) begin
      fork record(TR_chan,0); join_none
   end
   if (cfg.mode == REPLAY_MODE) begin
      fork replay(TR_chan,0); join_none
   end

   if(cfg.mode == REPLAY_MODE)
      TR_chan.notify.wait_for(vmm_channel::PLAYBACK_DONE);
   vote.wait_for_consensus();
endtask: run_ph

task ENV::shutdown_ph();
   super.shutdown_ph();
   //ToDo: Shutdown the other components if added later
endtask: shutdown_ph

task void ENV::cleanup_ph();
   super.cleanup_ph();
   // ToDo: check that nothing was lost
endtask: cleanup_ph

function void ENV::report_ph();
   super.report_ph();
   // ToDo: Generate the Final Report
endfunction: report_ph

task ENV::record(vmm_channel TR_chan, int i);
   string id_s = $psprintf("%0d", i);
   TR_chan.record({"Chan", id_s, ".dat"});
	//ToDo: Record other channel if added later
endtask: record

task ENV::replay(vmm_channel TR_chan, int i);
   bit success;
   TR tr = new;
   TR_chan.playback(success, {"Chan", id_s, ".dat"}, tr);
   if (!success) `vmm_error(log, {"Playback mode failed for channel", id_s});
	//ToDo: Replay other channel if added later
endtask:replay

