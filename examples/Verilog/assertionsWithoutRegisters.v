// Channel interface with datawire of size SIZE
interface chan #(parameter SIZE = 1);

    // highest bit needed to encoded the given size
    localparam S = SIZE < 1 ? 0 : SIZE - 1;

    logic irdy;
    logic trdy;
    logic [S:0] data;

    modport data_input (input irdy, input data, output trdy);
    modport token_input (input irdy, output trdy);
    modport data_output (output irdy, output data, input trdy);
    modport token_output (output irdy, input trdy);
    modport function_input (input data);
    modport function_output (output data);
endinterface

// Data Queue with length LENGTH, standard length is 2
module DQueue #(LENGTH = 2, DATASIZE=1) (
     input clk, input rst
    ,chan.data_input i0
    ,chan.data_output o0
  );

  // highest bit needed to encode LENGTH positions
  localparam s = LENGTH < 2 ? 0 : $clog2(LENGTH) - 1;
  localparam t = (LENGTH + 1) < 2 ? 0 : $clog2(LENGTH + 1) - 1;
  localparam l = DATASIZE < 1 ? 0 : DATASIZE - 1;

  reg [s:0] in;
  reg [s:0] out;
  reg [l:0] data$addr [0:(LENGTH-1)];
  reg full;

  initial begin
    in = 0;
    out = 0;
    full = 0;
    for (integer i=0; i < LENGTH; i = i + 1)
      data$addr[i] = 0;
  end

  wire [s:0] nextin = (in==(LENGTH-1)) ? 1'b 0 : (in+1'b1);
  wire [s:0] nextout = (out==(LENGTH-1)) ? 1'b 0 : (out+1'b1);
  assign i0.trdy = !full;
  assign o0.irdy = !(in==out) || full;

  assign o0.data = (0 <= out && out < LENGTH) ? data$addr [out] : data$addr [LENGTH-1];

  wire writing = i0.irdy && i0.trdy; // writing into the queue
  wire reading = o0.irdy && o0.trdy; // reading from the queue

  always @(posedge clk) in <= rst ? 1'b 0 : (writing ? nextin : in);
  always @(posedge clk) out <= rst ? 1'b 0 : (reading ? nextout : out);
  always @(posedge clk) full <= (rst || reading) ? 1'b 0 : ((nextin==out && writing) ? 1'b 1 : full);

  generate
    genvar i;
    for (i = 0; i < LENGTH; i = i + 1) begin: calcNewDataTypes
        always @(posedge clk) begin
            data$addr [i] <= (writing && (in==(i))) ? i0.data : data$addr [i];
        end
    end
  endgenerate

  function [t:0] nr_of_packets;
    return full ? LENGTH : in - out + (in < out ? LENGTH : 0);
  endfunction

  function[t:0] nr_of_packets_data (logic[l:0] data);
    integer count;
    count = 0;
    for (integer i = 0; i < LENGTH; i = i + 1) begin
      count = count + matches_data(i, data);
    end
    return count;
  endfunction

  function matches_data (int position, logic[l:0] data);
    bit match;
    match = has_data(position);
    for (integer j = 0; j <= l; j = j + 1) begin
      match = match && (data[j] === 1'bX || data$addr[position][j] == data[j]);
    end
    return match;
  endfunction

  function has_data(int position);
    return (full || out <= position && position < in) ||
    (in < out && (out <= position || position < in));
  endfunction
endmodule

// Source that generates packets of type GTYPE
module Source #(GTYPE = 1'b0, DATASIZE=1) (
     input clk, input rst, input [63:0] t
    ,chan.data_output o0
  );

  localparam l = DATASIZE < 1 ? 1'b0 : DATASIZE - 1'b1;

  wire generator;
  wire newgen;
  reg pre;

  // Generator function:
  assign generator = rst? 1'b 0 : 1'b 1;
  always @(posedge clk) pre <= rst? 1'b 0 : o0.irdy && !o0.trdy;
  assign o0.irdy = 1'b 1;
  assign newgen = generator && !pre;

  // Equations:
  reg [l:0] prevo0$data;

  assign o0.data = newgen ? GTYPE : prevo0$data;
  always @(posedge clk) prevo0$data <= o0.data;
endmodule

// Sink, consumes packets, and is always ready to consume.
module Sink (
     input clk, input rst, input [63:0] t
    ,chan.data_input i0
  );
  assign i0.trdy = 1'b 1;
endmodule

// Fork, transfers the packet from input 0 to output 0 and output1
module Fork (
     input clk, input rst
    ,chan.data_input i0
    ,chan.data_output o0
    ,chan.data_output o1
  );
  assign i0.trdy = o0.trdy && o1.trdy;
  assign o0.irdy = i0.irdy && o1.trdy;
  assign o1.irdy = i0.irdy && o0.trdy;
  assign o0.data = i0.data;
  assign o1.data = i0.data;
endmodule

// Control Join, takes packets on input0 and input1.
// Outputs packet from input port 0.
module CTRLJoin (
     input clk, input rst
    ,chan.data_input i0
    ,chan.token_input i1
    ,chan.data_output o0
  );
  assign o0.irdy = i0.irdy && i1.irdy;
  assign i0.trdy = o0.trdy && i1.irdy;
  assign i1.trdy = o0.trdy && i0.irdy;
  assign o0.data = i0.data;
endmodule

// Switch that outputs packets with data type ITYPE on output 0,
//  and packets with another data type on output 1
module Switch (
     input clk, input rst
    ,chan.data_input i0
    ,switch_chan.in sw
    ,chan.data_output o0
    ,chan.data_output o1
  );
  assign i0.trdy = (o0.trdy && o0.irdy) || (o1.trdy && o1.irdy);
  assign o0.irdy = i0.irdy && !sw.sel; //selected output is output 0
  assign o1.irdy = i0.irdy && sw.sel; //selected output is output 1
  assign o0.data = sw.data0;
  assign o1.data = sw.data1;
endmodule

interface switch_chan #(SIZE0 = 1, SIZE1 = 1);

    // highest bit needed to encoded the given sizes
    localparam S0 = SIZE0 < 1 ? 0 : SIZE0 - 1;
    localparam S1 = SIZE1 < 1 ? 0 : SIZE1 - 1;

    logic sel;
    logic [S0:0] data0;
    logic [S1:0] data1;

    modport in (input sel, input data0, input data1);
    modport out (output sel, output data0, output data1);
endinterface

// Merge
module Merge (
     input clk, input rst
    ,chan.data_input i0
    ,chan.data_input i1
    ,chan.function_input fun
    ,chan.data_output o0
    ,output sel
  );
  merge2arb inarb0(
      .clk(clk), .rst(rst)
    , .i0(i0)
    , .i1(i1)
    , .o0(o0)
    , .sel(sel)
  );
  assign o0.data = fun.data;
endmodule

// -- Supporting Modules --

// Merge 2-input arbitrator
module merge2arb(
     input clk, input rst
    ,chan.data_input i0
    ,chan.data_input i1
    ,chan.data_output o0
    ,output sel
  );
  reg prevSel;
  reg transfer;

  always @(posedge clk) prevSel <= rst ? 1'b 0 : sel;
  always @(posedge clk) transfer <= rst ? 1'b 0 : o0.irdy && o0.trdy;
  assign sel = rst ? 1'b 0 : (i0.irdy && !i1.irdy) ? 1'b 0 : (i1.irdy && !i0.irdy) ? 1'b 1 : transfer ? !prevSel : prevSel;
  assign o0.irdy = i0.irdy || i1.irdy;
  assign i0.trdy = !sel && o0.trdy && i0.irdy;
  assign i1.trdy = sel && o0.trdy && i1.irdy;
endmodule

//--------------------------------------


//
// Top Level Definitions
//
// Constant value to use for data of size 0, since wire size 0 is not possible in verilog
`define TOKEN 0
// Macro for assertion on the positive edge of the clock
`define assert_clk_pos(arg, name) \
  assert property (@(posedge clk) disable iff (rst) arg) $display("Succes %s", name); else $display("Fail %s", name)
// Macro for assertion on the negative edge of the clock
`define assert_clk_neg(arg, name) \
    assert property (@(posedge clk) disable iff (rst) arg) $display("Succes %s", name); else $display("Fail %s", name)

module \pLib_top (
      input \clk , input \rst
  );

  //
  // Invariant assertions
  //
  Invariant_0:
    `assert_clk_neg(0 == (-1) * \agentP .\cq2 .nr_of_packets() + (1) * \agentQ .\cc2 .\queue .nr_of_packets() + (-1) * \agentQ .\dq2 .nr_of_packets() + (-1) * \fabric .\cx2 .nr_of_packets() + (-1) * \fabric .\dx1 .nr_of_packets_data(1'b1), "Invariant_0");
  Invariant_1:
    `assert_clk_neg(0 == (-1) * \agentP .\cq1 .nr_of_packets() + (1) * \agentQ .\cc1 .\queue .nr_of_packets() + (-1) * \agentQ .\dq1 .nr_of_packets() + (-1) * \fabric .\cx1 .nr_of_packets() + (-1) * \fabric .\dx1 .nr_of_packets_data(1'b0), "Invariant_1");
  Invariant_2:
    `assert_clk_neg(0 == (-1) * \agentP .\cc2 .\queue .nr_of_packets() + (1) * \agentP .\dq2 .nr_of_packets() + (1) * \agentQ .\cq2 .nr_of_packets() + (1) * \fabric .\cx4 .nr_of_packets() + (1) * \fabric .\dx2 .nr_of_packets_data(1'b1), "Invariant_2");
  Invariant_3:
    `assert_clk_neg(0 == (-1) * \agentP .\cc1 .\queue .nr_of_packets() + (1) * \agentP .\dq1 .nr_of_packets() + (1) * \agentQ .\cq1 .nr_of_packets() + (1) * \fabric .\cx3 .nr_of_packets() + (1) * \fabric .\dx2 .nr_of_packets_data(1'b0), "Invariant_3");
endmodule





//
// Macro modules
//
module \credit_counter_10$type0 (
      input \clk , input \rst , input [63:0] \t
    , chan \input
    , chan \output
  );

  //
  // Channel declarations
  //
  chan #(0) \source_fork ();
  chan #(0) \fork_queue ();
  chan #(0) \queue_cjoin ();
  chan #(0) \cjoin_sink ();

  //
  // Component and Macro instantiations
  //
  Source #(
    .DATASIZE(0),
    .GTYPE(0)
  ) \source  (
      .clk(\clk ), .rst(\rst ), .t(\t )
    , .o0(\source_fork )
  );

  Fork \fork  (
      .clk(\clk ), .rst(\rst )
    , .i0(\source_fork )
    , .o0(\output )
    , .o1(\fork_queue )
  );

  DQueue #(
    .DATASIZE(0),
    .LENGTH(10)
  ) \queue  (
      .clk(\clk ), .rst(\rst )
    , .i0(\fork_queue )
    , .o0(\queue_cjoin )
  );

  CTRLJoin \cjoin  (
      .clk(\clk ), .rst(\rst )
    , .i0(\input )
    , .i1(\queue_cjoin )
    , .o0(\cjoin_sink )
  );

  Sink \sink  (
      .clk(\clk ), .rst(\rst ), .t(\t )
    , .i0(\cjoin_sink )
  );

endmodule

module \credit_counter_10$type1 (
      input \clk , input \rst , input [63:0] \t
    , chan \input
    , chan \output
  );

  //
  // Channel declarations
  //
  chan #(0) \source_fork ();
  chan #(0) \fork_queue ();
  chan #(0) \queue_cjoin ();
  chan #(0) \cjoin_sink ();

  //
  // Component and Macro instantiations
  //
  Source #(
    .DATASIZE(0),
    .GTYPE(0)
  ) \source  (
      .clk(\clk ), .rst(\rst ), .t(\t )
    , .o0(\source_fork )
  );

  Fork \fork  (
      .clk(\clk ), .rst(\rst )
    , .i0(\source_fork )
    , .o0(\output )
    , .o1(\fork_queue )
  );

  DQueue #(
    .DATASIZE(0),
    .LENGTH(10)
  ) \queue  (
      .clk(\clk ), .rst(\rst )
    , .i0(\fork_queue )
    , .o0(\queue_cjoin )
  );

  CTRLJoin \cjoin  (
      .clk(\clk ), .rst(\rst )
    , .i0(\input )
    , .i1(\queue_cjoin )
    , .o0(\cjoin_sink )
  );

  Sink \sink  (
      .clk(\clk ), .rst(\rst ), .t(\t )
    , .i0(\cjoin_sink )
  );

endmodule

module \fabric (
      input \clk , input \rst
    , chan \i0
    , chan \i1
    , chan \i2
    , chan \i3
    , chan \i4
    , chan \i5
    , chan \o0
    , chan \o1
    , chan \o2
    , chan \o3
    , chan \o4
    , chan \o5
  );

  //
  // Component and Macro instantiations
  //
  DQueue #(
    .DATASIZE(1),
    .LENGTH(2)
  ) \dx1  (
      .clk(\clk ), .rst(\rst )
    , .i0(\i0 )
    , .o0(\o0 )
  );

  DQueue #(
    .DATASIZE(0),
    .LENGTH(2)
  ) \cx1  (
      .clk(\clk ), .rst(\rst )
    , .i0(\i1 )
    , .o0(\o1 )
  );

  DQueue #(
    .DATASIZE(0),
    .LENGTH(2)
  ) \cx2  (
      .clk(\clk ), .rst(\rst )
    , .i0(\i2 )
    , .o0(\o2 )
  );

  DQueue #(
    .DATASIZE(1),
    .LENGTH(2)
  ) \dx2  (
      .clk(\clk ), .rst(\rst )
    , .i0(\i3 )
    , .o0(\o3 )
  );

  DQueue #(
    .DATASIZE(0),
    .LENGTH(2)
  ) \cx3  (
      .clk(\clk ), .rst(\rst )
    , .i0(\i4 )
    , .o0(\o4 )
  );

  DQueue #(
    .DATASIZE(0),
    .LENGTH(2)
  ) \cx4  (
      .clk(\clk ), .rst(\rst )
    , .i0(\i5 )
    , .o0(\o5 )
  );

endmodule

module \delay (
      input \clk , input \rst , input [63:0] \t
    , chan \input
    , chan \output
  );

  //
  // Channel declarations
  //
  chan #(0) \fork_sink ();

  //
  // Component and Macro instantiations
  //
  Fork \fork  (
      .clk(\clk ), .rst(\rst )
    , .i0(\input )
    , .o0(\output )
    , .o1(\fork_sink )
  );

  Sink \sink  (
      .clk(\clk ), .rst(\rst ), .t(\t )
    , .i0(\fork_sink )
  );

endmodule

module \agent (
      input \clk , input \rst , input [63:0] \t
    , chan \i0
    , chan \i1
    , chan \i2
    , chan \o0
    , chan \o1
    , chan \o2
  );

  //
  // Channel declarations
  //
  chan #(0) \source_cjoin1 ();
  chan #(0) \cq1_cjoin_1 ();
  chan #(0) \cjoin1_merge ();
  chan #(0) \function_cjoin2 ();
  chan #(0) \cq2_cjoin2 ();
  chan #(0) \cjoin2_merge ();
  chan #(0) \delay_function ();
  chan #(0) \switch_dq1 ();
  chan #(0) \dq1_fork1 ();
  chan #(0) \fork1_cc1 ();
  chan #(0) \fork1_delay ();
  chan #(0) \switch_dq2 ();
  chan #(0) \dq2_fork2 ();
  chan #(0) \fork2_cc2 ();
  chan #(0) \fork2_sink ();

  //
  // Function Channels
  //
  switch_chan #(0, 0) \sfunchan_switch  ();
  chan #(1) \ofunchan_merge ();
  wire \sel_merge  ;

  //
  // Component and Macro instantiations
  //
  DQueue #(
    .DATASIZE(0),
    .LENGTH(10)
  ) \cq1  (
      .clk(\clk ), .rst(\rst )
    , .i0(\i1 )
    , .o0(\cq1_cjoin_1 )
  );

  DQueue #(
    .DATASIZE(0),
    .LENGTH(10)
  ) \cq2  (
      .clk(\clk ), .rst(\rst )
    , .i0(\i2 )
    , .o0(\cq2_cjoin2 )
  );

  DQueue #(
    .DATASIZE(0),
    .LENGTH(10)
  ) \dq1  (
      .clk(\clk ), .rst(\rst )
    , .i0(\switch_dq1 )
    , .o0(\dq1_fork1 )
  );

  DQueue #(
    .DATASIZE(0),
    .LENGTH(10)
  ) \dq2  (
      .clk(\clk ), .rst(\rst )
    , .i0(\switch_dq2 )
    , .o0(\dq2_fork2 )
  );

  FUN$agent_function \function  (
      .clk(\clk ), .rst(\rst )
    , .i0(\delay_function )
    , .o0(\function_cjoin2 )
  );

  Source #(
    .DATASIZE(0),
    .GTYPE(0)
  ) \source  (
      .clk(\clk ), .rst(\rst ), .t(\t )
    , .o0(\source_cjoin1 )
  );

  Sink \sink  (
      .clk(\clk ), .rst(\rst ), .t(\t )
    , .i0(\fork2_sink )
  );

  Fork \fork1  (
      .clk(\clk ), .rst(\rst )
    , .i0(\dq1_fork1 )
    , .o0(\fork1_delay )
    , .o1(\fork1_cc1 )
  );

  Fork \fork2  (
      .clk(\clk ), .rst(\rst )
    , .i0(\dq2_fork2 )
    , .o0(\fork2_sink )
    , .o1(\fork2_cc2 )
  );

  CTRLJoin \cjoin1  (
      .clk(\clk ), .rst(\rst )
    , .i0(\source_cjoin1 )
    , .i1(\cq1_cjoin_1 )
    , .o0(\cjoin1_merge )
  );

  CTRLJoin \cjoin2  (
      .clk(\clk ), .rst(\rst )
    , .i0(\function_cjoin2 )
    , .i1(\cq2_cjoin2 )
    , .o0(\cjoin2_merge )
  );

  Switch \switch  (
      .clk(\clk ), .rst(\rst )
    , .i0(\i0 )
    , .sw(\sfunchan_switch )
    , .o0(\switch_dq1 )
    , .o1(\switch_dq2 )
  );

  \SFUN$agent_switch  \sfun_switch  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0 (\i0 )
    , .\o0 (\sfunchan_switch )
  );

  Merge \merge  (
      .clk(\clk ), .rst(\rst )
    , .i0(\cjoin1_merge )
    , .i1(\cjoin2_merge )
    , .fun(\ofunchan_merge )
    , .sel(\sel_merge )
    , .o0(\o0 )
  );

  \OFUN$agent_merge  \ofun_merge  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0 (\cjoin1_merge )
    , .\i1 (\cjoin2_merge )
    , .\sel (\sel_merge )
    , .\o0 (\ofunchan_merge )
  );

  \delay  \delay  (
      .\clk (\clk ), .\rst (\rst ), .\t (\t )
    , .\input (\fork1_delay )
    , .\output (\delay_function )
  );

  \credit_counter_10$type0  \cc1  (
      .\clk (\clk ), .\rst (\rst ), .\t (\t )
    , .\input (\fork1_cc1 )
    , .\output (\o1 )
  );

  \credit_counter_10$type1  \cc2  (
      .\clk (\clk ), .\rst (\rst ), .\t (\t )
    , .\input (\fork2_cc2 )
    , .\output (\o2 )
  );

endmodule


//
// agent function components
//
module \FUN$agent_function (
      input \clk , input \rst
    , chan.data_input \i0
    , chan.data_output \o0
  );
  assign \i0 .trdy  = \o0 .trdy ;
  assign \o0 .irdy  = \i0 .irdy ;

  //
  // Function logic
  //
  wire \f  = `TOKEN ;

  assign \o0 .data  = \f  ;
endmodule


//
// agent switch functions
//
module \SFUN$agent_switch (
      input \clk , input \rst
    , chan.function_input \i0
    , switch_chan.out \o0
  );

  //
  // Function logic
  //
  wire \match0req  = \i0 .data[0:0] == 1'd 0 ;
  wire \match0  = \match0req  ;
  wire \match1rsp  = \i0 .data[0:0] == 1'd 1 ;
  wire \match1  = \match1rsp  ;

  //
  // Data variables
  //
  wire \data0  = `TOKEN ;
  wire \data1  = `TOKEN ;

  assign \o0 .sel  = \match0  ? 1'd 0 : 1'd 1 ;
  assign \o0 .data0  = \match0  ? \data0  : 1'b 0 ;
  assign \o0 .data1  = \match1  ? \data1  : 1'b 0 ;
endmodule

module \OFUN$agent_merge (
      input \clk , input \rst
    , chan.function_input \i0
    , chan.function_input \i1
    , input \sel
    , chan.function_output \o0
  );

  //
  // Function logic
  //
  wire[0:0] \f$sel  = \sel  ;
  wire[0:0] \f$0  = 0 ;
  wire[0:0] \f$1  = 1 ;
  wire[0:0] \f  = \f$sel  [0:0] == 0 ? \f$0  : \f$sel  [0:0] == 1 ? \f$1  : 1'b 0 ;

  assign \o0 .data  = \f  ;
endmodule


//
// Top level module
//
module \top (
      input \clk , input \rst , input [63:0] \t
  );

  //
  // Channel declarations
  //
  chan #(1) \agentP-o0_fabric-i0 ();
  chan #(0) \agentP-o1_fabric-i4 ();
  chan #(0) \agentP-o2_fabric-i5 ();
  chan #(1) \agentQ-o0_fabric-i3 ();
  chan #(0) \agentQ-o1_fabric-i1 ();
  chan #(0) \agentQ-o2_fabric-i2 ();
  chan #(1) \fabric-o0_agentQ_i0 ();
  chan #(0) \fabric-o1_agentP-i1 ();
  chan #(0) \fabric-o2_agentP-i2 ();
  chan #(1) \fabric-o3_agentP-i0 ();
  chan #(0) \fabric-o4_agentQ-i1 ();
  chan #(0) \fabric-o5_agentQ-i2 ();

  //
  // Component and Macro instantiations
  //
  \agent  \agentP  (
      .\clk (\clk ), .\rst (\rst ), .\t (\t )
    , .\i0 (\fabric-o3_agentP-i0 )
    , .\i1 (\fabric-o1_agentP-i1 )
    , .\i2 (\fabric-o2_agentP-i2 )
    , .\o0 (\agentP-o0_fabric-i0 )
    , .\o1 (\agentP-o1_fabric-i4 )
    , .\o2 (\agentP-o2_fabric-i5 )
  );

  \agent  \agentQ  (
      .\clk (\clk ), .\rst (\rst ), .\t (\t )
    , .\i0 (\fabric-o0_agentQ_i0 )
    , .\i1 (\fabric-o4_agentQ-i1 )
    , .\i2 (\fabric-o5_agentQ-i2 )
    , .\o0 (\agentQ-o0_fabric-i3 )
    , .\o1 (\agentQ-o1_fabric-i1 )
    , .\o2 (\agentQ-o2_fabric-i2 )
  );

  \fabric  \fabric  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0 (\agentP-o0_fabric-i0 )
    , .\i1 (\agentQ-o1_fabric-i1 )
    , .\i2 (\agentQ-o2_fabric-i2 )
    , .\i3 (\agentQ-o0_fabric-i3 )
    , .\i4 (\agentP-o1_fabric-i4 )
    , .\i5 (\agentP-o2_fabric-i5 )
    , .\o0 (\fabric-o0_agentQ_i0 )
    , .\o1 (\fabric-o1_agentP-i1 )
    , .\o2 (\fabric-o2_agentP-i2 )
    , .\o3 (\fabric-o3_agentP-i0 )
    , .\o4 (\fabric-o4_agentQ-i1 )
    , .\o5 (\fabric-o5_agentQ-i2 )
  );

endmodule

//
// Wrapper module
//
module \wrapper (
      input \clk , input \rst , input [63:0] \t
  );
  \top  \top  (
      .\clk (\clk ), .\rst (\rst ), .\t (\t )
  );

  bind \top  \pLib_top  \top_assertions  (
      .\clk (\clk ), .\rst (\rst )
  );
endmodule