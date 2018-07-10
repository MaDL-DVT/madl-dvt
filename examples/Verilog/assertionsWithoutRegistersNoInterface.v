
//
// Top Level Definitions
//
// Constant value to use for data of size 0, since wire size 0 is not possible in verilog
`define TOKEN 0

//
// Included files
//
module \arbiter2 (
      input \clk , input \rst
    , input \client0
    , input \client1
    , input \transfer
    , output [0:0] \sel
  );
  reg [0:0] prevSel;
  reg transferReg;

  always @(posedge clk) prevSel <= rst ? 1'b 0 : sel;
  always @(posedge clk) transferReg <= rst ? 1'b 0 : transfer;
  assign \sel  = ( rst ? 1'b 0 : ( (!client0) ? 1'd1 : ( (!client1) ? 1'd0 : ( transferReg ? ( (prevSel == 1'd1) ? 1'd0 : 1'd1 ) : prevSel ) ) ) ) ;
endmodule

module \CTRLJoin2 #(
    INPUTSIZE1 = 1,
    OUTPUTSIZE = 1,
    INPUTSIZE0 = 1
  ) (
      input \clk , input \rst
    , input \i0$irdy , input [INPUTSIZE0-1:0] \i0$data , output \i0$trdy
    , input \i1$irdy , input [INPUTSIZE1-1:0] \i1$data , output \i1$trdy
    , output \o0$irdy , output [OUTPUTSIZE-1:0] \o0$data , input \o0$trdy
  );
  assign \i0$trdy  = (\o0$trdy  && \i1$irdy ) ;
  assign \i1$trdy  = (\o0$trdy  && \i0$irdy ) ;
  assign \o0$irdy  = (\i0$irdy  && \i1$irdy ) ;
  assign \o0$data  = \i0$data  ;
endmodule

module \Fork2 #(
    DATASIZE = 1
  ) (
      input \clk , input \rst
    , input \i0$irdy , input [DATASIZE-1:0] \i0$data , output \i0$trdy
    , output \o0$irdy , output [DATASIZE-1:0] \o0$data , input \o0$trdy
    , output \o1$irdy , output [DATASIZE-1:0] \o1$data , input \o1$trdy
  );
  assign \i0$trdy  = (\o0$trdy  && \o1$trdy ) ;
  assign \o0$irdy  = (\i0$irdy  && \o1$trdy ) ;
  assign \o1$irdy  = (\i0$irdy  && \o0$trdy ) ;
  assign \o0$data  = \i0$data  ;
  assign \o1$data  = \i0$data  ;
endmodule

module \Merge2 #(
    INPUTSIZE1 = 1,
    OUTPUTSIZE = 1,
    INPUTSIZE0 = 1
  ) (
      input \clk , input \rst
    , input \i0$irdy , input [INPUTSIZE0-1:0] \i0$data , output \i0$trdy
    , input \i1$irdy , input [INPUTSIZE1-1:0] \i1$data , output \i1$trdy
    , output \o0$irdy , output [OUTPUTSIZE-1:0] \o0$data , input \o0$trdy
    , input [OUTPUTSIZE-1:0] \f$data
    , output \sel
  );
  \arbiter2  \arb  (
      .\clk (\clk ), .\rst (\rst )
    , .\client0 (\i0$irdy )
    , .\client1 (\i1$irdy )
    , .\transfer ((\o0$irdy  && \o0$trdy ))
    , .\sel (\sel )
  );

  assign \i0$trdy  = (((\sel  == 1'd0) && \i0$irdy ) && \o0$trdy ) ;
  assign \i1$trdy  = (((\sel  == 1'd1) && \i1$irdy ) && \o0$trdy ) ;
  assign \o0$irdy  = (\i0$irdy  || \i1$irdy ) ;
  assign \o0$data  = \f$data  ;
endmodule

module \Queue #(
    DATASIZE = 1,
    LENGTH = 1
  ) (
      input \clk , input \rst
    , input \i0$irdy , input [DATASIZE-1:0] \i0$data , output \i0$trdy
    , output \o0$irdy , output [DATASIZE-1:0] \o0$data , input \o0$trdy
  );
  // highest bit needed to encode LENGTH positions
  localparam s = LENGTH < 2 ? 0 : $clog2(LENGTH) - 1;
  localparam t = (LENGTH + 1) < 2 ? 0 : $clog2(LENGTH + 1) - 1;
  localparam l = DATASIZE < 1 ? 0 : DATASIZE - 1;

  reg [s:0] in;
  reg [s:0] out;
  reg [l:0] data$addr [0:(LENGTH-1)];
  reg full;

  wire [s:0] nextin = (in==(LENGTH-1)) ? 1'b 0 : (in+1'b1);
  wire [s:0] nextout = (out==(LENGTH-1)) ? 1'b 0 : (out+1'b1);
  assign \i0$trdy  = !full ;
  assign \o0$irdy  = !(in==out) || full ;
  assign \o0$data  = (0 <= out && out < LENGTH) ? data$addr [out] : data$addr [LENGTH-1] ;
  wire \writing  = (\i0$irdy  && \i0$trdy ) ;
  wire \reading  = (\o0$irdy  && \o0$trdy ) ;

  always @(posedge clk) in <= rst ? 1'b 0 : (writing ? nextin : in);
  always @(posedge clk) out <= rst ? 1'b 0 : (reading ? nextout : out);
  always @(posedge clk) full <= (rst || reading) ? 1'b 0 : ((nextin==out && writing) ? 1'b 1 : full);

  generate
    genvar i;
    for (i = 0; i < LENGTH; i = i + 1) begin: calcNewDataTypes
        always @(posedge clk) begin
            data$addr [i] <= (writing && (in==(i))) ? \i0$data  : data$addr [i];
        end
    end
  endgenerate

endmodule

module \Sink #(
    DATASIZE = 1,
    TRDY = 1'b 1
  ) (
      input \clk , input \rst , input [63:0] \t
    , input \i0$irdy , input [DATASIZE-1:0] \i0$data , output \i0$trdy
  );
  assign \i0$trdy  = TRDY ;
endmodule

module \Source #(
    DATASIZE = 1,
    GTYPE = 0
  ) (
      input \clk , input \rst , input [63:0] \t
    , output \o0$irdy , output [DATASIZE-1:0] \o0$data , input \o0$trdy
  );
  assign \o0$irdy  = 1'd1 ;
  assign \o0$data  = GTYPE ;
endmodule

module \Switch2 #(
    OUTPUTSIZE0 = 1,
    OUTPUTSIZE1 = 1,
    INPUTSIZE = 1
  ) (
      input \clk , input \rst
    , input \i0$irdy , input [INPUTSIZE-1:0] \i0$data , output \i0$trdy
    , output \o0$irdy , output [OUTPUTSIZE0-1:0] \o0$data , input \o0$trdy
    , output \o1$irdy , output [OUTPUTSIZE1-1:0] \o1$data , input \o1$trdy
    , input [0:0] \sel$data
    , input [OUTPUTSIZE0-1:0] \f0$data
    , input [OUTPUTSIZE1-1:0] \f1$data
  );
  assign \i0$trdy  = ((\o0$irdy  && \o0$trdy ) || (\o1$irdy  && \o1$trdy )) ;
  assign \o0$irdy  = (\i0$irdy  && (\sel$data  == 1'd0)) ;
  assign \o1$irdy  = (\i0$irdy  && (\sel$data  == 1'd1)) ;
  assign \o0$data  = \f0$data  ;
  assign \o1$data  = \f1$data  ;
endmodule

//
// Macro modules
//
module \credit_counter_10$type0 (
      input \clk , input \rst , input [63:0] \t
    , input \input$irdy , input [0:0] \input$data , output \input$trdy
    , output \output$irdy , output [0:0] \output$data , input \output$trdy
  );

  //
  // Channel declarations
  //
  wire \cjoin_sink$irdy  ;
  wire \cjoin_sink$data  ;
  wire \cjoin_sink$trdy  ;
  wire \queue_cjoin$irdy  ;
  wire \queue_cjoin$data  ;
  wire \queue_cjoin$trdy  ;
  wire \fork_queue$irdy  ;
  wire \fork_queue$data  ;
  wire \fork_queue$trdy  ;
  wire \source_fork$irdy  ;
  wire \source_fork$data  ;
  wire \source_fork$trdy  ;

  //
  // Component and Macro instantiations
  //
  \Source  #(
    .DATASIZE(1),
    .GTYPE(0)
  ) \PatientSource1  (
      .\clk (\clk ), .\rst (\rst ), .\t (\t )
    , .\o0$irdy (\source_fork$irdy )
    , .\o0$data (\source_fork$data )
    , .\o0$trdy (\source_fork$trdy )
  );

  \Fork2  #(
    .DATASIZE(1)
  ) \Fork1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\source_fork$irdy )
    , .\i0$data (\source_fork$data )
    , .\i0$trdy (\source_fork$trdy )
    , .\o0$irdy (\output$irdy )
    , .\o0$data (\output$data )
    , .\o0$trdy (\output$trdy )
    , .\o1$irdy (\fork_queue$irdy )
    , .\o1$data (\fork_queue$data )
    , .\o1$trdy (\fork_queue$trdy )
  );

  \Queue  #(
    .DATASIZE(1),
    .LENGTH(10)
  ) \Queue1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\fork_queue$irdy )
    , .\i0$data (\fork_queue$data )
    , .\i0$trdy (\fork_queue$trdy )
    , .\o0$irdy (\queue_cjoin$irdy )
    , .\o0$data (\queue_cjoin$data )
    , .\o0$trdy (\queue_cjoin$trdy )
  );

  \CTRLJoin2  #(
    .INPUTSIZE1(1),
    .OUTPUTSIZE(1),
    .INPUTSIZE0(1)
  ) \CtrlJoin1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\input$irdy )
    , .\i0$data (\input$data )
    , .\i0$trdy (\input$trdy )
    , .\i1$irdy (\queue_cjoin$irdy )
    , .\i1$data (\queue_cjoin$data )
    , .\i1$trdy (\queue_cjoin$trdy )
    , .\o0$irdy (\cjoin_sink$irdy )
    , .\o0$data (\cjoin_sink$data )
    , .\o0$trdy (\cjoin_sink$trdy )
  );

  \Sink  #(
    .DATASIZE(1),
    .TRDY(1'b 1)
  ) \Sink1  (
      .\clk (\clk ), .\rst (\rst ), .\t (\t )
    , .\i0$irdy (\cjoin_sink$irdy )
    , .\i0$data (\cjoin_sink$data )
    , .\i0$trdy (\cjoin_sink$trdy )
  );

endmodule

module \credit_counter_10$type1 (
      input \clk , input \rst , input [63:0] \t
    , input \input$irdy , input [0:0] \input$data , output \input$trdy
    , output \output$irdy , output [0:0] \output$data , input \output$trdy
  );

  //
  // Channel declarations
  //
  wire \cjoin_sink$irdy  ;
  wire \cjoin_sink$data  ;
  wire \cjoin_sink$trdy  ;
  wire \queue_cjoin$irdy  ;
  wire \queue_cjoin$data  ;
  wire \queue_cjoin$trdy  ;
  wire \fork_queue$irdy  ;
  wire \fork_queue$data  ;
  wire \fork_queue$trdy  ;
  wire \source_fork$irdy  ;
  wire \source_fork$data  ;
  wire \source_fork$trdy  ;

  //
  // Component and Macro instantiations
  //
  \Source  #(
    .DATASIZE(1),
    .GTYPE(0)
  ) \PatientSource1  (
      .\clk (\clk ), .\rst (\rst ), .\t (\t )
    , .\o0$irdy (\source_fork$irdy )
    , .\o0$data (\source_fork$data )
    , .\o0$trdy (\source_fork$trdy )
  );

  \Fork2  #(
    .DATASIZE(1)
  ) \Fork1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\source_fork$irdy )
    , .\i0$data (\source_fork$data )
    , .\i0$trdy (\source_fork$trdy )
    , .\o0$irdy (\output$irdy )
    , .\o0$data (\output$data )
    , .\o0$trdy (\output$trdy )
    , .\o1$irdy (\fork_queue$irdy )
    , .\o1$data (\fork_queue$data )
    , .\o1$trdy (\fork_queue$trdy )
  );

  \Queue  #(
    .DATASIZE(1),
    .LENGTH(10)
  ) \Queue1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\fork_queue$irdy )
    , .\i0$data (\fork_queue$data )
    , .\i0$trdy (\fork_queue$trdy )
    , .\o0$irdy (\queue_cjoin$irdy )
    , .\o0$data (\queue_cjoin$data )
    , .\o0$trdy (\queue_cjoin$trdy )
  );

  \CTRLJoin2  #(
    .INPUTSIZE1(1),
    .OUTPUTSIZE(1),
    .INPUTSIZE0(1)
  ) \CtrlJoin1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\input$irdy )
    , .\i0$data (\input$data )
    , .\i0$trdy (\input$trdy )
    , .\i1$irdy (\queue_cjoin$irdy )
    , .\i1$data (\queue_cjoin$data )
    , .\i1$trdy (\queue_cjoin$trdy )
    , .\o0$irdy (\cjoin_sink$irdy )
    , .\o0$data (\cjoin_sink$data )
    , .\o0$trdy (\cjoin_sink$trdy )
  );

  \Sink  #(
    .DATASIZE(1),
    .TRDY(1'b 1)
  ) \Sink1  (
      .\clk (\clk ), .\rst (\rst ), .\t (\t )
    , .\i0$irdy (\cjoin_sink$irdy )
    , .\i0$data (\cjoin_sink$data )
    , .\i0$trdy (\cjoin_sink$trdy )
  );

endmodule

module \Fabric (
      input \clk , input \rst
    , input \i0$irdy , input [0:0] \i0$data , output \i0$trdy
    , input \i1$irdy , input [0:0] \i1$data , output \i1$trdy
    , input \i2$irdy , input [0:0] \i2$data , output \i2$trdy
    , input \i3$irdy , input [0:0] \i3$data , output \i3$trdy
    , input \i4$irdy , input [0:0] \i4$data , output \i4$trdy
    , input \i5$irdy , input [0:0] \i5$data , output \i5$trdy
    , output \o0$irdy , output [0:0] \o0$data , input \o0$trdy
    , output \o1$irdy , output [0:0] \o1$data , input \o1$trdy
    , output \o2$irdy , output [0:0] \o2$data , input \o2$trdy
    , output \o3$irdy , output [0:0] \o3$data , input \o3$trdy
    , output \o4$irdy , output [0:0] \o4$data , input \o4$trdy
    , output \o5$irdy , output [0:0] \o5$data , input \o5$trdy
  );

  //
  // Component and Macro instantiations
  //
  \Queue  #(
    .DATASIZE(1),
    .LENGTH(2)
  ) \Queue1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\i0$irdy )
    , .\i0$data (\i0$data )
    , .\i0$trdy (\i0$trdy )
    , .\o0$irdy (\o0$irdy )
    , .\o0$data (\o0$data )
    , .\o0$trdy (\o0$trdy )
  );

  \Queue  #(
    .DATASIZE(1),
    .LENGTH(2)
  ) \Queue2  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\i1$irdy )
    , .\i0$data (\i1$data )
    , .\i0$trdy (\i1$trdy )
    , .\o0$irdy (\o1$irdy )
    , .\o0$data (\o1$data )
    , .\o0$trdy (\o1$trdy )
  );

  \Queue  #(
    .DATASIZE(1),
    .LENGTH(2)
  ) \Queue3  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\i2$irdy )
    , .\i0$data (\i2$data )
    , .\i0$trdy (\i2$trdy )
    , .\o0$irdy (\o2$irdy )
    , .\o0$data (\o2$data )
    , .\o0$trdy (\o2$trdy )
  );

  \Queue  #(
    .DATASIZE(1),
    .LENGTH(2)
  ) \Queue4  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\i3$irdy )
    , .\i0$data (\i3$data )
    , .\i0$trdy (\i3$trdy )
    , .\o0$irdy (\o3$irdy )
    , .\o0$data (\o3$data )
    , .\o0$trdy (\o3$trdy )
  );

  \Queue  #(
    .DATASIZE(1),
    .LENGTH(2)
  ) \Queue5  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\i4$irdy )
    , .\i0$data (\i4$data )
    , .\i0$trdy (\i4$trdy )
    , .\o0$irdy (\o4$irdy )
    , .\o0$data (\o4$data )
    , .\o0$trdy (\o4$trdy )
  );

  \Queue  #(
    .DATASIZE(1),
    .LENGTH(2)
  ) \Queue6  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\i5$irdy )
    , .\i0$data (\i5$data )
    , .\i0$trdy (\i5$trdy )
    , .\o0$irdy (\o5$irdy )
    , .\o0$data (\o5$data )
    , .\o0$trdy (\o5$trdy )
  );

endmodule

module \Delay (
      input \clk , input \rst , input [63:0] \t
    , input \input$irdy , input [0:0] \input$data , output \input$trdy
    , output \output$irdy , output [0:0] \output$data , input \output$trdy
  );

  //
  // Channel declarations
  //
  wire \fork_sink$irdy  ;
  wire \fork_sink$data  ;
  wire \fork_sink$trdy  ;

  //
  // Component and Macro instantiations
  //
  \Fork2  #(
    .DATASIZE(1)
  ) \Fork1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\input$irdy )
    , .\i0$data (\input$data )
    , .\i0$trdy (\input$trdy )
    , .\o0$irdy (\output$irdy )
    , .\o0$data (\output$data )
    , .\o0$trdy (\output$trdy )
    , .\o1$irdy (\fork_sink$irdy )
    , .\o1$data (\fork_sink$data )
    , .\o1$trdy (\fork_sink$trdy )
  );

  \Sink  #(
    .DATASIZE(1),
    .TRDY(1'b 1)
  ) \Sink1  (
      .\clk (\clk ), .\rst (\rst ), .\t (\t )
    , .\i0$irdy (\fork_sink$irdy )
    , .\i0$data (\fork_sink$data )
    , .\i0$trdy (\fork_sink$trdy )
  );

endmodule

module \Agent (
      input \clk , input \rst , input [63:0] \t
    , input \i0$irdy , input [0:0] \i0$data , output \i0$trdy
    , input \i1$irdy , input [0:0] \i1$data , output \i1$trdy
    , input \i2$irdy , input [0:0] \i2$data , output \i2$trdy
    , output \o0$irdy , output [0:0] \o0$data , input \o0$trdy
    , output \o1$irdy , output [0:0] \o1$data , input \o1$trdy
    , output \o2$irdy , output [0:0] \o2$data , input \o2$trdy
  );

  //
  // Channel declarations
  //
  wire \fork2_sink$irdy  ;
  wire \fork2_sink$data  ;
  wire \fork2_sink$trdy  ;
  wire \fork2_cc2$irdy  ;
  wire \fork2_cc2$data  ;
  wire \fork2_cc2$trdy  ;
  wire \dq2_fork2$irdy  ;
  wire \dq2_fork2$data  ;
  wire \dq2_fork2$trdy  ;
  wire \switch_dq2$irdy  ;
  wire \switch_dq2$data  ;
  wire \switch_dq2$trdy  ;
  wire \fork1_delay$irdy  ;
  wire \fork1_delay$data  ;
  wire \fork1_delay$trdy  ;
  wire \fork1_cc1$irdy  ;
  wire \fork1_cc1$data  ;
  wire \fork1_cc1$trdy  ;
  wire \dq1_fork1$irdy  ;
  wire \dq1_fork1$data  ;
  wire \dq1_fork1$trdy  ;
  wire \switch_dq1$irdy  ;
  wire \switch_dq1$data  ;
  wire \switch_dq1$trdy  ;
  wire \delay_function$irdy  ;
  wire \delay_function$data  ;
  wire \delay_function$trdy  ;
  wire \cjoin2_merge$irdy  ;
  wire \cjoin2_merge$data  ;
  wire \cjoin2_merge$trdy  ;
  wire \cq2_cjoin2$irdy  ;
  wire \cq2_cjoin2$data  ;
  wire \cq2_cjoin2$trdy  ;
  wire \function_cjoin2$irdy  ;
  wire \function_cjoin2$data  ;
  wire \function_cjoin2$trdy  ;
  wire \cjoin1_merge$irdy  ;
  wire \cjoin1_merge$data  ;
  wire \cjoin1_merge$trdy  ;
  wire \cq1_cjoin_1$irdy  ;
  wire \cq1_cjoin_1$data  ;
  wire \cq1_cjoin_1$trdy  ;
  wire \source_cjoin1$irdy  ;
  wire \source_cjoin1$data  ;
  wire \source_cjoin1$trdy  ;

  //
  // Function Channels
  //
  wire \sfunchan_0_Switch1$data  ;
  wire \ofunchan_1_Switch1$data  ;
  wire \ofunchan_2_Switch1$data  ;
  wire \ofunchan_0_Merge1$data  ;
  wire \sel_Merge1  ;

  //
  // Component and Macro instantiations
  //
  \Queue  #(
    .DATASIZE(1),
    .LENGTH(10)
  ) \Queue1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\i1$irdy )
    , .\i0$data (\i1$data )
    , .\i0$trdy (\i1$trdy )
    , .\o0$irdy (\cq1_cjoin_1$irdy )
    , .\o0$data (\cq1_cjoin_1$data )
    , .\o0$trdy (\cq1_cjoin_1$trdy )
  );

  \Queue  #(
    .DATASIZE(1),
    .LENGTH(10)
  ) \Queue2  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\i2$irdy )
    , .\i0$data (\i2$data )
    , .\i0$trdy (\i2$trdy )
    , .\o0$irdy (\cq2_cjoin2$irdy )
    , .\o0$data (\cq2_cjoin2$data )
    , .\o0$trdy (\cq2_cjoin2$trdy )
  );

  \Queue  #(
    .DATASIZE(1),
    .LENGTH(10)
  ) \Queue3  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\switch_dq1$irdy )
    , .\i0$data (\switch_dq1$data )
    , .\i0$trdy (\switch_dq1$trdy )
    , .\o0$irdy (\dq1_fork1$irdy )
    , .\o0$data (\dq1_fork1$data )
    , .\o0$trdy (\dq1_fork1$trdy )
  );

  \Queue  #(
    .DATASIZE(1),
    .LENGTH(10)
  ) \Queue4  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\switch_dq2$irdy )
    , .\i0$data (\switch_dq2$data )
    , .\i0$trdy (\switch_dq2$trdy )
    , .\o0$irdy (\dq2_fork2$irdy )
    , .\o0$data (\dq2_fork2$data )
    , .\o0$trdy (\dq2_fork2$trdy )
  );

  \FUN$Agent_Function1  \Function1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\delay_function$irdy )
    , .\i0$data (\delay_function$data )
    , .\i0$trdy (\delay_function$trdy )
    , .\o0$irdy (\function_cjoin2$irdy )
    , .\o0$data (\function_cjoin2$data )
    , .\o0$trdy (\function_cjoin2$trdy )
  );

  \Source  #(
    .DATASIZE(1),
    .GTYPE(0)
  ) \Source1  (
      .\clk (\clk ), .\rst (\rst ), .\t (\t )
    , .\o0$irdy (\source_cjoin1$irdy )
    , .\o0$data (\source_cjoin1$data )
    , .\o0$trdy (\source_cjoin1$trdy )
  );

  \Sink  #(
    .DATASIZE(1),
    .TRDY(1'b 1)
  ) \Sink1  (
      .\clk (\clk ), .\rst (\rst ), .\t (\t )
    , .\i0$irdy (\fork2_sink$irdy )
    , .\i0$data (\fork2_sink$data )
    , .\i0$trdy (\fork2_sink$trdy )
  );

  \Fork2  #(
    .DATASIZE(1)
  ) \Fork1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\dq1_fork1$irdy )
    , .\i0$data (\dq1_fork1$data )
    , .\i0$trdy (\dq1_fork1$trdy )
    , .\o0$irdy (\fork1_delay$irdy )
    , .\o0$data (\fork1_delay$data )
    , .\o0$trdy (\fork1_delay$trdy )
    , .\o1$irdy (\fork1_cc1$irdy )
    , .\o1$data (\fork1_cc1$data )
    , .\o1$trdy (\fork1_cc1$trdy )
  );

  \Fork2  #(
    .DATASIZE(1)
  ) \Fork2  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\dq2_fork2$irdy )
    , .\i0$data (\dq2_fork2$data )
    , .\i0$trdy (\dq2_fork2$trdy )
    , .\o0$irdy (\fork2_sink$irdy )
    , .\o0$data (\fork2_sink$data )
    , .\o0$trdy (\fork2_sink$trdy )
    , .\o1$irdy (\fork2_cc2$irdy )
    , .\o1$data (\fork2_cc2$data )
    , .\o1$trdy (\fork2_cc2$trdy )
  );

  \CTRLJoin2  #(
    .INPUTSIZE1(1),
    .OUTPUTSIZE(1),
    .INPUTSIZE0(1)
  ) \CtrlJoin1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\source_cjoin1$irdy )
    , .\i0$data (\source_cjoin1$data )
    , .\i0$trdy (\source_cjoin1$trdy )
    , .\i1$irdy (\cq1_cjoin_1$irdy )
    , .\i1$data (\cq1_cjoin_1$data )
    , .\i1$trdy (\cq1_cjoin_1$trdy )
    , .\o0$irdy (\cjoin1_merge$irdy )
    , .\o0$data (\cjoin1_merge$data )
    , .\o0$trdy (\cjoin1_merge$trdy )
  );

  \CTRLJoin2  #(
    .INPUTSIZE1(1),
    .OUTPUTSIZE(1),
    .INPUTSIZE0(1)
  ) \CtrlJoin2  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\function_cjoin2$irdy )
    , .\i0$data (\function_cjoin2$data )
    , .\i0$trdy (\function_cjoin2$trdy )
    , .\i1$irdy (\cq2_cjoin2$irdy )
    , .\i1$data (\cq2_cjoin2$data )
    , .\i1$trdy (\cq2_cjoin2$trdy )
    , .\o0$irdy (\cjoin2_merge$irdy )
    , .\o0$data (\cjoin2_merge$data )
    , .\o0$trdy (\cjoin2_merge$trdy )
  );

  \Switch2  #(
    .OUTPUTSIZE0(1),
    .OUTPUTSIZE1(1),
    .INPUTSIZE(1)
  ) \Switch1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\i0$irdy )
    , .\i0$data (\i0$data )
    , .\i0$trdy (\i0$trdy )
    , .\sel$data (\sfunchan_0_Switch1$data )
    , .\f0$data (\ofunchan_1_Switch1$data )
    , .\f1$data (\ofunchan_2_Switch1$data )
    , .\o0$irdy (\switch_dq1$irdy )
    , .\o0$data (\switch_dq1$data )
    , .\o0$trdy (\switch_dq1$trdy )
    , .\o1$irdy (\switch_dq2$irdy )
    , .\o1$data (\switch_dq2$data )
    , .\o1$trdy (\switch_dq2$trdy )
  );

  \SFUN_0$Agent_Switch1  \sfun_0_Switch1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\i0$data )
    , .\o0 (\sfunchan_0_Switch1$data )
  );

  \OFUN_1$Agent_Switch1  \ofun_1_Switch1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\i0$data )
    , .\o0 (\ofunchan_1_Switch1$data )
  );

  \OFUN_2$Agent_Switch1  \ofun_2_Switch1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\i0$data )
    , .\o0 (\ofunchan_2_Switch1$data )
  );

  \Merge2  #(
    .INPUTSIZE1(1),
    .OUTPUTSIZE(1),
    .INPUTSIZE0(1)
  ) \Merge1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\cjoin1_merge$irdy )
    , .\i0$data (\cjoin1_merge$data )
    , .\i0$trdy (\cjoin1_merge$trdy )
    , .\i1$irdy (\cjoin2_merge$irdy )
    , .\i1$data (\cjoin2_merge$data )
    , .\i1$trdy (\cjoin2_merge$trdy )
    , .\f$data (\ofunchan_0_Merge1$data )
    , .\sel (\sel_Merge1 )
    , .\o0$irdy (\o0$irdy )
    , .\o0$data (\o0$data )
    , .\o0$trdy (\o0$trdy )
  );

  \OFUN_0$Agent_Merge1  \ofun_0_Merge1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\cjoin1_merge$data )
    , .\i1$data (\cjoin2_merge$data )
    , .\sel (\sel_Merge1 )
    , .\o0 (\ofunchan_0_Merge1$data )
  );

  \Delay  \Delay1  (
      .\clk (\clk ), .\rst (\rst ), .\t (\t )
    , .\input$irdy (\fork1_delay$irdy )
    , .\input$data (\fork1_delay$data )
    , .\input$trdy (\fork1_delay$trdy )
    , .\output$irdy (\delay_function$irdy )
    , .\output$data (\delay_function$data )
    , .\output$trdy (\delay_function$trdy )
  );

  \credit_counter_10$type0  \credit_counter_101  (
      .\clk (\clk ), .\rst (\rst ), .\t (\t )
    , .\input$irdy (\fork1_cc1$irdy )
    , .\input$data (\fork1_cc1$data )
    , .\input$trdy (\fork1_cc1$trdy )
    , .\output$irdy (\o1$irdy )
    , .\output$data (\o1$data )
    , .\output$trdy (\o1$trdy )
  );

  \credit_counter_10$type1  \credit_counter_102  (
      .\clk (\clk ), .\rst (\rst ), .\t (\t )
    , .\input$irdy (\fork2_cc2$irdy )
    , .\input$data (\fork2_cc2$data )
    , .\input$trdy (\fork2_cc2$trdy )
    , .\output$irdy (\o2$irdy )
    , .\output$data (\o2$data )
    , .\output$trdy (\o2$trdy )
  );

endmodule


//
// Agent function components
//
module \FUN$Agent_Function1 (
      input \clk , input \rst
    , input \i0$irdy , input [0:0] \i0$data , output \i0$trdy
    , output \o0$irdy , output [0:0] \o0$data , input \o0$trdy
  );
  assign \i0$trdy  = \o0$trdy  ;
  assign \o0$irdy  = \i0$irdy  ;

  //
  // Function logic
  //
  wire \f  = `TOKEN ;

  assign \o0$data  = \f  ;
endmodule


//
// Agent switch functions
//
module \SFUN_0$Agent_Switch1 (
      input \clk , input \rst
    , input [0:0] \i0$data
    , output [0:0] \o0
  );

  //
  // Function logic
  //
  wire[0:0] \f$bool$g0  = \i0$data  ;
  wire[0:0] \f$bool$f$arg0  = \f$bool$g0  ;
  wire \f$bool$f$arg1  = `TOKEN ;
  wire \f$bool$f  = (\f$bool$f$arg0 [0:0] == 1'd0) ;
  wire \f$bool  = \f$bool$f  ;
  wire[0:0] \f$true$content  = 1'd0 ;
  wire[0:0] \f$true  = \f$true$content  ;
  wire[0:0] \f$false$bool$g0  = \i0$data  ;
  wire[0:0] \f$false$bool$f$arg0  = \f$false$bool$g0  ;
  wire \f$false$bool$f$arg1  = `TOKEN ;
  wire \f$false$bool$f  = (\f$false$bool$f$arg0 [0:0] == 1'd1) ;
  wire \f$false$bool  = \f$false$bool$f  ;
  wire[0:0] \f$false$true$content  = 1'd1 ;
  wire[0:0] \f$false$true  = \f$false$true$content  ;
  wire[0:0] \f$false$false$content  = 1'd0 ;
  wire[0:0] \f$false$false  = \f$false$false$content  ;
  wire[0:0] \f$false  = ( \f$false$bool  ? \f$false$true  : \f$false$false  ) ;
  wire[0:0] \f  = ( \f$bool  ? \f$true  : \f$false  ) ;

  assign \o0  = \f  ;
endmodule

module \OFUN_1$Agent_Switch1 (
      input \clk , input \rst
    , input [0:0] \i0$data
    , output [0:0] \o0
  );

  //
  // Function logic
  //
  wire \f  = `TOKEN ;

  assign \o0  = \f  ;
endmodule

module \OFUN_2$Agent_Switch1 (
      input \clk , input \rst
    , input [0:0] \i0$data
    , output [0:0] \o0
  );

  //
  // Function logic
  //
  wire \f  = `TOKEN ;

  assign \o0  = \f  ;
endmodule

module \OFUN_0$Agent_Merge1 (
      input \clk , input \rst
    , input [0:0] \i0$data
    , input [0:0] \i1$data
    , input \sel
    , output [0:0] \o0
  );

  //
  // Function logic
  //
  wire[0:0] \f$bool$arg0$disj  = \sel  ;
  wire[0:0] \f$bool$arg0  = \f$bool$arg0$disj [0:0] ;
  wire[0:0] \f$bool$arg1  = 1'd0 ;
  wire \f$bool  = \f$bool$arg0  == \f$bool$arg1  ;
  wire \f$true  = `TOKEN ;
  wire[0:0] \f$false$bool$arg0$disj  = \sel  ;
  wire[0:0] \f$false$bool$arg0  = \f$false$bool$arg0$disj [0:0] ;
  wire[0:0] \f$false$bool$arg1  = 1'd1 ;
  wire \f$false$bool  = \f$false$bool$arg0  == \f$false$bool$arg1  ;
  wire \f$false$true  = `TOKEN ;
  wire \f$false$false  = `TOKEN ;
  wire[0:0] \f$false$true'  = 1'd1 ;
  wire[0:0] \f$false$false'  = 1'd0 ;
  wire[0:0] \f$false  = ( \f$false$bool  ? \f$false$true'  : \f$false$false'  ) ;
  wire[0:0] \f$true'  = 1'd0 ;
  wire[0:0] \f  = ( \f$bool  ? \f$true'  : \f$false  ) ;

  assign \o0  = \f  ;
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
  wire \fabric_o5_agentQ_i2$irdy  ;
  wire \fabric_o5_agentQ_i2$data  ;
  wire \fabric_o5_agentQ_i2$trdy  ;
  wire \fabric_o4_agentQ_i1$irdy  ;
  wire \fabric_o4_agentQ_i1$data  ;
  wire \fabric_o4_agentQ_i1$trdy  ;
  wire \fabric_o3_agentP_i0$irdy  ;
  wire \fabric_o3_agentP_i0$data  ;
  wire \fabric_o3_agentP_i0$trdy  ;
  wire \fabric_o2_agentP_i2$irdy  ;
  wire \fabric_o2_agentP_i2$data  ;
  wire \fabric_o2_agentP_i2$trdy  ;
  wire \fabric_o1_agentP_i1$irdy  ;
  wire \fabric_o1_agentP_i1$data  ;
  wire \fabric_o1_agentP_i1$trdy  ;
  wire \fabric_o0_agentQ_i0$irdy  ;
  wire \fabric_o0_agentQ_i0$data  ;
  wire \fabric_o0_agentQ_i0$trdy  ;
  wire \agentQ_o2_fabric_i2$irdy  ;
  wire \agentQ_o2_fabric_i2$data  ;
  wire \agentQ_o2_fabric_i2$trdy  ;
  wire \agentQ_o1_fabric_i1$irdy  ;
  wire \agentQ_o1_fabric_i1$data  ;
  wire \agentQ_o1_fabric_i1$trdy  ;
  wire \agentQ_o0_fabric_i3$irdy  ;
  wire \agentQ_o0_fabric_i3$data  ;
  wire \agentQ_o0_fabric_i3$trdy  ;
  wire \agentP_o2_fabric_i5$irdy  ;
  wire \agentP_o2_fabric_i5$data  ;
  wire \agentP_o2_fabric_i5$trdy  ;
  wire \agentP_o1_fabric_i4$irdy  ;
  wire \agentP_o1_fabric_i4$data  ;
  wire \agentP_o1_fabric_i4$trdy  ;
  wire \agentP_o0_fabric_i0$irdy  ;
  wire \agentP_o0_fabric_i0$data  ;
  wire \agentP_o0_fabric_i0$trdy  ;

  //
  // Component and Macro instantiations
  //
  \Agent  \Agent1  (
      .\clk (\clk ), .\rst (\rst ), .\t (\t )
    , .\i0$irdy (\fabric_o3_agentP_i0$irdy )
    , .\i0$data (\fabric_o3_agentP_i0$data )
    , .\i0$trdy (\fabric_o3_agentP_i0$trdy )
    , .\i1$irdy (\fabric_o1_agentP_i1$irdy )
    , .\i1$data (\fabric_o1_agentP_i1$data )
    , .\i1$trdy (\fabric_o1_agentP_i1$trdy )
    , .\i2$irdy (\fabric_o2_agentP_i2$irdy )
    , .\i2$data (\fabric_o2_agentP_i2$data )
    , .\i2$trdy (\fabric_o2_agentP_i2$trdy )
    , .\o0$irdy (\agentP_o0_fabric_i0$irdy )
    , .\o0$data (\agentP_o0_fabric_i0$data )
    , .\o0$trdy (\agentP_o0_fabric_i0$trdy )
    , .\o1$irdy (\agentP_o1_fabric_i4$irdy )
    , .\o1$data (\agentP_o1_fabric_i4$data )
    , .\o1$trdy (\agentP_o1_fabric_i4$trdy )
    , .\o2$irdy (\agentP_o2_fabric_i5$irdy )
    , .\o2$data (\agentP_o2_fabric_i5$data )
    , .\o2$trdy (\agentP_o2_fabric_i5$trdy )
  );

  \Agent  \Agent2  (
      .\clk (\clk ), .\rst (\rst ), .\t (\t )
    , .\i0$irdy (\fabric_o0_agentQ_i0$irdy )
    , .\i0$data (\fabric_o0_agentQ_i0$data )
    , .\i0$trdy (\fabric_o0_agentQ_i0$trdy )
    , .\i1$irdy (\fabric_o4_agentQ_i1$irdy )
    , .\i1$data (\fabric_o4_agentQ_i1$data )
    , .\i1$trdy (\fabric_o4_agentQ_i1$trdy )
    , .\i2$irdy (\fabric_o5_agentQ_i2$irdy )
    , .\i2$data (\fabric_o5_agentQ_i2$data )
    , .\i2$trdy (\fabric_o5_agentQ_i2$trdy )
    , .\o0$irdy (\agentQ_o0_fabric_i3$irdy )
    , .\o0$data (\agentQ_o0_fabric_i3$data )
    , .\o0$trdy (\agentQ_o0_fabric_i3$trdy )
    , .\o1$irdy (\agentQ_o1_fabric_i1$irdy )
    , .\o1$data (\agentQ_o1_fabric_i1$data )
    , .\o1$trdy (\agentQ_o1_fabric_i1$trdy )
    , .\o2$irdy (\agentQ_o2_fabric_i2$irdy )
    , .\o2$data (\agentQ_o2_fabric_i2$data )
    , .\o2$trdy (\agentQ_o2_fabric_i2$trdy )
  );

  \Fabric  \Fabric1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\agentP_o0_fabric_i0$irdy )
    , .\i0$data (\agentP_o0_fabric_i0$data )
    , .\i0$trdy (\agentP_o0_fabric_i0$trdy )
    , .\i1$irdy (\agentQ_o1_fabric_i1$irdy )
    , .\i1$data (\agentQ_o1_fabric_i1$data )
    , .\i1$trdy (\agentQ_o1_fabric_i1$trdy )
    , .\i2$irdy (\agentQ_o2_fabric_i2$irdy )
    , .\i2$data (\agentQ_o2_fabric_i2$data )
    , .\i2$trdy (\agentQ_o2_fabric_i2$trdy )
    , .\i3$irdy (\agentQ_o0_fabric_i3$irdy )
    , .\i3$data (\agentQ_o0_fabric_i3$data )
    , .\i3$trdy (\agentQ_o0_fabric_i3$trdy )
    , .\i4$irdy (\agentP_o1_fabric_i4$irdy )
    , .\i4$data (\agentP_o1_fabric_i4$data )
    , .\i4$trdy (\agentP_o1_fabric_i4$trdy )
    , .\i5$irdy (\agentP_o2_fabric_i5$irdy )
    , .\i5$data (\agentP_o2_fabric_i5$data )
    , .\i5$trdy (\agentP_o2_fabric_i5$trdy )
    , .\o0$irdy (\fabric_o0_agentQ_i0$irdy )
    , .\o0$data (\fabric_o0_agentQ_i0$data )
    , .\o0$trdy (\fabric_o0_agentQ_i0$trdy )
    , .\o1$irdy (\fabric_o1_agentP_i1$irdy )
    , .\o1$data (\fabric_o1_agentP_i1$data )
    , .\o1$trdy (\fabric_o1_agentP_i1$trdy )
    , .\o2$irdy (\fabric_o2_agentP_i2$irdy )
    , .\o2$data (\fabric_o2_agentP_i2$data )
    , .\o2$trdy (\fabric_o2_agentP_i2$trdy )
    , .\o3$irdy (\fabric_o3_agentP_i0$irdy )
    , .\o3$data (\fabric_o3_agentP_i0$data )
    , .\o3$trdy (\fabric_o3_agentP_i0$trdy )
    , .\o4$irdy (\fabric_o4_agentQ_i1$irdy )
    , .\o4$data (\fabric_o4_agentQ_i1$data )
    , .\o4$trdy (\fabric_o4_agentQ_i1$trdy )
    , .\o5$irdy (\fabric_o5_agentQ_i2$irdy )
    , .\o5$data (\fabric_o5_agentQ_i2$data )
    , .\o5$trdy (\fabric_o5_agentQ_i2$trdy )
  );

endmodule

// Assertions
// Macro for assertion on the positive edge of the clock
`define assert_clk_pos(arg) \
  assert property (@(posedge clk) disable iff (rst) arg)

virtual class Q #(parameter DATASIZE=0, parameter LENGTH=0);
  localparam s = LENGTH < 2 ? 0 : $clog2(LENGTH) - 1;
  localparam t = (LENGTH + 1) < 2 ? 0 : $clog2(LENGTH + 1) - 1;
  localparam l = DATASIZE < 1 ? 0 : DATASIZE - 1;

  static function [t:0] nr_of_packets (logic full, logic[s:0] in, logic[s:0] out);
    return full ? LENGTH : in - out + (in < out ? LENGTH : 0);
  endfunction

  static function[t:0] nr_of_packets_data (logic[l:0] data, logic[l:0] data$addr [0:(LENGTH-1)], logic full, logic[s:0] in, logic[s:0] out);
    integer count;
    count = 0;
    for (integer i = 0; i < LENGTH; i = i + 1) begin
      count = count + matches_data(i, data, data$addr, full, in, out);
    end
    return count;
  endfunction

  static function matches_data (int position, logic[l:0] data, logic[l:0] data$addr [0:(LENGTH-1)], logic full, logic[s:0] in, logic[s:0] out);
    bit match;
    match = has_data(position, full, in, out);
    for (integer j = 0; j <= l; j = j + 1) begin
      match = match && (data[j] === 1'bX || data$addr[position][j] == data[j]);
    end
    return match;
  endfunction

  static function has_data(int position, logic full, logic[s:0] in, logic[s:0] out);
    return (full || out <= position && position < in) ||
    (in < out && (out <= position || position < in));
  endfunction
endclass

module \pLib_top (
      input \clk , input \rst
  );

  Test:
    `assert_clk_pos(0 == Q#(1,2)::nr_of_packets_data(1'b0, Fabric1.Queue1.data$addr, Fabric1.Queue1.full, Fabric1.Queue1.in, Fabric1.Queue1.out));
  //
  // Invariant assertions
  //
//   Invariant_0:
//    `assert_clk_pos(0 == (-1) * top.\Fabric1 .\Queue1 .nr_of_packets_data(1'b0) + (-1) * top.\Fabric1 .\Queue2 .nr_of_packets() + (-1) * top.\Agent2 .\Queue3 .nr_of_packets() + (1) * top.\Agent2 .\credit_counter_101 .\Queue1 .nr_of_packets() + (-1) * top.\Agent1 .\Queue1 .nr_of_packets() );
//  Invariant_1:
//    `assert_clk_pos(0 == (-1) * \Fabric1 .\Queue1 .nr_of_packets_data(1'b1) + (-1) * \Fabric1 .\Queue3 .nr_of_packets() + (-1) * \Agent2 .\Queue4 .nr_of_packets() + (1) * \Agent2 .\credit_counter_102 .\Queue1 .nr_of_packets() + (-1) * \Agent1 .\Queue2 .nr_of_packets() );
//  Invariant_2:
//    `assert_clk_pos(0 == (1) * \Fabric1 .\Queue4 .nr_of_packets_data(1'b1) + (1) * \Fabric1 .\Queue6 .nr_of_packets() + (1) * \Agent2 .\Queue2 .nr_of_packets() + (1) * \Agent1 .\Queue4 .nr_of_packets() + (-1) * \Agent1 .\credit_counter_102 .\Queue1 .nr_of_packets() );
//  Invariant_3:
//    `assert_clk_pos(0 == (-1) * \Fabric1 .\Queue4 .nr_of_packets_data(1'b0) + (-1) * \Fabric1 .\Queue5 .nr_of_packets() + (-1) * \Agent2 .\Queue1 .nr_of_packets() + (-1) * \Agent1 .\Queue3 .nr_of_packets() + (1) * \Agent1 .\credit_counter_101 .\Queue1 .nr_of_packets() );
endmodule


//
// Wrapper module
//
  bind \top  \pLib_top  \top_assertions  (
      .\clk (\clk ), .\rst (\rst )
  );

