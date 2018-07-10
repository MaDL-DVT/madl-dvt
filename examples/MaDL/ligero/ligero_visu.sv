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

module \arbiter3 (
      input \clk , input \rst 
    , input \client0 
    , input \client1 
    , input \client2 
    , input \transfer 
    , output [1:0] \sel 
  );
  wire[0:0] \sel2  ;
  \arbiter2  \arb  (
      .\clk (\clk ), .\rst (\rst )
    , .\client0 (\client0 )
    , .\client1 (\client1 )
    , .\transfer (\transfer )
    , .\sel (\sel2 )
  );
  
  reg [1:0] prevSel;
  reg transferReg;
  
  always @(posedge clk) prevSel <= rst ? 1'b 0 : sel;
  always @(posedge clk) transferReg <= rst ? 1'b 0 : transfer;
  assign \sel  = ( rst ? 1'b 0 : ( ((!client0) && (!client1)) ? 2'd2 : ( (!client2) ? sel2 : ( transferReg ? ( (prevSel == 2'd2) ? sel2 : 2'd2 ) : prevSel ) ) ) ) ;
endmodule

module \arbiter4 (
      input \clk , input \rst 
    , input \client0 
    , input \client1 
    , input \client2 
    , input \client3 
    , input \transfer 
    , output [1:0] \sel 
  );
  wire[1:0] \sel2  ;
  \arbiter3  \arb  (
      .\clk (\clk ), .\rst (\rst )
    , .\client0 (\client0 )
    , .\client1 (\client1 )
    , .\client2 (\client2 )
    , .\transfer (\transfer )
    , .\sel (\sel2 )
  );
  
  reg [1:0] prevSel;
  reg transferReg;
  
  always @(posedge clk) prevSel <= rst ? 1'b 0 : sel;
  always @(posedge clk) transferReg <= rst ? 1'b 0 : transfer;
  assign \sel  = ( rst ? 1'b 0 : ( ((!client0) && (!client1) && (!client2)) ? 2'd3 : ( (!client3) ? sel2 : ( transferReg ? ( (prevSel == 2'd3) ? sel2 : 2'd3 ) : prevSel ) ) ) ) ;
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

module \LoadBalancer2 #(
    DATASIZE = 1
  ) (
      input \clk , input \rst 
    , input \i0$irdy , input [DATASIZE-1:0] \i0$data , output \i0$trdy 
    , output \o0$irdy , output [DATASIZE-1:0] \o0$data , input \o0$trdy 
    , output \o1$irdy , output [DATASIZE-1:0] \o1$data , input \o1$trdy 
  );
  wire[0:0] \sel  ;
  \arbiter2  \arb  (
      .\clk (\clk ), .\rst (\rst )
    , .\client0 (\o0$trdy )
    , .\client1 (\o1$trdy )
    , .\transfer ((\i0$irdy  && \i0$trdy ))
    , .\sel (\sel )
  );
  
  assign \i0$trdy  = (((\sel  == 1'd0) && \o0$trdy ) || ((\sel  == 1'd1) && \o1$trdy )) ;
  assign \o0$irdy  = (((\sel  == 1'd0) && \o0$trdy ) && \i0$irdy ) ;
  assign \o1$irdy  = (((\sel  == 1'd1) && \o1$trdy ) && \i0$irdy ) ;
  assign \o0$data  = \i0$data  ;
  assign \o1$data  = \i0$data  ;
endmodule

module \LoadBalancer4 #(
    DATASIZE = 1
  ) (
      input \clk , input \rst 
    , input \i0$irdy , input [DATASIZE-1:0] \i0$data , output \i0$trdy 
    , output \o0$irdy , output [DATASIZE-1:0] \o0$data , input \o0$trdy 
    , output \o1$irdy , output [DATASIZE-1:0] \o1$data , input \o1$trdy 
    , output \o2$irdy , output [DATASIZE-1:0] \o2$data , input \o2$trdy 
    , output \o3$irdy , output [DATASIZE-1:0] \o3$data , input \o3$trdy 
  );
  wire[1:0] \sel  ;
  \arbiter4  \arb  (
      .\clk (\clk ), .\rst (\rst )
    , .\client0 (\o0$trdy )
    , .\client1 (\o1$trdy )
    , .\client2 (\o2$trdy )
    , .\client3 (\o3$trdy )
    , .\transfer ((\i0$irdy  && \i0$trdy ))
    , .\sel (\sel )
  );
  
  assign \i0$trdy  = (((\sel  == 2'd0) && \o0$trdy ) || ((\sel  == 2'd1) && \o1$trdy ) || ((\sel  == 2'd2) && \o2$trdy ) || ((\sel  == 2'd3) && \o3$trdy )) ;
  assign \o0$irdy  = (((\sel  == 2'd0) && \o0$trdy ) && \i0$irdy ) ;
  assign \o1$irdy  = (((\sel  == 2'd1) && \o1$trdy ) && \i0$irdy ) ;
  assign \o2$irdy  = (((\sel  == 2'd2) && \o2$trdy ) && \i0$irdy ) ;
  assign \o3$irdy  = (((\sel  == 2'd3) && \o3$trdy ) && \i0$irdy ) ;
  assign \o0$data  = \i0$data  ;
  assign \o1$data  = \i0$data  ;
  assign \o2$data  = \i0$data  ;
  assign \o3$data  = \i0$data  ;
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
    NUM_DATA = 0,
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
    DATASIZE = 1
  ) (
      input \clk , input \rst , input [63:0] \t 
    , input \i0$irdy , input [DATASIZE-1:0] \i0$data , output \i0$trdy 
    , input \unbound_trdy 
  );
  assume property (##[0:$] \unbound_trdy  == 1);
  
  reg \trdy ;
  
  always @(posedge clk) begin
    \trdy  <= ( ((!\i0$irdy ) & \trdy ) ? \trdy  : \unbound_trdy  ) ;
  end
  
  assign \i0$trdy  = \trdy  ;
endmodule

module \Source #(
    DATASIZE = 1
  ) (
      input \clk , input \rst , input [63:0] \t 
    , output \o0$irdy , output [DATASIZE-1:0] \o0$data , input \o0$trdy 
    , input \unbound_irdy 
    , input [DATASIZE-1:0] \unbound_data 
  );
  assume property (##[0:$] \unbound_irdy  == 1);
  
  reg \irdy ;
  reg [DATASIZE-1:0] \data ;
  
  always @(posedge clk) begin
    \irdy  <= ( ((!\o0$trdy ) & irdy) ? \irdy  : \unbound_irdy  ) ;
    \data  <= ( ((!\o0$trdy ) & irdy) ? \data  : \unbound_data  ) ;
  end
  
  assign \o0$irdy  = \irdy  ;
  assign \o0$data  = \data  ;
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
// Top Level Definitions
//
// Constant value to use for data of size 0, since wire size 0 is not possible in verilog
`define TOKEN 0

//
// Macro modules
//
module \CreditCounter_2 (
      input \clk , input \rst , input [63:0] \t 
    , input \i$irdy , input [1:0] \i$data , output \i$trdy 
    , output \o$irdy , output [0:0] \o$data , input \o$trdy 
    , input \PatientSource1$unbound_irdy 
    , input [0:0] \PatientSource1$unbound_data 
    , output \PatientSource1$trdy 
    , input \Sink1$unbound_trdy 
    , output \Sink1$irdy 
    , output [0:0] \Sink1$data 
  );
  
  //
  // Channel declarations
  //
  wire \q_in$irdy  ;
  wire \q_in$data  ;
  wire \q_in$trdy  ;
  wire \channel1$irdy  ;
  wire \channel1$data  ;
  wire \channel1$trdy  ;
  wire \channel3$irdy  ;
  wire \channel3$data  ;
  wire \channel3$trdy  ;
  wire \channel2$irdy  ;
  wire \channel2$data  ;
  wire \channel2$trdy  ;
  
  //
  // Component and Macro instantiations
  //
  \Fork2  #(
    .DATASIZE(1)
  ) \Fork1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\channel1$irdy )
    , .\i0$data (\channel1$data )
    , .\i0$trdy (\channel1$trdy )
    , .\o0$irdy (\q_in$irdy )
    , .\o0$data (\q_in$data )
    , .\o0$trdy (\q_in$trdy )
    , .\o1$irdy (\o$irdy )
    , .\o1$data (\o$data )
    , .\o1$trdy (\o$trdy )
  );
  
  assign \PatientSource1$trdy  = \channel1$trdy  ;
  \Source  #(
    .DATASIZE(1)
  ) \PatientSource1  (
      .\clk (\clk ), .\rst (\rst ), .\t (\t )
    , .\o0$irdy (\channel1$irdy )
    , .\o0$data (\channel1$data )
    , .\o0$trdy (\channel1$trdy )
    , .\unbound_irdy (\PatientSource1$unbound_irdy )
    , .\unbound_data (\PatientSource1$unbound_data )
  );
  
  assign \Sink1$irdy  = \channel3$irdy  ;
  assign \Sink1$data  = \channel3$data  ;
  \Sink  #(
    .DATASIZE(1)
  ) \Sink1  (
      .\clk (\clk ), .\rst (\rst ), .\t (\t )
    , .\i0$irdy (\channel3$irdy )
    , .\i0$data (\channel3$data )
    , .\i0$trdy (\channel3$trdy )
    , .\unbound_trdy (\Sink1$unbound_trdy )
  );
  
  \CTRLJoin2  #(
    .INPUTSIZE1(2),
    .OUTPUTSIZE(1),
    .INPUTSIZE0(1)
  ) \CtrlJoin1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\channel2$irdy )
    , .\i0$data (\channel2$data )
    , .\i0$trdy (\channel2$trdy )
    , .\i1$irdy (\i$irdy )
    , .\i1$data (\i$data )
    , .\i1$trdy (\i$trdy )
    , .\o0$irdy (\channel3$irdy )
    , .\o0$data (\channel3$data )
    , .\o0$trdy (\channel3$trdy )
  );
  
  \Queue  #(
    .NUM_DATA(0),
    .DATASIZE(1),
    .LENGTH(2)
  ) \Queue1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\q_in$irdy )
    , .\i0$data (\q_in$data )
    , .\i0$trdy (\q_in$trdy )
    , .\o0$irdy (\channel2$irdy )
    , .\o0$data (\channel2$data )
    , .\o0$trdy (\channel2$trdy )
  );
  
endmodule

module \Latch$type0 (
      input \clk , input \rst 
    , input \input$irdy , input [1:0] \input$data , output \input$trdy 
    , output \output$irdy , output [1:0] \output$data , input \output$trdy 
  );
  
  //
  // Component and Macro instantiations
  //
  \Queue  #(
    .NUM_DATA(0),
    .DATASIZE(2),
    .LENGTH(1)
  ) \Queue1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\input$irdy )
    , .\i0$data (\input$data )
    , .\i0$trdy (\input$trdy )
    , .\o0$irdy (\output$irdy )
    , .\o0$data (\output$data )
    , .\o0$trdy (\output$trdy )
  );
  
endmodule

module \Latch$type1 (
      input \clk , input \rst 
    , input \input$irdy , input [1:0] \input$data , output \input$trdy 
    , output \output$irdy , output [1:0] \output$data , input \output$trdy 
  );
  
  //
  // Component and Macro instantiations
  //
  \Queue  #(
    .NUM_DATA(0),
    .DATASIZE(2),
    .LENGTH(1)
  ) \Queue1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\input$irdy )
    , .\i0$data (\input$data )
    , .\i0$trdy (\input$trdy )
    , .\o0$irdy (\output$irdy )
    , .\o0$data (\output$data )
    , .\o0$trdy (\output$trdy )
  );
  
endmodule

module \Latch$type2 (
      input \clk , input \rst 
    , input \input$irdy , input [1:0] \input$data , output \input$trdy 
    , output \output$irdy , output [1:0] \output$data , input \output$trdy 
  );
  
  //
  // Component and Macro instantiations
  //
  \Queue  #(
    .NUM_DATA(0),
    .DATASIZE(2),
    .LENGTH(1)
  ) \Queue1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\input$irdy )
    , .\i0$data (\input$data )
    , .\i0$trdy (\input$trdy )
    , .\o0$irdy (\output$irdy )
    , .\o0$data (\output$data )
    , .\o0$trdy (\output$trdy )
  );
  
endmodule

module \Latch$type3 (
      input \clk , input \rst 
    , input \input$irdy , input [1:0] \input$data , output \input$trdy 
    , output \output$irdy , output [1:0] \output$data , input \output$trdy 
  );
  
  //
  // Component and Macro instantiations
  //
  \Queue  #(
    .NUM_DATA(0),
    .DATASIZE(2),
    .LENGTH(1)
  ) \Queue1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\input$irdy )
    , .\i0$data (\input$data )
    , .\i0$trdy (\input$trdy )
    , .\o0$irdy (\output$irdy )
    , .\o0$data (\output$data )
    , .\o0$trdy (\output$trdy )
  );
  
endmodule

module \Latch$type4 (
      input \clk , input \rst 
    , input \input$irdy , input [1:0] \input$data , output \input$trdy 
    , output \output$irdy , output [1:0] \output$data , input \output$trdy 
  );
  
  //
  // Component and Macro instantiations
  //
  \Queue  #(
    .NUM_DATA(0),
    .DATASIZE(2),
    .LENGTH(1)
  ) \Queue1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\input$irdy )
    , .\i0$data (\input$data )
    , .\i0$trdy (\input$trdy )
    , .\o0$irdy (\output$irdy )
    , .\o0$data (\output$data )
    , .\o0$trdy (\output$trdy )
  );
  
endmodule

module \Latch$type5 (
      input \clk , input \rst 
    , input \input$irdy , input [1:0] \input$data , output \input$trdy 
    , output \output$irdy , output [1:0] \output$data , input \output$trdy 
  );
  
  //
  // Component and Macro instantiations
  //
  \Queue  #(
    .NUM_DATA(0),
    .DATASIZE(2),
    .LENGTH(1)
  ) \Queue1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\input$irdy )
    , .\i0$data (\input$data )
    , .\i0$trdy (\input$trdy )
    , .\o0$irdy (\output$irdy )
    , .\o0$data (\output$data )
    , .\o0$trdy (\output$trdy )
  );
  
endmodule

module \Latch$type6 (
      input \clk , input \rst 
    , input \input$irdy , input [1:0] \input$data , output \input$trdy 
    , output \output$irdy , output [1:0] \output$data , input \output$trdy 
  );
  
  //
  // Component and Macro instantiations
  //
  \Queue  #(
    .NUM_DATA(0),
    .DATASIZE(2),
    .LENGTH(1)
  ) \Queue1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\input$irdy )
    , .\i0$data (\input$data )
    , .\i0$trdy (\input$trdy )
    , .\o0$irdy (\output$irdy )
    , .\o0$data (\output$data )
    , .\o0$trdy (\output$trdy )
  );
  
endmodule

module \Latch$type7 (
      input \clk , input \rst 
    , input \input$irdy , input [1:0] \input$data , output \input$trdy 
    , output \output$irdy , output [1:0] \output$data , input \output$trdy 
  );
  
  //
  // Component and Macro instantiations
  //
  \Queue  #(
    .NUM_DATA(0),
    .DATASIZE(2),
    .LENGTH(1)
  ) \Queue1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\input$irdy )
    , .\i0$data (\input$data )
    , .\i0$trdy (\input$trdy )
    , .\o0$irdy (\output$irdy )
    , .\o0$data (\output$data )
    , .\o0$trdy (\output$trdy )
  );
  
endmodule

module \Latch$type8 (
      input \clk , input \rst 
    , input \input$irdy , input [1:0] \input$data , output \input$trdy 
    , output \output$irdy , output [1:0] \output$data , input \output$trdy 
  );
  
  //
  // Component and Macro instantiations
  //
  \Queue  #(
    .NUM_DATA(0),
    .DATASIZE(2),
    .LENGTH(1)
  ) \Queue1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\input$irdy )
    , .\i0$data (\input$data )
    , .\i0$trdy (\input$trdy )
    , .\o0$irdy (\output$irdy )
    , .\o0$data (\output$data )
    , .\o0$trdy (\output$trdy )
  );
  
endmodule

module \Merge3$type0 (
      input \clk , input \rst 
    , input \bus_ins1$irdy , input [1:0] \bus_ins1$data , output \bus_ins1$trdy 
    , input \bus_ins2$irdy , input [1:0] \bus_ins2$data , output \bus_ins2$trdy 
    , input \bus_ins3$irdy , input [1:0] \bus_ins3$data , output \bus_ins3$trdy 
    , output \output$irdy , output [1:0] \output$data , input \output$trdy 
  );
  
  //
  // Channel declarations
  //
  wire \channel1$irdy  ;
  wire [1:0] \channel1$data  ;
  wire \channel1$trdy  ;
  
  //
  // Function Channels
  //
  wire [1:0] \ofunchan_0_Merge1$data  ;
  wire \sel_Merge1  ;
  wire [1:0] \ofunchan_0_Merge2$data  ;
  wire \sel_Merge2  ;
  
  //
  // Component and Macro instantiations
  //
  \Merge2  #(
    .INPUTSIZE1(2),
    .OUTPUTSIZE(2),
    .INPUTSIZE0(2)
  ) \Merge1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\bus_ins1$irdy )
    , .\i0$data (\bus_ins1$data )
    , .\i0$trdy (\bus_ins1$trdy )
    , .\i1$irdy (\channel1$irdy )
    , .\i1$data (\channel1$data )
    , .\i1$trdy (\channel1$trdy )
    , .\o0$irdy (\output$irdy )
    , .\o0$data (\output$data )
    , .\o0$trdy (\output$trdy )
    , .\f$data (\ofunchan_0_Merge1$data )
    , .\sel (\sel_Merge1 )
  );
  
  \OFUN_0$Merge3_Merge1  \ofun_0_Merge1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\bus_ins1$data )
    , .\i1$data (\channel1$data )
    , .\sel (\sel_Merge1 )
    , .\o0 (\ofunchan_0_Merge1$data )
  );
  
  \Merge2  #(
    .INPUTSIZE1(2),
    .OUTPUTSIZE(2),
    .INPUTSIZE0(2)
  ) \Merge2  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\bus_ins2$irdy )
    , .\i0$data (\bus_ins2$data )
    , .\i0$trdy (\bus_ins2$trdy )
    , .\i1$irdy (\bus_ins3$irdy )
    , .\i1$data (\bus_ins3$data )
    , .\i1$trdy (\bus_ins3$trdy )
    , .\o0$irdy (\channel1$irdy )
    , .\o0$data (\channel1$data )
    , .\o0$trdy (\channel1$trdy )
    , .\f$data (\ofunchan_0_Merge2$data )
    , .\sel (\sel_Merge2 )
  );
  
  \OFUN_0$Merge3_Merge2  \ofun_0_Merge2  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\bus_ins2$data )
    , .\i1$data (\bus_ins3$data )
    , .\sel (\sel_Merge2 )
    , .\o0 (\ofunchan_0_Merge2$data )
  );
  
endmodule


//
// Merge3 switch functions
//
module \OFUN_0$Merge3_Merge1 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , input [1:0] \i1$data 
    , input \sel 
    , output [1:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[0:0] \f$bool$arg0$disj  = \sel  ;
  wire[0:0] \f$bool$arg0  = \f$bool$arg0$disj [0:0] ;
  wire[0:0] \f$bool$arg1  = 1'd0 ;
  wire \f$bool  = \f$bool$arg0  == \f$bool$arg1  ;
  wire[1:0] \f$true  = \i0$data  ;
  wire[0:0] \f$false$bool$arg0$disj  = \sel  ;
  wire[0:0] \f$false$bool$arg0  = \f$false$bool$arg0$disj [0:0] ;
  wire[0:0] \f$false$bool$arg1  = 1'd1 ;
  wire \f$false$bool  = \f$false$bool$arg0  == \f$false$bool$arg1  ;
  wire[1:0] \f$false$true  = \i1$data  ;
  wire[1:0] \f$false$false  = \i0$data  ;
  wire[1:0] \f$false  = ( \f$false$bool  ? \f$false$true  : \f$false$false  ) ;
  wire[1:0] \f  = ( \f$bool  ? \f$true  : \f$false  ) ;
  
  assign \o0  = \f  ;
endmodule

module \OFUN_0$Merge3_Merge2 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , input [1:0] \i1$data 
    , input \sel 
    , output [1:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[0:0] \f$bool$arg0$disj  = \sel  ;
  wire[0:0] \f$bool$arg0  = \f$bool$arg0$disj [0:0] ;
  wire[0:0] \f$bool$arg1  = 1'd0 ;
  wire \f$bool  = \f$bool$arg0  == \f$bool$arg1  ;
  wire[1:0] \f$true  = \i0$data  ;
  wire[0:0] \f$false$bool$arg0$disj  = \sel  ;
  wire[0:0] \f$false$bool$arg0  = \f$false$bool$arg0$disj [0:0] ;
  wire[0:0] \f$false$bool$arg1  = 1'd1 ;
  wire \f$false$bool  = \f$false$bool$arg0  == \f$false$bool$arg1  ;
  wire[1:0] \f$false$true  = \i1$data  ;
  wire[1:0] \f$false$false  = \i0$data  ;
  wire[1:0] \f$false  = ( \f$false$bool  ? \f$false$true  : \f$false$false  ) ;
  wire[1:0] \f  = ( \f$bool  ? \f$true  : \f$false  ) ;
  
  assign \o0  = \f  ;
endmodule

module \Merge3$type1 (
      input \clk , input \rst 
    , input \bus_ins1$irdy , input [1:0] \bus_ins1$data , output \bus_ins1$trdy 
    , input \bus_ins2$irdy , input [1:0] \bus_ins2$data , output \bus_ins2$trdy 
    , input \bus_ins3$irdy , input [1:0] \bus_ins3$data , output \bus_ins3$trdy 
    , output \output$irdy , output [1:0] \output$data , input \output$trdy 
  );
  
  //
  // Channel declarations
  //
  wire \channel1$irdy  ;
  wire [1:0] \channel1$data  ;
  wire \channel1$trdy  ;
  
  //
  // Function Channels
  //
  wire [1:0] \ofunchan_0_Merge1$data  ;
  wire \sel_Merge1  ;
  wire [1:0] \ofunchan_0_Merge2$data  ;
  wire \sel_Merge2  ;
  
  //
  // Component and Macro instantiations
  //
  \Merge2  #(
    .INPUTSIZE1(2),
    .OUTPUTSIZE(2),
    .INPUTSIZE0(2)
  ) \Merge1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\bus_ins1$irdy )
    , .\i0$data (\bus_ins1$data )
    , .\i0$trdy (\bus_ins1$trdy )
    , .\i1$irdy (\channel1$irdy )
    , .\i1$data (\channel1$data )
    , .\i1$trdy (\channel1$trdy )
    , .\o0$irdy (\output$irdy )
    , .\o0$data (\output$data )
    , .\o0$trdy (\output$trdy )
    , .\f$data (\ofunchan_0_Merge1$data )
    , .\sel (\sel_Merge1 )
  );
  
  \OFUN_0$Merge3_Merge1  \ofun_0_Merge1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\bus_ins1$data )
    , .\i1$data (\channel1$data )
    , .\sel (\sel_Merge1 )
    , .\o0 (\ofunchan_0_Merge1$data )
  );
  
  \Merge2  #(
    .INPUTSIZE1(2),
    .OUTPUTSIZE(2),
    .INPUTSIZE0(2)
  ) \Merge2  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\bus_ins2$irdy )
    , .\i0$data (\bus_ins2$data )
    , .\i0$trdy (\bus_ins2$trdy )
    , .\i1$irdy (\bus_ins3$irdy )
    , .\i1$data (\bus_ins3$data )
    , .\i1$trdy (\bus_ins3$trdy )
    , .\o0$irdy (\channel1$irdy )
    , .\o0$data (\channel1$data )
    , .\o0$trdy (\channel1$trdy )
    , .\f$data (\ofunchan_0_Merge2$data )
    , .\sel (\sel_Merge2 )
  );
  
  \OFUN_0$Merge3_Merge2  \ofun_0_Merge2  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\bus_ins2$data )
    , .\i1$data (\bus_ins3$data )
    , .\sel (\sel_Merge2 )
    , .\o0 (\ofunchan_0_Merge2$data )
  );
  
endmodule


//
// Merge3 switch functions
//
module \OFUN_0$Merge3_Merge1 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , input [1:0] \i1$data 
    , input \sel 
    , output [1:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[0:0] \f$bool$arg0$disj  = \sel  ;
  wire[0:0] \f$bool$arg0  = \f$bool$arg0$disj [0:0] ;
  wire[0:0] \f$bool$arg1  = 1'd0 ;
  wire \f$bool  = \f$bool$arg0  == \f$bool$arg1  ;
  wire[1:0] \f$true  = \i0$data  ;
  wire[0:0] \f$false$bool$arg0$disj  = \sel  ;
  wire[0:0] \f$false$bool$arg0  = \f$false$bool$arg0$disj [0:0] ;
  wire[0:0] \f$false$bool$arg1  = 1'd1 ;
  wire \f$false$bool  = \f$false$bool$arg0  == \f$false$bool$arg1  ;
  wire[1:0] \f$false$true  = \i1$data  ;
  wire[1:0] \f$false$false  = \i0$data  ;
  wire[1:0] \f$false  = ( \f$false$bool  ? \f$false$true  : \f$false$false  ) ;
  wire[1:0] \f  = ( \f$bool  ? \f$true  : \f$false  ) ;
  
  assign \o0  = \f  ;
endmodule

module \OFUN_0$Merge3_Merge2 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , input [1:0] \i1$data 
    , input \sel 
    , output [1:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[0:0] \f$bool$arg0$disj  = \sel  ;
  wire[0:0] \f$bool$arg0  = \f$bool$arg0$disj [0:0] ;
  wire[0:0] \f$bool$arg1  = 1'd0 ;
  wire \f$bool  = \f$bool$arg0  == \f$bool$arg1  ;
  wire[1:0] \f$true  = \i0$data  ;
  wire[0:0] \f$false$bool$arg0$disj  = \sel  ;
  wire[0:0] \f$false$bool$arg0  = \f$false$bool$arg0$disj [0:0] ;
  wire[0:0] \f$false$bool$arg1  = 1'd1 ;
  wire \f$false$bool  = \f$false$bool$arg0  == \f$false$bool$arg1  ;
  wire[1:0] \f$false$true  = \i1$data  ;
  wire[1:0] \f$false$false  = \i0$data  ;
  wire[1:0] \f$false  = ( \f$false$bool  ? \f$false$true  : \f$false$false  ) ;
  wire[1:0] \f  = ( \f$bool  ? \f$true  : \f$false  ) ;
  
  assign \o0  = \f  ;
endmodule

module \Merge3$type2 (
      input \clk , input \rst 
    , input \bus_ins1$irdy , input [1:0] \bus_ins1$data , output \bus_ins1$trdy 
    , input \bus_ins2$irdy , input [1:0] \bus_ins2$data , output \bus_ins2$trdy 
    , input \bus_ins3$irdy , input [1:0] \bus_ins3$data , output \bus_ins3$trdy 
    , output \output$irdy , output [1:0] \output$data , input \output$trdy 
  );
  
  //
  // Channel declarations
  //
  wire \channel1$irdy  ;
  wire [1:0] \channel1$data  ;
  wire \channel1$trdy  ;
  
  //
  // Function Channels
  //
  wire [1:0] \ofunchan_0_Merge1$data  ;
  wire \sel_Merge1  ;
  wire [1:0] \ofunchan_0_Merge2$data  ;
  wire \sel_Merge2  ;
  
  //
  // Component and Macro instantiations
  //
  \Merge2  #(
    .INPUTSIZE1(2),
    .OUTPUTSIZE(2),
    .INPUTSIZE0(2)
  ) \Merge1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\bus_ins1$irdy )
    , .\i0$data (\bus_ins1$data )
    , .\i0$trdy (\bus_ins1$trdy )
    , .\i1$irdy (\channel1$irdy )
    , .\i1$data (\channel1$data )
    , .\i1$trdy (\channel1$trdy )
    , .\o0$irdy (\output$irdy )
    , .\o0$data (\output$data )
    , .\o0$trdy (\output$trdy )
    , .\f$data (\ofunchan_0_Merge1$data )
    , .\sel (\sel_Merge1 )
  );
  
  \OFUN_0$Merge3_Merge1  \ofun_0_Merge1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\bus_ins1$data )
    , .\i1$data (\channel1$data )
    , .\sel (\sel_Merge1 )
    , .\o0 (\ofunchan_0_Merge1$data )
  );
  
  \Merge2  #(
    .INPUTSIZE1(2),
    .OUTPUTSIZE(2),
    .INPUTSIZE0(2)
  ) \Merge2  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\bus_ins2$irdy )
    , .\i0$data (\bus_ins2$data )
    , .\i0$trdy (\bus_ins2$trdy )
    , .\i1$irdy (\bus_ins3$irdy )
    , .\i1$data (\bus_ins3$data )
    , .\i1$trdy (\bus_ins3$trdy )
    , .\o0$irdy (\channel1$irdy )
    , .\o0$data (\channel1$data )
    , .\o0$trdy (\channel1$trdy )
    , .\f$data (\ofunchan_0_Merge2$data )
    , .\sel (\sel_Merge2 )
  );
  
  \OFUN_0$Merge3_Merge2  \ofun_0_Merge2  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\bus_ins2$data )
    , .\i1$data (\bus_ins3$data )
    , .\sel (\sel_Merge2 )
    , .\o0 (\ofunchan_0_Merge2$data )
  );
  
endmodule


//
// Merge3 switch functions
//
module \OFUN_0$Merge3_Merge1 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , input [1:0] \i1$data 
    , input \sel 
    , output [1:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[0:0] \f$bool$arg0$disj  = \sel  ;
  wire[0:0] \f$bool$arg0  = \f$bool$arg0$disj [0:0] ;
  wire[0:0] \f$bool$arg1  = 1'd0 ;
  wire \f$bool  = \f$bool$arg0  == \f$bool$arg1  ;
  wire[1:0] \f$true  = \i0$data  ;
  wire[0:0] \f$false$bool$arg0$disj  = \sel  ;
  wire[0:0] \f$false$bool$arg0  = \f$false$bool$arg0$disj [0:0] ;
  wire[0:0] \f$false$bool$arg1  = 1'd1 ;
  wire \f$false$bool  = \f$false$bool$arg0  == \f$false$bool$arg1  ;
  wire[1:0] \f$false$true  = \i1$data  ;
  wire[1:0] \f$false$false  = \i0$data  ;
  wire[1:0] \f$false  = ( \f$false$bool  ? \f$false$true  : \f$false$false  ) ;
  wire[1:0] \f  = ( \f$bool  ? \f$true  : \f$false  ) ;
  
  assign \o0  = \f  ;
endmodule

module \OFUN_0$Merge3_Merge2 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , input [1:0] \i1$data 
    , input \sel 
    , output [1:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[0:0] \f$bool$arg0$disj  = \sel  ;
  wire[0:0] \f$bool$arg0  = \f$bool$arg0$disj [0:0] ;
  wire[0:0] \f$bool$arg1  = 1'd0 ;
  wire \f$bool  = \f$bool$arg0  == \f$bool$arg1  ;
  wire[1:0] \f$true  = \i0$data  ;
  wire[0:0] \f$false$bool$arg0$disj  = \sel  ;
  wire[0:0] \f$false$bool$arg0  = \f$false$bool$arg0$disj [0:0] ;
  wire[0:0] \f$false$bool$arg1  = 1'd1 ;
  wire \f$false$bool  = \f$false$bool$arg0  == \f$false$bool$arg1  ;
  wire[1:0] \f$false$true  = \i1$data  ;
  wire[1:0] \f$false$false  = \i0$data  ;
  wire[1:0] \f$false  = ( \f$false$bool  ? \f$false$true  : \f$false$false  ) ;
  wire[1:0] \f  = ( \f$bool  ? \f$true  : \f$false  ) ;
  
  assign \o0  = \f  ;
endmodule

module \Merge3$type3 (
      input \clk , input \rst 
    , input \bus_ins1$irdy , input [1:0] \bus_ins1$data , output \bus_ins1$trdy 
    , input \bus_ins2$irdy , input [1:0] \bus_ins2$data , output \bus_ins2$trdy 
    , input \bus_ins3$irdy , input [1:0] \bus_ins3$data , output \bus_ins3$trdy 
    , output \output$irdy , output [1:0] \output$data , input \output$trdy 
  );
  
  //
  // Channel declarations
  //
  wire \channel1$irdy  ;
  wire [1:0] \channel1$data  ;
  wire \channel1$trdy  ;
  
  //
  // Function Channels
  //
  wire [1:0] \ofunchan_0_Merge1$data  ;
  wire \sel_Merge1  ;
  wire [1:0] \ofunchan_0_Merge2$data  ;
  wire \sel_Merge2  ;
  
  //
  // Component and Macro instantiations
  //
  \Merge2  #(
    .INPUTSIZE1(2),
    .OUTPUTSIZE(2),
    .INPUTSIZE0(2)
  ) \Merge1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\bus_ins1$irdy )
    , .\i0$data (\bus_ins1$data )
    , .\i0$trdy (\bus_ins1$trdy )
    , .\i1$irdy (\channel1$irdy )
    , .\i1$data (\channel1$data )
    , .\i1$trdy (\channel1$trdy )
    , .\o0$irdy (\output$irdy )
    , .\o0$data (\output$data )
    , .\o0$trdy (\output$trdy )
    , .\f$data (\ofunchan_0_Merge1$data )
    , .\sel (\sel_Merge1 )
  );
  
  \OFUN_0$Merge3_Merge1  \ofun_0_Merge1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\bus_ins1$data )
    , .\i1$data (\channel1$data )
    , .\sel (\sel_Merge1 )
    , .\o0 (\ofunchan_0_Merge1$data )
  );
  
  \Merge2  #(
    .INPUTSIZE1(2),
    .OUTPUTSIZE(2),
    .INPUTSIZE0(2)
  ) \Merge2  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\bus_ins2$irdy )
    , .\i0$data (\bus_ins2$data )
    , .\i0$trdy (\bus_ins2$trdy )
    , .\i1$irdy (\bus_ins3$irdy )
    , .\i1$data (\bus_ins3$data )
    , .\i1$trdy (\bus_ins3$trdy )
    , .\o0$irdy (\channel1$irdy )
    , .\o0$data (\channel1$data )
    , .\o0$trdy (\channel1$trdy )
    , .\f$data (\ofunchan_0_Merge2$data )
    , .\sel (\sel_Merge2 )
  );
  
  \OFUN_0$Merge3_Merge2  \ofun_0_Merge2  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\bus_ins2$data )
    , .\i1$data (\bus_ins3$data )
    , .\sel (\sel_Merge2 )
    , .\o0 (\ofunchan_0_Merge2$data )
  );
  
endmodule


//
// Merge3 switch functions
//
module \OFUN_0$Merge3_Merge1 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , input [1:0] \i1$data 
    , input \sel 
    , output [1:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[0:0] \f$bool$arg0$disj  = \sel  ;
  wire[0:0] \f$bool$arg0  = \f$bool$arg0$disj [0:0] ;
  wire[0:0] \f$bool$arg1  = 1'd0 ;
  wire \f$bool  = \f$bool$arg0  == \f$bool$arg1  ;
  wire[1:0] \f$true  = \i0$data  ;
  wire[0:0] \f$false$bool$arg0$disj  = \sel  ;
  wire[0:0] \f$false$bool$arg0  = \f$false$bool$arg0$disj [0:0] ;
  wire[0:0] \f$false$bool$arg1  = 1'd1 ;
  wire \f$false$bool  = \f$false$bool$arg0  == \f$false$bool$arg1  ;
  wire[1:0] \f$false$true  = \i1$data  ;
  wire[1:0] \f$false$false  = \i0$data  ;
  wire[1:0] \f$false  = ( \f$false$bool  ? \f$false$true  : \f$false$false  ) ;
  wire[1:0] \f  = ( \f$bool  ? \f$true  : \f$false  ) ;
  
  assign \o0  = \f  ;
endmodule

module \OFUN_0$Merge3_Merge2 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , input [1:0] \i1$data 
    , input \sel 
    , output [1:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[0:0] \f$bool$arg0$disj  = \sel  ;
  wire[0:0] \f$bool$arg0  = \f$bool$arg0$disj [0:0] ;
  wire[0:0] \f$bool$arg1  = 1'd0 ;
  wire \f$bool  = \f$bool$arg0  == \f$bool$arg1  ;
  wire[1:0] \f$true  = \i0$data  ;
  wire[0:0] \f$false$bool$arg0$disj  = \sel  ;
  wire[0:0] \f$false$bool$arg0  = \f$false$bool$arg0$disj [0:0] ;
  wire[0:0] \f$false$bool$arg1  = 1'd1 ;
  wire \f$false$bool  = \f$false$bool$arg0  == \f$false$bool$arg1  ;
  wire[1:0] \f$false$true  = \i1$data  ;
  wire[1:0] \f$false$false  = \i0$data  ;
  wire[1:0] \f$false  = ( \f$false$bool  ? \f$false$true  : \f$false$false  ) ;
  wire[1:0] \f  = ( \f$bool  ? \f$true  : \f$false  ) ;
  
  assign \o0  = \f  ;
endmodule

module \Merge3$type4 (
      input \clk , input \rst 
    , input \bus_ins1$irdy , input [1:0] \bus_ins1$data , output \bus_ins1$trdy 
    , input \bus_ins2$irdy , input [1:0] \bus_ins2$data , output \bus_ins2$trdy 
    , input \bus_ins3$irdy , input [1:0] \bus_ins3$data , output \bus_ins3$trdy 
    , output \output$irdy , output [1:0] \output$data , input \output$trdy 
  );
  
  //
  // Channel declarations
  //
  wire \channel1$irdy  ;
  wire [1:0] \channel1$data  ;
  wire \channel1$trdy  ;
  
  //
  // Function Channels
  //
  wire [1:0] \ofunchan_0_Merge1$data  ;
  wire \sel_Merge1  ;
  wire [1:0] \ofunchan_0_Merge2$data  ;
  wire \sel_Merge2  ;
  
  //
  // Component and Macro instantiations
  //
  \Merge2  #(
    .INPUTSIZE1(2),
    .OUTPUTSIZE(2),
    .INPUTSIZE0(2)
  ) \Merge1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\bus_ins1$irdy )
    , .\i0$data (\bus_ins1$data )
    , .\i0$trdy (\bus_ins1$trdy )
    , .\i1$irdy (\channel1$irdy )
    , .\i1$data (\channel1$data )
    , .\i1$trdy (\channel1$trdy )
    , .\o0$irdy (\output$irdy )
    , .\o0$data (\output$data )
    , .\o0$trdy (\output$trdy )
    , .\f$data (\ofunchan_0_Merge1$data )
    , .\sel (\sel_Merge1 )
  );
  
  \OFUN_0$Merge3_Merge1  \ofun_0_Merge1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\bus_ins1$data )
    , .\i1$data (\channel1$data )
    , .\sel (\sel_Merge1 )
    , .\o0 (\ofunchan_0_Merge1$data )
  );
  
  \Merge2  #(
    .INPUTSIZE1(2),
    .OUTPUTSIZE(2),
    .INPUTSIZE0(2)
  ) \Merge2  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\bus_ins2$irdy )
    , .\i0$data (\bus_ins2$data )
    , .\i0$trdy (\bus_ins2$trdy )
    , .\i1$irdy (\bus_ins3$irdy )
    , .\i1$data (\bus_ins3$data )
    , .\i1$trdy (\bus_ins3$trdy )
    , .\o0$irdy (\channel1$irdy )
    , .\o0$data (\channel1$data )
    , .\o0$trdy (\channel1$trdy )
    , .\f$data (\ofunchan_0_Merge2$data )
    , .\sel (\sel_Merge2 )
  );
  
  \OFUN_0$Merge3_Merge2  \ofun_0_Merge2  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\bus_ins2$data )
    , .\i1$data (\bus_ins3$data )
    , .\sel (\sel_Merge2 )
    , .\o0 (\ofunchan_0_Merge2$data )
  );
  
endmodule


//
// Merge3 switch functions
//
module \OFUN_0$Merge3_Merge1 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , input [1:0] \i1$data 
    , input \sel 
    , output [1:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[0:0] \f$bool$arg0$disj  = \sel  ;
  wire[0:0] \f$bool$arg0  = \f$bool$arg0$disj [0:0] ;
  wire[0:0] \f$bool$arg1  = 1'd0 ;
  wire \f$bool  = \f$bool$arg0  == \f$bool$arg1  ;
  wire[1:0] \f$true  = \i0$data  ;
  wire[0:0] \f$false$bool$arg0$disj  = \sel  ;
  wire[0:0] \f$false$bool$arg0  = \f$false$bool$arg0$disj [0:0] ;
  wire[0:0] \f$false$bool$arg1  = 1'd1 ;
  wire \f$false$bool  = \f$false$bool$arg0  == \f$false$bool$arg1  ;
  wire[1:0] \f$false$true  = \i1$data  ;
  wire[1:0] \f$false$false  = \i0$data  ;
  wire[1:0] \f$false  = ( \f$false$bool  ? \f$false$true  : \f$false$false  ) ;
  wire[1:0] \f  = ( \f$bool  ? \f$true  : \f$false  ) ;
  
  assign \o0  = \f  ;
endmodule

module \OFUN_0$Merge3_Merge2 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , input [1:0] \i1$data 
    , input \sel 
    , output [1:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[0:0] \f$bool$arg0$disj  = \sel  ;
  wire[0:0] \f$bool$arg0  = \f$bool$arg0$disj [0:0] ;
  wire[0:0] \f$bool$arg1  = 1'd0 ;
  wire \f$bool  = \f$bool$arg0  == \f$bool$arg1  ;
  wire[1:0] \f$true  = \i0$data  ;
  wire[0:0] \f$false$bool$arg0$disj  = \sel  ;
  wire[0:0] \f$false$bool$arg0  = \f$false$bool$arg0$disj [0:0] ;
  wire[0:0] \f$false$bool$arg1  = 1'd1 ;
  wire \f$false$bool  = \f$false$bool$arg0  == \f$false$bool$arg1  ;
  wire[1:0] \f$false$true  = \i1$data  ;
  wire[1:0] \f$false$false  = \i0$data  ;
  wire[1:0] \f$false  = ( \f$false$bool  ? \f$false$true  : \f$false$false  ) ;
  wire[1:0] \f  = ( \f$bool  ? \f$true  : \f$false  ) ;
  
  assign \o0  = \f  ;
endmodule

module \Merge3$type5 (
      input \clk , input \rst 
    , input \bus_ins1$irdy , input [1:0] \bus_ins1$data , output \bus_ins1$trdy 
    , input \bus_ins2$irdy , input [1:0] \bus_ins2$data , output \bus_ins2$trdy 
    , input \bus_ins3$irdy , input [1:0] \bus_ins3$data , output \bus_ins3$trdy 
    , output \output$irdy , output [1:0] \output$data , input \output$trdy 
  );
  
  //
  // Channel declarations
  //
  wire \channel1$irdy  ;
  wire [1:0] \channel1$data  ;
  wire \channel1$trdy  ;
  
  //
  // Function Channels
  //
  wire [1:0] \ofunchan_0_Merge1$data  ;
  wire \sel_Merge1  ;
  wire [1:0] \ofunchan_0_Merge2$data  ;
  wire \sel_Merge2  ;
  
  //
  // Component and Macro instantiations
  //
  \Merge2  #(
    .INPUTSIZE1(2),
    .OUTPUTSIZE(2),
    .INPUTSIZE0(2)
  ) \Merge1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\bus_ins1$irdy )
    , .\i0$data (\bus_ins1$data )
    , .\i0$trdy (\bus_ins1$trdy )
    , .\i1$irdy (\channel1$irdy )
    , .\i1$data (\channel1$data )
    , .\i1$trdy (\channel1$trdy )
    , .\o0$irdy (\output$irdy )
    , .\o0$data (\output$data )
    , .\o0$trdy (\output$trdy )
    , .\f$data (\ofunchan_0_Merge1$data )
    , .\sel (\sel_Merge1 )
  );
  
  \OFUN_0$Merge3_Merge1  \ofun_0_Merge1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\bus_ins1$data )
    , .\i1$data (\channel1$data )
    , .\sel (\sel_Merge1 )
    , .\o0 (\ofunchan_0_Merge1$data )
  );
  
  \Merge2  #(
    .INPUTSIZE1(2),
    .OUTPUTSIZE(2),
    .INPUTSIZE0(2)
  ) \Merge2  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\bus_ins2$irdy )
    , .\i0$data (\bus_ins2$data )
    , .\i0$trdy (\bus_ins2$trdy )
    , .\i1$irdy (\bus_ins3$irdy )
    , .\i1$data (\bus_ins3$data )
    , .\i1$trdy (\bus_ins3$trdy )
    , .\o0$irdy (\channel1$irdy )
    , .\o0$data (\channel1$data )
    , .\o0$trdy (\channel1$trdy )
    , .\f$data (\ofunchan_0_Merge2$data )
    , .\sel (\sel_Merge2 )
  );
  
  \OFUN_0$Merge3_Merge2  \ofun_0_Merge2  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\bus_ins2$data )
    , .\i1$data (\bus_ins3$data )
    , .\sel (\sel_Merge2 )
    , .\o0 (\ofunchan_0_Merge2$data )
  );
  
endmodule


//
// Merge3 switch functions
//
module \OFUN_0$Merge3_Merge1 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , input [1:0] \i1$data 
    , input \sel 
    , output [1:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[0:0] \f$bool$arg0$disj  = \sel  ;
  wire[0:0] \f$bool$arg0  = \f$bool$arg0$disj [0:0] ;
  wire[0:0] \f$bool$arg1  = 1'd0 ;
  wire \f$bool  = \f$bool$arg0  == \f$bool$arg1  ;
  wire[1:0] \f$true  = \i0$data  ;
  wire[0:0] \f$false$bool$arg0$disj  = \sel  ;
  wire[0:0] \f$false$bool$arg0  = \f$false$bool$arg0$disj [0:0] ;
  wire[0:0] \f$false$bool$arg1  = 1'd1 ;
  wire \f$false$bool  = \f$false$bool$arg0  == \f$false$bool$arg1  ;
  wire[1:0] \f$false$true  = \i1$data  ;
  wire[1:0] \f$false$false  = \i0$data  ;
  wire[1:0] \f$false  = ( \f$false$bool  ? \f$false$true  : \f$false$false  ) ;
  wire[1:0] \f  = ( \f$bool  ? \f$true  : \f$false  ) ;
  
  assign \o0  = \f  ;
endmodule

module \OFUN_0$Merge3_Merge2 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , input [1:0] \i1$data 
    , input \sel 
    , output [1:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[0:0] \f$bool$arg0$disj  = \sel  ;
  wire[0:0] \f$bool$arg0  = \f$bool$arg0$disj [0:0] ;
  wire[0:0] \f$bool$arg1  = 1'd0 ;
  wire \f$bool  = \f$bool$arg0  == \f$bool$arg1  ;
  wire[1:0] \f$true  = \i0$data  ;
  wire[0:0] \f$false$bool$arg0$disj  = \sel  ;
  wire[0:0] \f$false$bool$arg0  = \f$false$bool$arg0$disj [0:0] ;
  wire[0:0] \f$false$bool$arg1  = 1'd1 ;
  wire \f$false$bool  = \f$false$bool$arg0  == \f$false$bool$arg1  ;
  wire[1:0] \f$false$true  = \i1$data  ;
  wire[1:0] \f$false$false  = \i0$data  ;
  wire[1:0] \f$false  = ( \f$false$bool  ? \f$false$true  : \f$false$false  ) ;
  wire[1:0] \f  = ( \f$bool  ? \f$true  : \f$false  ) ;
  
  assign \o0  = \f  ;
endmodule

module \Merge3$type6 (
      input \clk , input \rst 
    , input \bus_ins1$irdy , input [1:0] \bus_ins1$data , output \bus_ins1$trdy 
    , input \bus_ins2$irdy , input [1:0] \bus_ins2$data , output \bus_ins2$trdy 
    , input \bus_ins3$irdy , input [1:0] \bus_ins3$data , output \bus_ins3$trdy 
    , output \output$irdy , output [1:0] \output$data , input \output$trdy 
  );
  
  //
  // Channel declarations
  //
  wire \channel1$irdy  ;
  wire [1:0] \channel1$data  ;
  wire \channel1$trdy  ;
  
  //
  // Function Channels
  //
  wire [1:0] \ofunchan_0_Merge1$data  ;
  wire \sel_Merge1  ;
  wire [1:0] \ofunchan_0_Merge2$data  ;
  wire \sel_Merge2  ;
  
  //
  // Component and Macro instantiations
  //
  \Merge2  #(
    .INPUTSIZE1(2),
    .OUTPUTSIZE(2),
    .INPUTSIZE0(2)
  ) \Merge1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\bus_ins1$irdy )
    , .\i0$data (\bus_ins1$data )
    , .\i0$trdy (\bus_ins1$trdy )
    , .\i1$irdy (\channel1$irdy )
    , .\i1$data (\channel1$data )
    , .\i1$trdy (\channel1$trdy )
    , .\o0$irdy (\output$irdy )
    , .\o0$data (\output$data )
    , .\o0$trdy (\output$trdy )
    , .\f$data (\ofunchan_0_Merge1$data )
    , .\sel (\sel_Merge1 )
  );
  
  \OFUN_0$Merge3_Merge1  \ofun_0_Merge1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\bus_ins1$data )
    , .\i1$data (\channel1$data )
    , .\sel (\sel_Merge1 )
    , .\o0 (\ofunchan_0_Merge1$data )
  );
  
  \Merge2  #(
    .INPUTSIZE1(2),
    .OUTPUTSIZE(2),
    .INPUTSIZE0(2)
  ) \Merge2  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\bus_ins2$irdy )
    , .\i0$data (\bus_ins2$data )
    , .\i0$trdy (\bus_ins2$trdy )
    , .\i1$irdy (\bus_ins3$irdy )
    , .\i1$data (\bus_ins3$data )
    , .\i1$trdy (\bus_ins3$trdy )
    , .\o0$irdy (\channel1$irdy )
    , .\o0$data (\channel1$data )
    , .\o0$trdy (\channel1$trdy )
    , .\f$data (\ofunchan_0_Merge2$data )
    , .\sel (\sel_Merge2 )
  );
  
  \OFUN_0$Merge3_Merge2  \ofun_0_Merge2  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\bus_ins2$data )
    , .\i1$data (\bus_ins3$data )
    , .\sel (\sel_Merge2 )
    , .\o0 (\ofunchan_0_Merge2$data )
  );
  
endmodule


//
// Merge3 switch functions
//
module \OFUN_0$Merge3_Merge1 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , input [1:0] \i1$data 
    , input \sel 
    , output [1:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[0:0] \f$bool$arg0$disj  = \sel  ;
  wire[0:0] \f$bool$arg0  = \f$bool$arg0$disj [0:0] ;
  wire[0:0] \f$bool$arg1  = 1'd0 ;
  wire \f$bool  = \f$bool$arg0  == \f$bool$arg1  ;
  wire[1:0] \f$true  = \i0$data  ;
  wire[0:0] \f$false$bool$arg0$disj  = \sel  ;
  wire[0:0] \f$false$bool$arg0  = \f$false$bool$arg0$disj [0:0] ;
  wire[0:0] \f$false$bool$arg1  = 1'd1 ;
  wire \f$false$bool  = \f$false$bool$arg0  == \f$false$bool$arg1  ;
  wire[1:0] \f$false$true  = \i1$data  ;
  wire[1:0] \f$false$false  = \i0$data  ;
  wire[1:0] \f$false  = ( \f$false$bool  ? \f$false$true  : \f$false$false  ) ;
  wire[1:0] \f  = ( \f$bool  ? \f$true  : \f$false  ) ;
  
  assign \o0  = \f  ;
endmodule

module \OFUN_0$Merge3_Merge2 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , input [1:0] \i1$data 
    , input \sel 
    , output [1:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[0:0] \f$bool$arg0$disj  = \sel  ;
  wire[0:0] \f$bool$arg0  = \f$bool$arg0$disj [0:0] ;
  wire[0:0] \f$bool$arg1  = 1'd0 ;
  wire \f$bool  = \f$bool$arg0  == \f$bool$arg1  ;
  wire[1:0] \f$true  = \i0$data  ;
  wire[0:0] \f$false$bool$arg0$disj  = \sel  ;
  wire[0:0] \f$false$bool$arg0  = \f$false$bool$arg0$disj [0:0] ;
  wire[0:0] \f$false$bool$arg1  = 1'd1 ;
  wire \f$false$bool  = \f$false$bool$arg0  == \f$false$bool$arg1  ;
  wire[1:0] \f$false$true  = \i1$data  ;
  wire[1:0] \f$false$false  = \i0$data  ;
  wire[1:0] \f$false  = ( \f$false$bool  ? \f$false$true  : \f$false$false  ) ;
  wire[1:0] \f  = ( \f$bool  ? \f$true  : \f$false  ) ;
  
  assign \o0  = \f  ;
endmodule

module \Merge3$type7 (
      input \clk , input \rst 
    , input \bus_ins1$irdy , input [1:0] \bus_ins1$data , output \bus_ins1$trdy 
    , input \bus_ins2$irdy , input [1:0] \bus_ins2$data , output \bus_ins2$trdy 
    , input \bus_ins3$irdy , input [1:0] \bus_ins3$data , output \bus_ins3$trdy 
    , output \output$irdy , output [1:0] \output$data , input \output$trdy 
  );
  
  //
  // Channel declarations
  //
  wire \channel1$irdy  ;
  wire [1:0] \channel1$data  ;
  wire \channel1$trdy  ;
  
  //
  // Function Channels
  //
  wire [1:0] \ofunchan_0_Merge1$data  ;
  wire \sel_Merge1  ;
  wire [1:0] \ofunchan_0_Merge2$data  ;
  wire \sel_Merge2  ;
  
  //
  // Component and Macro instantiations
  //
  \Merge2  #(
    .INPUTSIZE1(2),
    .OUTPUTSIZE(2),
    .INPUTSIZE0(2)
  ) \Merge1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\bus_ins1$irdy )
    , .\i0$data (\bus_ins1$data )
    , .\i0$trdy (\bus_ins1$trdy )
    , .\i1$irdy (\channel1$irdy )
    , .\i1$data (\channel1$data )
    , .\i1$trdy (\channel1$trdy )
    , .\o0$irdy (\output$irdy )
    , .\o0$data (\output$data )
    , .\o0$trdy (\output$trdy )
    , .\f$data (\ofunchan_0_Merge1$data )
    , .\sel (\sel_Merge1 )
  );
  
  \OFUN_0$Merge3_Merge1  \ofun_0_Merge1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\bus_ins1$data )
    , .\i1$data (\channel1$data )
    , .\sel (\sel_Merge1 )
    , .\o0 (\ofunchan_0_Merge1$data )
  );
  
  \Merge2  #(
    .INPUTSIZE1(2),
    .OUTPUTSIZE(2),
    .INPUTSIZE0(2)
  ) \Merge2  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\bus_ins2$irdy )
    , .\i0$data (\bus_ins2$data )
    , .\i0$trdy (\bus_ins2$trdy )
    , .\i1$irdy (\bus_ins3$irdy )
    , .\i1$data (\bus_ins3$data )
    , .\i1$trdy (\bus_ins3$trdy )
    , .\o0$irdy (\channel1$irdy )
    , .\o0$data (\channel1$data )
    , .\o0$trdy (\channel1$trdy )
    , .\f$data (\ofunchan_0_Merge2$data )
    , .\sel (\sel_Merge2 )
  );
  
  \OFUN_0$Merge3_Merge2  \ofun_0_Merge2  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\bus_ins2$data )
    , .\i1$data (\bus_ins3$data )
    , .\sel (\sel_Merge2 )
    , .\o0 (\ofunchan_0_Merge2$data )
  );
  
endmodule


//
// Merge3 switch functions
//
module \OFUN_0$Merge3_Merge1 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , input [1:0] \i1$data 
    , input \sel 
    , output [1:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[0:0] \f$bool$arg0$disj  = \sel  ;
  wire[0:0] \f$bool$arg0  = \f$bool$arg0$disj [0:0] ;
  wire[0:0] \f$bool$arg1  = 1'd0 ;
  wire \f$bool  = \f$bool$arg0  == \f$bool$arg1  ;
  wire[1:0] \f$true  = \i0$data  ;
  wire[0:0] \f$false$bool$arg0$disj  = \sel  ;
  wire[0:0] \f$false$bool$arg0  = \f$false$bool$arg0$disj [0:0] ;
  wire[0:0] \f$false$bool$arg1  = 1'd1 ;
  wire \f$false$bool  = \f$false$bool$arg0  == \f$false$bool$arg1  ;
  wire[1:0] \f$false$true  = \i1$data  ;
  wire[1:0] \f$false$false  = \i0$data  ;
  wire[1:0] \f$false  = ( \f$false$bool  ? \f$false$true  : \f$false$false  ) ;
  wire[1:0] \f  = ( \f$bool  ? \f$true  : \f$false  ) ;
  
  assign \o0  = \f  ;
endmodule

module \OFUN_0$Merge3_Merge2 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , input [1:0] \i1$data 
    , input \sel 
    , output [1:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[0:0] \f$bool$arg0$disj  = \sel  ;
  wire[0:0] \f$bool$arg0  = \f$bool$arg0$disj [0:0] ;
  wire[0:0] \f$bool$arg1  = 1'd0 ;
  wire \f$bool  = \f$bool$arg0  == \f$bool$arg1  ;
  wire[1:0] \f$true  = \i0$data  ;
  wire[0:0] \f$false$bool$arg0$disj  = \sel  ;
  wire[0:0] \f$false$bool$arg0  = \f$false$bool$arg0$disj [0:0] ;
  wire[0:0] \f$false$bool$arg1  = 1'd1 ;
  wire \f$false$bool  = \f$false$bool$arg0  == \f$false$bool$arg1  ;
  wire[1:0] \f$false$true  = \i1$data  ;
  wire[1:0] \f$false$false  = \i0$data  ;
  wire[1:0] \f$false  = ( \f$false$bool  ? \f$false$true  : \f$false$false  ) ;
  wire[1:0] \f  = ( \f$bool  ? \f$true  : \f$false  ) ;
  
  assign \o0  = \f  ;
endmodule

module \RECEPTION_0_1_1_2 (
      input \clk , input \rst , input [63:0] \t 
    , input \input$irdy , input [1:0] \input$data , output \input$trdy 
    , output \bus_outs1$irdy , output [1:0] \bus_outs1$data , input \bus_outs1$trdy 
    , output \bus_outs2$irdy , output [1:0] \bus_outs2$data , input \bus_outs2$trdy 
    , output \bus_outs3$irdy , output [1:0] \bus_outs3$data , input \bus_outs3$trdy 
    , output \bus_outs4$irdy , output [0:0] \bus_outs4$data , input \bus_outs4$trdy 
    , input \CreditCounter1$PatientSource1$unbound_irdy 
    , input [0:0] \CreditCounter1$PatientSource1$unbound_data 
    , output \CreditCounter1$PatientSource1$trdy 
    , input \CreditCounter1$Sink1$unbound_trdy 
    , output \CreditCounter1$Sink1$irdy 
    , output [0:0] \CreditCounter1$Sink1$data 
  );
  
  //
  // Channel declarations
  //
  wire \noCONS$irdy  ;
  wire [1:0] \noCONS$data  ;
  wire \noCONS$trdy  ;
  wire \toRCP$irdy  ;
  wire [1:0] \toRCP$data  ;
  wire \toRCP$trdy  ;
  wire \creditBack$irdy  ;
  wire [1:0] \creditBack$data  ;
  wire \creditBack$trdy  ;
  wire \channel1$irdy  ;
  wire [1:0] \channel1$data  ;
  wire \channel1$trdy  ;
  
  //
  // Function Channels
  //
  wire \sfunchan_0_Switch1$data  ;
  wire [1:0] \ofunchan_1_Switch1$data  ;
  wire [1:0] \ofunchan_2_Switch1$data  ;
  wire \sfunchan_0_Switch2$data  ;
  wire [1:0] \ofunchan_1_Switch2$data  ;
  wire [1:0] \ofunchan_2_Switch2$data  ;
  
  //
  // Component and Macro instantiations
  //
  \Fork2  #(
    .DATASIZE(2)
  ) \Fork1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\channel1$irdy )
    , .\i0$data (\channel1$data )
    , .\i0$trdy (\channel1$trdy )
    , .\o0$irdy (\toRCP$irdy )
    , .\o0$data (\toRCP$data )
    , .\o0$trdy (\toRCP$trdy )
    , .\o1$irdy (\creditBack$irdy )
    , .\o1$data (\creditBack$data )
    , .\o1$trdy (\creditBack$trdy )
  );
  
  \Queue  #(
    .NUM_DATA(0),
    .DATASIZE(2),
    .LENGTH(2)
  ) \Queue1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\input$irdy )
    , .\i0$data (\input$data )
    , .\i0$trdy (\input$trdy )
    , .\o0$irdy (\channel1$irdy )
    , .\o0$data (\channel1$data )
    , .\o0$trdy (\channel1$trdy )
  );
  
  \Switch2  #(
    .OUTPUTSIZE0(2),
    .OUTPUTSIZE1(2),
    .INPUTSIZE(2)
  ) \Switch1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\toRCP$irdy )
    , .\i0$data (\toRCP$data )
    , .\i0$trdy (\toRCP$trdy )
    , .\o0$irdy (\bus_outs1$irdy )
    , .\o0$data (\bus_outs1$data )
    , .\o0$trdy (\bus_outs1$trdy )
    , .\o1$irdy (\noCONS$irdy )
    , .\o1$data (\noCONS$data )
    , .\o1$trdy (\noCONS$trdy )
    , .\sel$data (\sfunchan_0_Switch1$data )
    , .\f0$data (\ofunchan_1_Switch1$data )
    , .\f1$data (\ofunchan_2_Switch1$data )
  );
  
  \SFUN_0$RECEPTION_0_1_1_2_Switch1  \sfun_0_Switch1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\toRCP$data )
    , .\o0 (\sfunchan_0_Switch1$data )
  );
  
  \OFUN_1$RECEPTION_0_1_1_2_Switch1  \ofun_1_Switch1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\toRCP$data )
    , .\o0 (\ofunchan_1_Switch1$data )
  );
  
  \OFUN_2$RECEPTION_0_1_1_2_Switch1  \ofun_2_Switch1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\toRCP$data )
    , .\o0 (\ofunchan_2_Switch1$data )
  );
  
  \Switch2  #(
    .OUTPUTSIZE0(2),
    .OUTPUTSIZE1(2),
    .INPUTSIZE(2)
  ) \Switch2  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\noCONS$irdy )
    , .\i0$data (\noCONS$data )
    , .\i0$trdy (\noCONS$trdy )
    , .\o0$irdy (\bus_outs2$irdy )
    , .\o0$data (\bus_outs2$data )
    , .\o0$trdy (\bus_outs2$trdy )
    , .\o1$irdy (\bus_outs3$irdy )
    , .\o1$data (\bus_outs3$data )
    , .\o1$trdy (\bus_outs3$trdy )
    , .\sel$data (\sfunchan_0_Switch2$data )
    , .\f0$data (\ofunchan_1_Switch2$data )
    , .\f1$data (\ofunchan_2_Switch2$data )
  );
  
  \SFUN_0$RECEPTION_0_1_1_2_Switch2  \sfun_0_Switch2  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\noCONS$data )
    , .\o0 (\sfunchan_0_Switch2$data )
  );
  
  \OFUN_1$RECEPTION_0_1_1_2_Switch2  \ofun_1_Switch2  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\noCONS$data )
    , .\o0 (\ofunchan_1_Switch2$data )
  );
  
  \OFUN_2$RECEPTION_0_1_1_2_Switch2  \ofun_2_Switch2  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\noCONS$data )
    , .\o0 (\ofunchan_2_Switch2$data )
  );
  
  \CreditCounter_2  \CreditCounter1  (
      .\clk (\clk ), .\rst (\rst ), .\t (\t )
    , .\i$irdy (\creditBack$irdy )
    , .\i$data (\creditBack$data )
    , .\i$trdy (\creditBack$trdy )
    , .\o$irdy (\bus_outs4$irdy )
    , .\o$data (\bus_outs4$data )
    , .\o$trdy (\bus_outs4$trdy )
    , .\PatientSource1$unbound_irdy (\CreditCounter1$PatientSource1$unbound_irdy )
    , .\PatientSource1$unbound_data (\CreditCounter1$PatientSource1$unbound_data )
    , .\PatientSource1$trdy (\CreditCounter1$PatientSource1$trdy )
    , .\Sink1$unbound_trdy (\CreditCounter1$Sink1$unbound_trdy )
    , .\Sink1$irdy (\CreditCounter1$Sink1$irdy )
    , .\Sink1$data (\CreditCounter1$Sink1$data )
  );
  
endmodule


//
// RECEPTION_0_1_1_2 switch functions
//
module \SFUN_0$RECEPTION_0_1_1_2_Switch1 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , output [0:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[1:0] \f$bool$g0  = \i0$data  ;
  wire[1:0] \f$bool$f$arg0$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$arg0$arg0$conj  = \f$bool$f$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$arg0$arg0  = \f$bool$f$arg0$arg0$conj [1:1] ;
  wire[0:0] \f$bool$f$arg0$arg1  = 1'd0 ;
  wire \f$bool$f$arg0  = \f$bool$f$arg0$arg0  == \f$bool$f$arg0$arg1  ;
  wire[1:0] \f$bool$f$arg1$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$arg1$arg0$conj  = \f$bool$f$arg1$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$arg1$arg0  = \f$bool$f$arg1$arg0$conj [0:0] ;
  wire[0:0] \f$bool$f$arg1$arg1  = 1'd1 ;
  wire \f$bool$f$arg1  = \f$bool$f$arg1$arg0  == \f$bool$f$arg1$arg1  ;
  wire \f$bool$f  = \f$bool$f$arg0  && \f$bool$f$arg1  ;
  wire \f$bool  = \f$bool$f  ;
  wire[0:0] \f$true$content  = 1'd0 ;
  wire[0:0] \f$true  = \f$true$content  ;
  wire[1:0] \f$false$bool$g0  = \i0$data  ;
  wire[1:0] \f$false$bool$f$arg0$arg0$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$arg0$arg0$conj  = \f$false$bool$f$arg0$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$arg0$arg0  = \f$false$bool$f$arg0$arg0$arg0$conj [1:1] ;
  wire[0:0] \f$false$bool$f$arg0$arg0$arg1  = 1'd0 ;
  wire \f$false$bool$f$arg0$arg0  = \f$false$bool$f$arg0$arg0$arg0  == \f$false$bool$f$arg0$arg0$arg1  ;
  wire[1:0] \f$false$bool$f$arg0$arg1$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$arg1$arg0$conj  = \f$false$bool$f$arg0$arg1$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$arg1$arg0  = \f$false$bool$f$arg0$arg1$arg0$conj [0:0] ;
  wire[0:0] \f$false$bool$f$arg0$arg1$arg1  = 1'd1 ;
  wire \f$false$bool$f$arg0$arg1  = \f$false$bool$f$arg0$arg1$arg0  == \f$false$bool$f$arg0$arg1$arg1  ;
  wire \f$false$bool$f$arg0  = \f$false$bool$f$arg0$arg0  && \f$false$bool$f$arg0$arg1  ;
  wire \f$false$bool$f  = !\f$false$bool$f$arg0  ;
  wire \f$false$bool  = \f$false$bool$f  ;
  wire[0:0] \f$false$true$content  = 1'd1 ;
  wire[0:0] \f$false$true  = \f$false$true$content  ;
  wire[0:0] \f$false$false$content  = 1'd0 ;
  wire[0:0] \f$false$false  = \f$false$false$content  ;
  wire[0:0] \f$false  = ( \f$false$bool  ? \f$false$true  : \f$false$false  ) ;
  wire[0:0] \f  = ( \f$bool  ? \f$true  : \f$false  ) ;
  
  assign \o0  = \f  ;
endmodule

module \OFUN_1$RECEPTION_0_1_1_2_Switch1 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , output [1:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[1:0] \f  = \i0$data  ;
  
  assign \o0  = \f  ;
endmodule

module \OFUN_2$RECEPTION_0_1_1_2_Switch1 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , output [1:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[1:0] \f  = \i0$data  ;
  
  assign \o0  = \f  ;
endmodule

module \SFUN_0$RECEPTION_0_1_1_2_Switch2 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , output [0:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[1:0] \f$bool$g0  = \i0$data  ;
  wire \f$bool$f$bool  = 1'd0 ;
  wire[1:0] \f$bool$f$true$arg0$arg0$arg0$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$true$arg0$arg0$arg0$arg0$conj  = \f$bool$f$true$arg0$arg0$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$true$arg0$arg0$arg0$arg0  = \f$bool$f$true$arg0$arg0$arg0$arg0$conj [1:1] ;
  wire[0:0] \f$bool$f$true$arg0$arg0$arg0$arg1  = 1'd0 ;
  wire \f$bool$f$true$arg0$arg0$arg0  = \f$bool$f$true$arg0$arg0$arg0$arg0  == \f$bool$f$true$arg0$arg0$arg0$arg1  ;
  wire \f$bool$f$true$arg0$arg0  = !\f$bool$f$true$arg0$arg0$arg0  ;
  wire[1:0] \f$bool$f$true$arg0$arg1$arg0$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$true$arg0$arg1$arg0$arg0$conj  = \f$bool$f$true$arg0$arg1$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$true$arg0$arg1$arg0$arg0  = \f$bool$f$true$arg0$arg1$arg0$arg0$conj [1:1] ;
  wire[0:0] \f$bool$f$true$arg0$arg1$arg0$arg1  = 1'd0 ;
  wire \f$bool$f$true$arg0$arg1$arg0  = \f$bool$f$true$arg0$arg1$arg0$arg0  > \f$bool$f$true$arg0$arg1$arg0$arg1  ;
  wire \f$bool$f$true$arg0$arg1  = !\f$bool$f$true$arg0$arg1$arg0  ;
  wire \f$bool$f$true$arg0  = \f$bool$f$true$arg0$arg0  && \f$bool$f$true$arg0$arg1  ;
  wire \f$bool$f$true$arg1$arg0  = 1'd1 ;
  wire[1:0] \f$bool$f$true$arg1$arg1$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$true$arg1$arg1$arg0$conj  = \f$bool$f$true$arg1$arg1$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$true$arg1$arg1$arg0  = \f$bool$f$true$arg1$arg1$arg0$conj [1:1] ;
  wire[0:0] \f$bool$f$true$arg1$arg1$arg1  = 1'd1 ;
  wire \f$bool$f$true$arg1$arg1  = \f$bool$f$true$arg1$arg1$arg0  == \f$bool$f$true$arg1$arg1$arg1  ;
  wire \f$bool$f$true$arg1  = \f$bool$f$true$arg1$arg0  && \f$bool$f$true$arg1$arg1  ;
  wire \f$bool$f$true  = \f$bool$f$true$arg0  || \f$bool$f$true$arg1  ;
  wire \f$bool$f$false$bool  = 1'd1 ;
  wire[1:0] \f$bool$f$false$true$arg0$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$false$true$arg0$arg0$conj  = \f$bool$f$false$true$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$false$true$arg0$arg0  = \f$bool$f$false$true$arg0$arg0$conj [1:1] ;
  wire[0:0] \f$bool$f$false$true$arg0$arg1  = 1'd0 ;
  wire \f$bool$f$false$true$arg0  = \f$bool$f$false$true$arg0$arg0  > \f$bool$f$false$true$arg0$arg1  ;
  wire \f$bool$f$false$true$arg1  = 1'd0 ;
  wire \f$bool$f$false$true  = \f$bool$f$false$true$arg0  || \f$bool$f$false$true$arg1  ;
  wire \f$bool$f$false$false$bool  = 1'd0 ;
  wire[1:0] \f$bool$f$false$false$true$arg0$arg0$arg0$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$false$false$true$arg0$arg0$arg0$arg0$conj  = \f$bool$f$false$false$true$arg0$arg0$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$false$false$true$arg0$arg0$arg0$arg0  = \f$bool$f$false$false$true$arg0$arg0$arg0$arg0$conj [0:0] ;
  wire[0:0] \f$bool$f$false$false$true$arg0$arg0$arg0$arg1  = 1'd1 ;
  wire \f$bool$f$false$false$true$arg0$arg0$arg0  = \f$bool$f$false$false$true$arg0$arg0$arg0$arg0  == \f$bool$f$false$false$true$arg0$arg0$arg0$arg1  ;
  wire \f$bool$f$false$false$true$arg0$arg0  = !\f$bool$f$false$false$true$arg0$arg0$arg0  ;
  wire[1:0] \f$bool$f$false$false$true$arg0$arg1$arg0$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$false$false$true$arg0$arg1$arg0$arg0$conj  = \f$bool$f$false$false$true$arg0$arg1$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$false$false$true$arg0$arg1$arg0$arg0  = \f$bool$f$false$false$true$arg0$arg1$arg0$arg0$conj [0:0] ;
  wire[0:0] \f$bool$f$false$false$true$arg0$arg1$arg0$arg1  = 1'd1 ;
  wire \f$bool$f$false$false$true$arg0$arg1$arg0  = \f$bool$f$false$false$true$arg0$arg1$arg0$arg0  > \f$bool$f$false$false$true$arg0$arg1$arg0$arg1  ;
  wire \f$bool$f$false$false$true$arg0$arg1  = !\f$bool$f$false$false$true$arg0$arg1$arg0  ;
  wire \f$bool$f$false$false$true$arg0  = \f$bool$f$false$false$true$arg0$arg0  && \f$bool$f$false$false$true$arg0$arg1  ;
  wire \f$bool$f$false$false$true$arg1  = 1'd0 ;
  wire \f$bool$f$false$false$true  = \f$bool$f$false$false$true$arg0  || \f$bool$f$false$false$true$arg1  ;
  wire[1:0] \f$bool$f$false$false$false$arg0$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$false$false$false$arg0$arg0$conj  = \f$bool$f$false$false$false$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$false$false$false$arg0$arg0  = \f$bool$f$false$false$false$arg0$arg0$conj [0:0] ;
  wire[0:0] \f$bool$f$false$false$false$arg0$arg1  = 1'd1 ;
  wire \f$bool$f$false$false$false$arg0  = \f$bool$f$false$false$false$arg0$arg0  > \f$bool$f$false$false$false$arg0$arg1  ;
  wire \f$bool$f$false$false$false$arg1$arg0  = 1'd1 ;
  wire[1:0] \f$bool$f$false$false$false$arg1$arg1$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$false$false$false$arg1$arg1$arg0$conj  = \f$bool$f$false$false$false$arg1$arg1$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$false$false$false$arg1$arg1$arg0  = \f$bool$f$false$false$false$arg1$arg1$arg0$conj [0:0] ;
  wire[0:0] \f$bool$f$false$false$false$arg1$arg1$arg1  = 1'd0 ;
  wire \f$bool$f$false$false$false$arg1$arg1  = \f$bool$f$false$false$false$arg1$arg1$arg0  == \f$bool$f$false$false$false$arg1$arg1$arg1  ;
  wire \f$bool$f$false$false$false$arg1  = \f$bool$f$false$false$false$arg1$arg0  && \f$bool$f$false$false$false$arg1$arg1  ;
  wire \f$bool$f$false$false$false  = \f$bool$f$false$false$false$arg0  || \f$bool$f$false$false$false$arg1  ;
  wire \f$bool$f$false$false  = ( \f$bool$f$false$false$bool  ? \f$bool$f$false$false$true  : \f$bool$f$false$false$false  ) ;
  wire \f$bool$f$false  = ( \f$bool$f$false$bool  ? \f$bool$f$false$true  : \f$bool$f$false$false  ) ;
  wire \f$bool$f  = ( \f$bool$f$bool  ? \f$bool$f$true  : \f$bool$f$false  ) ;
  wire \f$bool  = \f$bool$f  ;
  wire[0:0] \f$true$content  = 1'd0 ;
  wire[0:0] \f$true  = \f$true$content  ;
  wire[1:0] \f$false$bool$g0  = \i0$data  ;
  wire \f$false$bool$f$arg0$bool  = 1'd0 ;
  wire[1:0] \f$false$bool$f$arg0$true$arg0$arg0$arg0$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$true$arg0$arg0$arg0$arg0$conj  = \f$false$bool$f$arg0$true$arg0$arg0$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$true$arg0$arg0$arg0$arg0  = \f$false$bool$f$arg0$true$arg0$arg0$arg0$arg0$conj [1:1] ;
  wire[0:0] \f$false$bool$f$arg0$true$arg0$arg0$arg0$arg1  = 1'd0 ;
  wire \f$false$bool$f$arg0$true$arg0$arg0$arg0  = \f$false$bool$f$arg0$true$arg0$arg0$arg0$arg0  == \f$false$bool$f$arg0$true$arg0$arg0$arg0$arg1  ;
  wire \f$false$bool$f$arg0$true$arg0$arg0  = !\f$false$bool$f$arg0$true$arg0$arg0$arg0  ;
  wire[1:0] \f$false$bool$f$arg0$true$arg0$arg1$arg0$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$true$arg0$arg1$arg0$arg0$conj  = \f$false$bool$f$arg0$true$arg0$arg1$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$true$arg0$arg1$arg0$arg0  = \f$false$bool$f$arg0$true$arg0$arg1$arg0$arg0$conj [1:1] ;
  wire[0:0] \f$false$bool$f$arg0$true$arg0$arg1$arg0$arg1  = 1'd0 ;
  wire \f$false$bool$f$arg0$true$arg0$arg1$arg0  = \f$false$bool$f$arg0$true$arg0$arg1$arg0$arg0  > \f$false$bool$f$arg0$true$arg0$arg1$arg0$arg1  ;
  wire \f$false$bool$f$arg0$true$arg0$arg1  = !\f$false$bool$f$arg0$true$arg0$arg1$arg0  ;
  wire \f$false$bool$f$arg0$true$arg0  = \f$false$bool$f$arg0$true$arg0$arg0  && \f$false$bool$f$arg0$true$arg0$arg1  ;
  wire \f$false$bool$f$arg0$true$arg1$arg0  = 1'd1 ;
  wire[1:0] \f$false$bool$f$arg0$true$arg1$arg1$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$true$arg1$arg1$arg0$conj  = \f$false$bool$f$arg0$true$arg1$arg1$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$true$arg1$arg1$arg0  = \f$false$bool$f$arg0$true$arg1$arg1$arg0$conj [1:1] ;
  wire[0:0] \f$false$bool$f$arg0$true$arg1$arg1$arg1  = 1'd1 ;
  wire \f$false$bool$f$arg0$true$arg1$arg1  = \f$false$bool$f$arg0$true$arg1$arg1$arg0  == \f$false$bool$f$arg0$true$arg1$arg1$arg1  ;
  wire \f$false$bool$f$arg0$true$arg1  = \f$false$bool$f$arg0$true$arg1$arg0  && \f$false$bool$f$arg0$true$arg1$arg1  ;
  wire \f$false$bool$f$arg0$true  = \f$false$bool$f$arg0$true$arg0  || \f$false$bool$f$arg0$true$arg1  ;
  wire \f$false$bool$f$arg0$false$bool  = 1'd1 ;
  wire[1:0] \f$false$bool$f$arg0$false$true$arg0$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$false$true$arg0$arg0$conj  = \f$false$bool$f$arg0$false$true$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$false$true$arg0$arg0  = \f$false$bool$f$arg0$false$true$arg0$arg0$conj [1:1] ;
  wire[0:0] \f$false$bool$f$arg0$false$true$arg0$arg1  = 1'd0 ;
  wire \f$false$bool$f$arg0$false$true$arg0  = \f$false$bool$f$arg0$false$true$arg0$arg0  > \f$false$bool$f$arg0$false$true$arg0$arg1  ;
  wire \f$false$bool$f$arg0$false$true$arg1  = 1'd0 ;
  wire \f$false$bool$f$arg0$false$true  = \f$false$bool$f$arg0$false$true$arg0  || \f$false$bool$f$arg0$false$true$arg1  ;
  wire \f$false$bool$f$arg0$false$false$bool  = 1'd0 ;
  wire[1:0] \f$false$bool$f$arg0$false$false$true$arg0$arg0$arg0$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$false$false$true$arg0$arg0$arg0$arg0$conj  = \f$false$bool$f$arg0$false$false$true$arg0$arg0$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$false$false$true$arg0$arg0$arg0$arg0  = \f$false$bool$f$arg0$false$false$true$arg0$arg0$arg0$arg0$conj [0:0] ;
  wire[0:0] \f$false$bool$f$arg0$false$false$true$arg0$arg0$arg0$arg1  = 1'd1 ;
  wire \f$false$bool$f$arg0$false$false$true$arg0$arg0$arg0  = \f$false$bool$f$arg0$false$false$true$arg0$arg0$arg0$arg0  == \f$false$bool$f$arg0$false$false$true$arg0$arg0$arg0$arg1  ;
  wire \f$false$bool$f$arg0$false$false$true$arg0$arg0  = !\f$false$bool$f$arg0$false$false$true$arg0$arg0$arg0  ;
  wire[1:0] \f$false$bool$f$arg0$false$false$true$arg0$arg1$arg0$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$false$false$true$arg0$arg1$arg0$arg0$conj  = \f$false$bool$f$arg0$false$false$true$arg0$arg1$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$false$false$true$arg0$arg1$arg0$arg0  = \f$false$bool$f$arg0$false$false$true$arg0$arg1$arg0$arg0$conj [0:0] ;
  wire[0:0] \f$false$bool$f$arg0$false$false$true$arg0$arg1$arg0$arg1  = 1'd1 ;
  wire \f$false$bool$f$arg0$false$false$true$arg0$arg1$arg0  = \f$false$bool$f$arg0$false$false$true$arg0$arg1$arg0$arg0  > \f$false$bool$f$arg0$false$false$true$arg0$arg1$arg0$arg1  ;
  wire \f$false$bool$f$arg0$false$false$true$arg0$arg1  = !\f$false$bool$f$arg0$false$false$true$arg0$arg1$arg0  ;
  wire \f$false$bool$f$arg0$false$false$true$arg0  = \f$false$bool$f$arg0$false$false$true$arg0$arg0  && \f$false$bool$f$arg0$false$false$true$arg0$arg1  ;
  wire \f$false$bool$f$arg0$false$false$true$arg1  = 1'd0 ;
  wire \f$false$bool$f$arg0$false$false$true  = \f$false$bool$f$arg0$false$false$true$arg0  || \f$false$bool$f$arg0$false$false$true$arg1  ;
  wire[1:0] \f$false$bool$f$arg0$false$false$false$arg0$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$false$false$false$arg0$arg0$conj  = \f$false$bool$f$arg0$false$false$false$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$false$false$false$arg0$arg0  = \f$false$bool$f$arg0$false$false$false$arg0$arg0$conj [0:0] ;
  wire[0:0] \f$false$bool$f$arg0$false$false$false$arg0$arg1  = 1'd1 ;
  wire \f$false$bool$f$arg0$false$false$false$arg0  = \f$false$bool$f$arg0$false$false$false$arg0$arg0  > \f$false$bool$f$arg0$false$false$false$arg0$arg1  ;
  wire \f$false$bool$f$arg0$false$false$false$arg1$arg0  = 1'd1 ;
  wire[1:0] \f$false$bool$f$arg0$false$false$false$arg1$arg1$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$false$false$false$arg1$arg1$arg0$conj  = \f$false$bool$f$arg0$false$false$false$arg1$arg1$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$false$false$false$arg1$arg1$arg0  = \f$false$bool$f$arg0$false$false$false$arg1$arg1$arg0$conj [0:0] ;
  wire[0:0] \f$false$bool$f$arg0$false$false$false$arg1$arg1$arg1  = 1'd0 ;
  wire \f$false$bool$f$arg0$false$false$false$arg1$arg1  = \f$false$bool$f$arg0$false$false$false$arg1$arg1$arg0  == \f$false$bool$f$arg0$false$false$false$arg1$arg1$arg1  ;
  wire \f$false$bool$f$arg0$false$false$false$arg1  = \f$false$bool$f$arg0$false$false$false$arg1$arg0  && \f$false$bool$f$arg0$false$false$false$arg1$arg1  ;
  wire \f$false$bool$f$arg0$false$false$false  = \f$false$bool$f$arg0$false$false$false$arg0  || \f$false$bool$f$arg0$false$false$false$arg1  ;
  wire \f$false$bool$f$arg0$false$false  = ( \f$false$bool$f$arg0$false$false$bool  ? \f$false$bool$f$arg0$false$false$true  : \f$false$bool$f$arg0$false$false$false  ) ;
  wire \f$false$bool$f$arg0$false  = ( \f$false$bool$f$arg0$false$bool  ? \f$false$bool$f$arg0$false$true  : \f$false$bool$f$arg0$false$false  ) ;
  wire \f$false$bool$f$arg0  = ( \f$false$bool$f$arg0$bool  ? \f$false$bool$f$arg0$true  : \f$false$bool$f$arg0$false  ) ;
  wire \f$false$bool$f  = !\f$false$bool$f$arg0  ;
  wire \f$false$bool  = \f$false$bool$f  ;
  wire[0:0] \f$false$true$content  = 1'd1 ;
  wire[0:0] \f$false$true  = \f$false$true$content  ;
  wire[0:0] \f$false$false$content  = 1'd0 ;
  wire[0:0] \f$false$false  = \f$false$false$content  ;
  wire[0:0] \f$false  = ( \f$false$bool  ? \f$false$true  : \f$false$false  ) ;
  wire[0:0] \f  = ( \f$bool  ? \f$true  : \f$false  ) ;
  
  assign \o0  = \f  ;
endmodule

module \OFUN_1$RECEPTION_0_1_1_2_Switch2 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , output [1:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[1:0] \f  = \i0$data  ;
  
  assign \o0  = \f  ;
endmodule

module \OFUN_2$RECEPTION_0_1_1_2_Switch2 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , output [1:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[1:0] \f  = \i0$data  ;
  
  assign \o0  = \f  ;
endmodule

module \RECEPTION_1_1_0_2 (
      input \clk , input \rst , input [63:0] \t 
    , input \input$irdy , input [1:0] \input$data , output \input$trdy 
    , output \bus_outs1$irdy , output [1:0] \bus_outs1$data , input \bus_outs1$trdy 
    , output \bus_outs2$irdy , output [1:0] \bus_outs2$data , input \bus_outs2$trdy 
    , output \bus_outs3$irdy , output [1:0] \bus_outs3$data , input \bus_outs3$trdy 
    , output \bus_outs4$irdy , output [0:0] \bus_outs4$data , input \bus_outs4$trdy 
    , input \CreditCounter1$PatientSource1$unbound_irdy 
    , input [0:0] \CreditCounter1$PatientSource1$unbound_data 
    , output \CreditCounter1$PatientSource1$trdy 
    , input \CreditCounter1$Sink1$unbound_trdy 
    , output \CreditCounter1$Sink1$irdy 
    , output [0:0] \CreditCounter1$Sink1$data 
  );
  
  //
  // Channel declarations
  //
  wire \noCONS$irdy  ;
  wire [1:0] \noCONS$data  ;
  wire \noCONS$trdy  ;
  wire \toRCP$irdy  ;
  wire [1:0] \toRCP$data  ;
  wire \toRCP$trdy  ;
  wire \creditBack$irdy  ;
  wire [1:0] \creditBack$data  ;
  wire \creditBack$trdy  ;
  wire \channel1$irdy  ;
  wire [1:0] \channel1$data  ;
  wire \channel1$trdy  ;
  
  //
  // Function Channels
  //
  wire \sfunchan_0_Switch1$data  ;
  wire [1:0] \ofunchan_1_Switch1$data  ;
  wire [1:0] \ofunchan_2_Switch1$data  ;
  wire \sfunchan_0_Switch2$data  ;
  wire [1:0] \ofunchan_1_Switch2$data  ;
  wire [1:0] \ofunchan_2_Switch2$data  ;
  
  //
  // Component and Macro instantiations
  //
  \Fork2  #(
    .DATASIZE(2)
  ) \Fork1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\channel1$irdy )
    , .\i0$data (\channel1$data )
    , .\i0$trdy (\channel1$trdy )
    , .\o0$irdy (\toRCP$irdy )
    , .\o0$data (\toRCP$data )
    , .\o0$trdy (\toRCP$trdy )
    , .\o1$irdy (\creditBack$irdy )
    , .\o1$data (\creditBack$data )
    , .\o1$trdy (\creditBack$trdy )
  );
  
  \Queue  #(
    .NUM_DATA(0),
    .DATASIZE(2),
    .LENGTH(2)
  ) \Queue1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\input$irdy )
    , .\i0$data (\input$data )
    , .\i0$trdy (\input$trdy )
    , .\o0$irdy (\channel1$irdy )
    , .\o0$data (\channel1$data )
    , .\o0$trdy (\channel1$trdy )
  );
  
  \Switch2  #(
    .OUTPUTSIZE0(2),
    .OUTPUTSIZE1(2),
    .INPUTSIZE(2)
  ) \Switch1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\toRCP$irdy )
    , .\i0$data (\toRCP$data )
    , .\i0$trdy (\toRCP$trdy )
    , .\o0$irdy (\bus_outs1$irdy )
    , .\o0$data (\bus_outs1$data )
    , .\o0$trdy (\bus_outs1$trdy )
    , .\o1$irdy (\noCONS$irdy )
    , .\o1$data (\noCONS$data )
    , .\o1$trdy (\noCONS$trdy )
    , .\sel$data (\sfunchan_0_Switch1$data )
    , .\f0$data (\ofunchan_1_Switch1$data )
    , .\f1$data (\ofunchan_2_Switch1$data )
  );
  
  \SFUN_0$RECEPTION_1_1_0_2_Switch1  \sfun_0_Switch1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\toRCP$data )
    , .\o0 (\sfunchan_0_Switch1$data )
  );
  
  \OFUN_1$RECEPTION_1_1_0_2_Switch1  \ofun_1_Switch1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\toRCP$data )
    , .\o0 (\ofunchan_1_Switch1$data )
  );
  
  \OFUN_2$RECEPTION_1_1_0_2_Switch1  \ofun_2_Switch1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\toRCP$data )
    , .\o0 (\ofunchan_2_Switch1$data )
  );
  
  \Switch2  #(
    .OUTPUTSIZE0(2),
    .OUTPUTSIZE1(2),
    .INPUTSIZE(2)
  ) \Switch2  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\noCONS$irdy )
    , .\i0$data (\noCONS$data )
    , .\i0$trdy (\noCONS$trdy )
    , .\o0$irdy (\bus_outs2$irdy )
    , .\o0$data (\bus_outs2$data )
    , .\o0$trdy (\bus_outs2$trdy )
    , .\o1$irdy (\bus_outs3$irdy )
    , .\o1$data (\bus_outs3$data )
    , .\o1$trdy (\bus_outs3$trdy )
    , .\sel$data (\sfunchan_0_Switch2$data )
    , .\f0$data (\ofunchan_1_Switch2$data )
    , .\f1$data (\ofunchan_2_Switch2$data )
  );
  
  \SFUN_0$RECEPTION_1_1_0_2_Switch2  \sfun_0_Switch2  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\noCONS$data )
    , .\o0 (\sfunchan_0_Switch2$data )
  );
  
  \OFUN_1$RECEPTION_1_1_0_2_Switch2  \ofun_1_Switch2  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\noCONS$data )
    , .\o0 (\ofunchan_1_Switch2$data )
  );
  
  \OFUN_2$RECEPTION_1_1_0_2_Switch2  \ofun_2_Switch2  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\noCONS$data )
    , .\o0 (\ofunchan_2_Switch2$data )
  );
  
  \CreditCounter_2  \CreditCounter1  (
      .\clk (\clk ), .\rst (\rst ), .\t (\t )
    , .\i$irdy (\creditBack$irdy )
    , .\i$data (\creditBack$data )
    , .\i$trdy (\creditBack$trdy )
    , .\o$irdy (\bus_outs4$irdy )
    , .\o$data (\bus_outs4$data )
    , .\o$trdy (\bus_outs4$trdy )
    , .\PatientSource1$unbound_irdy (\CreditCounter1$PatientSource1$unbound_irdy )
    , .\PatientSource1$unbound_data (\CreditCounter1$PatientSource1$unbound_data )
    , .\PatientSource1$trdy (\CreditCounter1$PatientSource1$trdy )
    , .\Sink1$unbound_trdy (\CreditCounter1$Sink1$unbound_trdy )
    , .\Sink1$irdy (\CreditCounter1$Sink1$irdy )
    , .\Sink1$data (\CreditCounter1$Sink1$data )
  );
  
endmodule


//
// RECEPTION_1_1_0_2 switch functions
//
module \SFUN_0$RECEPTION_1_1_0_2_Switch1 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , output [0:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[1:0] \f$bool$g0  = \i0$data  ;
  wire[1:0] \f$bool$f$arg0$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$arg0$arg0$conj  = \f$bool$f$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$arg0$arg0  = \f$bool$f$arg0$arg0$conj [1:1] ;
  wire[0:0] \f$bool$f$arg0$arg1  = 1'd1 ;
  wire \f$bool$f$arg0  = \f$bool$f$arg0$arg0  == \f$bool$f$arg0$arg1  ;
  wire[1:0] \f$bool$f$arg1$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$arg1$arg0$conj  = \f$bool$f$arg1$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$arg1$arg0  = \f$bool$f$arg1$arg0$conj [0:0] ;
  wire[0:0] \f$bool$f$arg1$arg1  = 1'd1 ;
  wire \f$bool$f$arg1  = \f$bool$f$arg1$arg0  == \f$bool$f$arg1$arg1  ;
  wire \f$bool$f  = \f$bool$f$arg0  && \f$bool$f$arg1  ;
  wire \f$bool  = \f$bool$f  ;
  wire[0:0] \f$true$content  = 1'd0 ;
  wire[0:0] \f$true  = \f$true$content  ;
  wire[1:0] \f$false$bool$g0  = \i0$data  ;
  wire[1:0] \f$false$bool$f$arg0$arg0$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$arg0$arg0$conj  = \f$false$bool$f$arg0$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$arg0$arg0  = \f$false$bool$f$arg0$arg0$arg0$conj [1:1] ;
  wire[0:0] \f$false$bool$f$arg0$arg0$arg1  = 1'd1 ;
  wire \f$false$bool$f$arg0$arg0  = \f$false$bool$f$arg0$arg0$arg0  == \f$false$bool$f$arg0$arg0$arg1  ;
  wire[1:0] \f$false$bool$f$arg0$arg1$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$arg1$arg0$conj  = \f$false$bool$f$arg0$arg1$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$arg1$arg0  = \f$false$bool$f$arg0$arg1$arg0$conj [0:0] ;
  wire[0:0] \f$false$bool$f$arg0$arg1$arg1  = 1'd1 ;
  wire \f$false$bool$f$arg0$arg1  = \f$false$bool$f$arg0$arg1$arg0  == \f$false$bool$f$arg0$arg1$arg1  ;
  wire \f$false$bool$f$arg0  = \f$false$bool$f$arg0$arg0  && \f$false$bool$f$arg0$arg1  ;
  wire \f$false$bool$f  = !\f$false$bool$f$arg0  ;
  wire \f$false$bool  = \f$false$bool$f  ;
  wire[0:0] \f$false$true$content  = 1'd1 ;
  wire[0:0] \f$false$true  = \f$false$true$content  ;
  wire[0:0] \f$false$false$content  = 1'd0 ;
  wire[0:0] \f$false$false  = \f$false$false$content  ;
  wire[0:0] \f$false  = ( \f$false$bool  ? \f$false$true  : \f$false$false  ) ;
  wire[0:0] \f  = ( \f$bool  ? \f$true  : \f$false  ) ;
  
  assign \o0  = \f  ;
endmodule

module \OFUN_1$RECEPTION_1_1_0_2_Switch1 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , output [1:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[1:0] \f  = \i0$data  ;
  
  assign \o0  = \f  ;
endmodule

module \OFUN_2$RECEPTION_1_1_0_2_Switch1 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , output [1:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[1:0] \f  = \i0$data  ;
  
  assign \o0  = \f  ;
endmodule

module \SFUN_0$RECEPTION_1_1_0_2_Switch2 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , output [0:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[1:0] \f$bool$g0  = \i0$data  ;
  wire \f$bool$f$bool  = 1'd1 ;
  wire[1:0] \f$bool$f$true$arg0$arg0$arg0$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$true$arg0$arg0$arg0$arg0$conj  = \f$bool$f$true$arg0$arg0$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$true$arg0$arg0$arg0$arg0  = \f$bool$f$true$arg0$arg0$arg0$arg0$conj [1:1] ;
  wire[0:0] \f$bool$f$true$arg0$arg0$arg0$arg1  = 1'd1 ;
  wire \f$bool$f$true$arg0$arg0$arg0  = \f$bool$f$true$arg0$arg0$arg0$arg0  == \f$bool$f$true$arg0$arg0$arg0$arg1  ;
  wire \f$bool$f$true$arg0$arg0  = !\f$bool$f$true$arg0$arg0$arg0  ;
  wire[1:0] \f$bool$f$true$arg0$arg1$arg0$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$true$arg0$arg1$arg0$arg0$conj  = \f$bool$f$true$arg0$arg1$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$true$arg0$arg1$arg0$arg0  = \f$bool$f$true$arg0$arg1$arg0$arg0$conj [1:1] ;
  wire[0:0] \f$bool$f$true$arg0$arg1$arg0$arg1  = 1'd1 ;
  wire \f$bool$f$true$arg0$arg1$arg0  = \f$bool$f$true$arg0$arg1$arg0$arg0  > \f$bool$f$true$arg0$arg1$arg0$arg1  ;
  wire \f$bool$f$true$arg0$arg1  = !\f$bool$f$true$arg0$arg1$arg0  ;
  wire \f$bool$f$true$arg0  = \f$bool$f$true$arg0$arg0  && \f$bool$f$true$arg0$arg1  ;
  wire \f$bool$f$true$arg1  = 1'd0 ;
  wire \f$bool$f$true  = \f$bool$f$true$arg0  || \f$bool$f$true$arg1  ;
  wire \f$bool$f$false$bool  = 1'd0 ;
  wire[1:0] \f$bool$f$false$true$arg0$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$false$true$arg0$arg0$conj  = \f$bool$f$false$true$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$false$true$arg0$arg0  = \f$bool$f$false$true$arg0$arg0$conj [1:1] ;
  wire[0:0] \f$bool$f$false$true$arg0$arg1  = 1'd1 ;
  wire \f$bool$f$false$true$arg0  = \f$bool$f$false$true$arg0$arg0  > \f$bool$f$false$true$arg0$arg1  ;
  wire \f$bool$f$false$true$arg1$arg0  = 1'd1 ;
  wire[1:0] \f$bool$f$false$true$arg1$arg1$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$false$true$arg1$arg1$arg0$conj  = \f$bool$f$false$true$arg1$arg1$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$false$true$arg1$arg1$arg0  = \f$bool$f$false$true$arg1$arg1$arg0$conj [1:1] ;
  wire[0:0] \f$bool$f$false$true$arg1$arg1$arg1  = 1'd0 ;
  wire \f$bool$f$false$true$arg1$arg1  = \f$bool$f$false$true$arg1$arg1$arg0  == \f$bool$f$false$true$arg1$arg1$arg1  ;
  wire \f$bool$f$false$true$arg1  = \f$bool$f$false$true$arg1$arg0  && \f$bool$f$false$true$arg1$arg1  ;
  wire \f$bool$f$false$true  = \f$bool$f$false$true$arg0  || \f$bool$f$false$true$arg1  ;
  wire \f$bool$f$false$false$bool  = 1'd0 ;
  wire[1:0] \f$bool$f$false$false$true$arg0$arg0$arg0$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$false$false$true$arg0$arg0$arg0$arg0$conj  = \f$bool$f$false$false$true$arg0$arg0$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$false$false$true$arg0$arg0$arg0$arg0  = \f$bool$f$false$false$true$arg0$arg0$arg0$arg0$conj [0:0] ;
  wire[0:0] \f$bool$f$false$false$true$arg0$arg0$arg0$arg1  = 1'd1 ;
  wire \f$bool$f$false$false$true$arg0$arg0$arg0  = \f$bool$f$false$false$true$arg0$arg0$arg0$arg0  == \f$bool$f$false$false$true$arg0$arg0$arg0$arg1  ;
  wire \f$bool$f$false$false$true$arg0$arg0  = !\f$bool$f$false$false$true$arg0$arg0$arg0  ;
  wire[1:0] \f$bool$f$false$false$true$arg0$arg1$arg0$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$false$false$true$arg0$arg1$arg0$arg0$conj  = \f$bool$f$false$false$true$arg0$arg1$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$false$false$true$arg0$arg1$arg0$arg0  = \f$bool$f$false$false$true$arg0$arg1$arg0$arg0$conj [0:0] ;
  wire[0:0] \f$bool$f$false$false$true$arg0$arg1$arg0$arg1  = 1'd1 ;
  wire \f$bool$f$false$false$true$arg0$arg1$arg0  = \f$bool$f$false$false$true$arg0$arg1$arg0$arg0  > \f$bool$f$false$false$true$arg0$arg1$arg0$arg1  ;
  wire \f$bool$f$false$false$true$arg0$arg1  = !\f$bool$f$false$false$true$arg0$arg1$arg0  ;
  wire \f$bool$f$false$false$true$arg0  = \f$bool$f$false$false$true$arg0$arg0  && \f$bool$f$false$false$true$arg0$arg1  ;
  wire \f$bool$f$false$false$true$arg1  = 1'd0 ;
  wire \f$bool$f$false$false$true  = \f$bool$f$false$false$true$arg0  || \f$bool$f$false$false$true$arg1  ;
  wire[1:0] \f$bool$f$false$false$false$arg0$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$false$false$false$arg0$arg0$conj  = \f$bool$f$false$false$false$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$false$false$false$arg0$arg0  = \f$bool$f$false$false$false$arg0$arg0$conj [0:0] ;
  wire[0:0] \f$bool$f$false$false$false$arg0$arg1  = 1'd1 ;
  wire \f$bool$f$false$false$false$arg0  = \f$bool$f$false$false$false$arg0$arg0  > \f$bool$f$false$false$false$arg0$arg1  ;
  wire \f$bool$f$false$false$false$arg1$arg0  = 1'd1 ;
  wire[1:0] \f$bool$f$false$false$false$arg1$arg1$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$false$false$false$arg1$arg1$arg0$conj  = \f$bool$f$false$false$false$arg1$arg1$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$false$false$false$arg1$arg1$arg0  = \f$bool$f$false$false$false$arg1$arg1$arg0$conj [0:0] ;
  wire[0:0] \f$bool$f$false$false$false$arg1$arg1$arg1  = 1'd0 ;
  wire \f$bool$f$false$false$false$arg1$arg1  = \f$bool$f$false$false$false$arg1$arg1$arg0  == \f$bool$f$false$false$false$arg1$arg1$arg1  ;
  wire \f$bool$f$false$false$false$arg1  = \f$bool$f$false$false$false$arg1$arg0  && \f$bool$f$false$false$false$arg1$arg1  ;
  wire \f$bool$f$false$false$false  = \f$bool$f$false$false$false$arg0  || \f$bool$f$false$false$false$arg1  ;
  wire \f$bool$f$false$false  = ( \f$bool$f$false$false$bool  ? \f$bool$f$false$false$true  : \f$bool$f$false$false$false  ) ;
  wire \f$bool$f$false  = ( \f$bool$f$false$bool  ? \f$bool$f$false$true  : \f$bool$f$false$false  ) ;
  wire \f$bool$f  = ( \f$bool$f$bool  ? \f$bool$f$true  : \f$bool$f$false  ) ;
  wire \f$bool  = \f$bool$f  ;
  wire[0:0] \f$true$content  = 1'd0 ;
  wire[0:0] \f$true  = \f$true$content  ;
  wire[1:0] \f$false$bool$g0  = \i0$data  ;
  wire \f$false$bool$f$arg0$bool  = 1'd1 ;
  wire[1:0] \f$false$bool$f$arg0$true$arg0$arg0$arg0$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$true$arg0$arg0$arg0$arg0$conj  = \f$false$bool$f$arg0$true$arg0$arg0$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$true$arg0$arg0$arg0$arg0  = \f$false$bool$f$arg0$true$arg0$arg0$arg0$arg0$conj [1:1] ;
  wire[0:0] \f$false$bool$f$arg0$true$arg0$arg0$arg0$arg1  = 1'd1 ;
  wire \f$false$bool$f$arg0$true$arg0$arg0$arg0  = \f$false$bool$f$arg0$true$arg0$arg0$arg0$arg0  == \f$false$bool$f$arg0$true$arg0$arg0$arg0$arg1  ;
  wire \f$false$bool$f$arg0$true$arg0$arg0  = !\f$false$bool$f$arg0$true$arg0$arg0$arg0  ;
  wire[1:0] \f$false$bool$f$arg0$true$arg0$arg1$arg0$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$true$arg0$arg1$arg0$arg0$conj  = \f$false$bool$f$arg0$true$arg0$arg1$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$true$arg0$arg1$arg0$arg0  = \f$false$bool$f$arg0$true$arg0$arg1$arg0$arg0$conj [1:1] ;
  wire[0:0] \f$false$bool$f$arg0$true$arg0$arg1$arg0$arg1  = 1'd1 ;
  wire \f$false$bool$f$arg0$true$arg0$arg1$arg0  = \f$false$bool$f$arg0$true$arg0$arg1$arg0$arg0  > \f$false$bool$f$arg0$true$arg0$arg1$arg0$arg1  ;
  wire \f$false$bool$f$arg0$true$arg0$arg1  = !\f$false$bool$f$arg0$true$arg0$arg1$arg0  ;
  wire \f$false$bool$f$arg0$true$arg0  = \f$false$bool$f$arg0$true$arg0$arg0  && \f$false$bool$f$arg0$true$arg0$arg1  ;
  wire \f$false$bool$f$arg0$true$arg1  = 1'd0 ;
  wire \f$false$bool$f$arg0$true  = \f$false$bool$f$arg0$true$arg0  || \f$false$bool$f$arg0$true$arg1  ;
  wire \f$false$bool$f$arg0$false$bool  = 1'd0 ;
  wire[1:0] \f$false$bool$f$arg0$false$true$arg0$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$false$true$arg0$arg0$conj  = \f$false$bool$f$arg0$false$true$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$false$true$arg0$arg0  = \f$false$bool$f$arg0$false$true$arg0$arg0$conj [1:1] ;
  wire[0:0] \f$false$bool$f$arg0$false$true$arg0$arg1  = 1'd1 ;
  wire \f$false$bool$f$arg0$false$true$arg0  = \f$false$bool$f$arg0$false$true$arg0$arg0  > \f$false$bool$f$arg0$false$true$arg0$arg1  ;
  wire \f$false$bool$f$arg0$false$true$arg1$arg0  = 1'd1 ;
  wire[1:0] \f$false$bool$f$arg0$false$true$arg1$arg1$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$false$true$arg1$arg1$arg0$conj  = \f$false$bool$f$arg0$false$true$arg1$arg1$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$false$true$arg1$arg1$arg0  = \f$false$bool$f$arg0$false$true$arg1$arg1$arg0$conj [1:1] ;
  wire[0:0] \f$false$bool$f$arg0$false$true$arg1$arg1$arg1  = 1'd0 ;
  wire \f$false$bool$f$arg0$false$true$arg1$arg1  = \f$false$bool$f$arg0$false$true$arg1$arg1$arg0  == \f$false$bool$f$arg0$false$true$arg1$arg1$arg1  ;
  wire \f$false$bool$f$arg0$false$true$arg1  = \f$false$bool$f$arg0$false$true$arg1$arg0  && \f$false$bool$f$arg0$false$true$arg1$arg1  ;
  wire \f$false$bool$f$arg0$false$true  = \f$false$bool$f$arg0$false$true$arg0  || \f$false$bool$f$arg0$false$true$arg1  ;
  wire \f$false$bool$f$arg0$false$false$bool  = 1'd0 ;
  wire[1:0] \f$false$bool$f$arg0$false$false$true$arg0$arg0$arg0$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$false$false$true$arg0$arg0$arg0$arg0$conj  = \f$false$bool$f$arg0$false$false$true$arg0$arg0$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$false$false$true$arg0$arg0$arg0$arg0  = \f$false$bool$f$arg0$false$false$true$arg0$arg0$arg0$arg0$conj [0:0] ;
  wire[0:0] \f$false$bool$f$arg0$false$false$true$arg0$arg0$arg0$arg1  = 1'd1 ;
  wire \f$false$bool$f$arg0$false$false$true$arg0$arg0$arg0  = \f$false$bool$f$arg0$false$false$true$arg0$arg0$arg0$arg0  == \f$false$bool$f$arg0$false$false$true$arg0$arg0$arg0$arg1  ;
  wire \f$false$bool$f$arg0$false$false$true$arg0$arg0  = !\f$false$bool$f$arg0$false$false$true$arg0$arg0$arg0  ;
  wire[1:0] \f$false$bool$f$arg0$false$false$true$arg0$arg1$arg0$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$false$false$true$arg0$arg1$arg0$arg0$conj  = \f$false$bool$f$arg0$false$false$true$arg0$arg1$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$false$false$true$arg0$arg1$arg0$arg0  = \f$false$bool$f$arg0$false$false$true$arg0$arg1$arg0$arg0$conj [0:0] ;
  wire[0:0] \f$false$bool$f$arg0$false$false$true$arg0$arg1$arg0$arg1  = 1'd1 ;
  wire \f$false$bool$f$arg0$false$false$true$arg0$arg1$arg0  = \f$false$bool$f$arg0$false$false$true$arg0$arg1$arg0$arg0  > \f$false$bool$f$arg0$false$false$true$arg0$arg1$arg0$arg1  ;
  wire \f$false$bool$f$arg0$false$false$true$arg0$arg1  = !\f$false$bool$f$arg0$false$false$true$arg0$arg1$arg0  ;
  wire \f$false$bool$f$arg0$false$false$true$arg0  = \f$false$bool$f$arg0$false$false$true$arg0$arg0  && \f$false$bool$f$arg0$false$false$true$arg0$arg1  ;
  wire \f$false$bool$f$arg0$false$false$true$arg1  = 1'd0 ;
  wire \f$false$bool$f$arg0$false$false$true  = \f$false$bool$f$arg0$false$false$true$arg0  || \f$false$bool$f$arg0$false$false$true$arg1  ;
  wire[1:0] \f$false$bool$f$arg0$false$false$false$arg0$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$false$false$false$arg0$arg0$conj  = \f$false$bool$f$arg0$false$false$false$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$false$false$false$arg0$arg0  = \f$false$bool$f$arg0$false$false$false$arg0$arg0$conj [0:0] ;
  wire[0:0] \f$false$bool$f$arg0$false$false$false$arg0$arg1  = 1'd1 ;
  wire \f$false$bool$f$arg0$false$false$false$arg0  = \f$false$bool$f$arg0$false$false$false$arg0$arg0  > \f$false$bool$f$arg0$false$false$false$arg0$arg1  ;
  wire \f$false$bool$f$arg0$false$false$false$arg1$arg0  = 1'd1 ;
  wire[1:0] \f$false$bool$f$arg0$false$false$false$arg1$arg1$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$false$false$false$arg1$arg1$arg0$conj  = \f$false$bool$f$arg0$false$false$false$arg1$arg1$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$false$false$false$arg1$arg1$arg0  = \f$false$bool$f$arg0$false$false$false$arg1$arg1$arg0$conj [0:0] ;
  wire[0:0] \f$false$bool$f$arg0$false$false$false$arg1$arg1$arg1  = 1'd0 ;
  wire \f$false$bool$f$arg0$false$false$false$arg1$arg1  = \f$false$bool$f$arg0$false$false$false$arg1$arg1$arg0  == \f$false$bool$f$arg0$false$false$false$arg1$arg1$arg1  ;
  wire \f$false$bool$f$arg0$false$false$false$arg1  = \f$false$bool$f$arg0$false$false$false$arg1$arg0  && \f$false$bool$f$arg0$false$false$false$arg1$arg1  ;
  wire \f$false$bool$f$arg0$false$false$false  = \f$false$bool$f$arg0$false$false$false$arg0  || \f$false$bool$f$arg0$false$false$false$arg1  ;
  wire \f$false$bool$f$arg0$false$false  = ( \f$false$bool$f$arg0$false$false$bool  ? \f$false$bool$f$arg0$false$false$true  : \f$false$bool$f$arg0$false$false$false  ) ;
  wire \f$false$bool$f$arg0$false  = ( \f$false$bool$f$arg0$false$bool  ? \f$false$bool$f$arg0$false$true  : \f$false$bool$f$arg0$false$false  ) ;
  wire \f$false$bool$f$arg0  = ( \f$false$bool$f$arg0$bool  ? \f$false$bool$f$arg0$true  : \f$false$bool$f$arg0$false  ) ;
  wire \f$false$bool$f  = !\f$false$bool$f$arg0  ;
  wire \f$false$bool  = \f$false$bool$f  ;
  wire[0:0] \f$false$true$content  = 1'd1 ;
  wire[0:0] \f$false$true  = \f$false$true$content  ;
  wire[0:0] \f$false$false$content  = 1'd0 ;
  wire[0:0] \f$false$false  = \f$false$false$content  ;
  wire[0:0] \f$false  = ( \f$false$bool  ? \f$false$true  : \f$false$false  ) ;
  wire[0:0] \f  = ( \f$bool  ? \f$true  : \f$false  ) ;
  
  assign \o0  = \f  ;
endmodule

module \OFUN_1$RECEPTION_1_1_0_2_Switch2 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , output [1:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[1:0] \f  = \i0$data  ;
  
  assign \o0  = \f  ;
endmodule

module \OFUN_2$RECEPTION_1_1_0_2_Switch2 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , output [1:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[1:0] \f  = \i0$data  ;
  
  assign \o0  = \f  ;
endmodule

module \RECEPTION_0_0_3_2 (
      input \clk , input \rst , input [63:0] \t 
    , input \input$irdy , input [1:0] \input$data , output \input$trdy 
    , output \bus_outs1$irdy , output [1:0] \bus_outs1$data , input \bus_outs1$trdy 
    , output \bus_outs2$irdy , output [1:0] \bus_outs2$data , input \bus_outs2$trdy 
    , output \bus_outs3$irdy , output [1:0] \bus_outs3$data , input \bus_outs3$trdy 
    , output \bus_outs4$irdy , output [0:0] \bus_outs4$data , input \bus_outs4$trdy 
    , input \CreditCounter1$PatientSource1$unbound_irdy 
    , input [0:0] \CreditCounter1$PatientSource1$unbound_data 
    , output \CreditCounter1$PatientSource1$trdy 
    , input \CreditCounter1$Sink1$unbound_trdy 
    , output \CreditCounter1$Sink1$irdy 
    , output [0:0] \CreditCounter1$Sink1$data 
  );
  
  //
  // Channel declarations
  //
  wire \noCONS$irdy  ;
  wire [1:0] \noCONS$data  ;
  wire \noCONS$trdy  ;
  wire \toRCP$irdy  ;
  wire [1:0] \toRCP$data  ;
  wire \toRCP$trdy  ;
  wire \creditBack$irdy  ;
  wire [1:0] \creditBack$data  ;
  wire \creditBack$trdy  ;
  wire \channel1$irdy  ;
  wire [1:0] \channel1$data  ;
  wire \channel1$trdy  ;
  
  //
  // Function Channels
  //
  wire \sfunchan_0_Switch1$data  ;
  wire [1:0] \ofunchan_1_Switch1$data  ;
  wire [1:0] \ofunchan_2_Switch1$data  ;
  wire \sfunchan_0_Switch2$data  ;
  wire [1:0] \ofunchan_1_Switch2$data  ;
  wire [1:0] \ofunchan_2_Switch2$data  ;
  
  //
  // Component and Macro instantiations
  //
  \Fork2  #(
    .DATASIZE(2)
  ) \Fork1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\channel1$irdy )
    , .\i0$data (\channel1$data )
    , .\i0$trdy (\channel1$trdy )
    , .\o0$irdy (\toRCP$irdy )
    , .\o0$data (\toRCP$data )
    , .\o0$trdy (\toRCP$trdy )
    , .\o1$irdy (\creditBack$irdy )
    , .\o1$data (\creditBack$data )
    , .\o1$trdy (\creditBack$trdy )
  );
  
  \Queue  #(
    .NUM_DATA(0),
    .DATASIZE(2),
    .LENGTH(2)
  ) \Queue1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\input$irdy )
    , .\i0$data (\input$data )
    , .\i0$trdy (\input$trdy )
    , .\o0$irdy (\channel1$irdy )
    , .\o0$data (\channel1$data )
    , .\o0$trdy (\channel1$trdy )
  );
  
  \Switch2  #(
    .OUTPUTSIZE0(2),
    .OUTPUTSIZE1(2),
    .INPUTSIZE(2)
  ) \Switch1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\toRCP$irdy )
    , .\i0$data (\toRCP$data )
    , .\i0$trdy (\toRCP$trdy )
    , .\o0$irdy (\bus_outs1$irdy )
    , .\o0$data (\bus_outs1$data )
    , .\o0$trdy (\bus_outs1$trdy )
    , .\o1$irdy (\noCONS$irdy )
    , .\o1$data (\noCONS$data )
    , .\o1$trdy (\noCONS$trdy )
    , .\sel$data (\sfunchan_0_Switch1$data )
    , .\f0$data (\ofunchan_1_Switch1$data )
    , .\f1$data (\ofunchan_2_Switch1$data )
  );
  
  \SFUN_0$RECEPTION_0_0_3_2_Switch1  \sfun_0_Switch1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\toRCP$data )
    , .\o0 (\sfunchan_0_Switch1$data )
  );
  
  \OFUN_1$RECEPTION_0_0_3_2_Switch1  \ofun_1_Switch1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\toRCP$data )
    , .\o0 (\ofunchan_1_Switch1$data )
  );
  
  \OFUN_2$RECEPTION_0_0_3_2_Switch1  \ofun_2_Switch1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\toRCP$data )
    , .\o0 (\ofunchan_2_Switch1$data )
  );
  
  \Switch2  #(
    .OUTPUTSIZE0(2),
    .OUTPUTSIZE1(2),
    .INPUTSIZE(2)
  ) \Switch2  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\noCONS$irdy )
    , .\i0$data (\noCONS$data )
    , .\i0$trdy (\noCONS$trdy )
    , .\o0$irdy (\bus_outs2$irdy )
    , .\o0$data (\bus_outs2$data )
    , .\o0$trdy (\bus_outs2$trdy )
    , .\o1$irdy (\bus_outs3$irdy )
    , .\o1$data (\bus_outs3$data )
    , .\o1$trdy (\bus_outs3$trdy )
    , .\sel$data (\sfunchan_0_Switch2$data )
    , .\f0$data (\ofunchan_1_Switch2$data )
    , .\f1$data (\ofunchan_2_Switch2$data )
  );
  
  \SFUN_0$RECEPTION_0_0_3_2_Switch2  \sfun_0_Switch2  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\noCONS$data )
    , .\o0 (\sfunchan_0_Switch2$data )
  );
  
  \OFUN_1$RECEPTION_0_0_3_2_Switch2  \ofun_1_Switch2  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\noCONS$data )
    , .\o0 (\ofunchan_1_Switch2$data )
  );
  
  \OFUN_2$RECEPTION_0_0_3_2_Switch2  \ofun_2_Switch2  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\noCONS$data )
    , .\o0 (\ofunchan_2_Switch2$data )
  );
  
  \CreditCounter_2  \CreditCounter1  (
      .\clk (\clk ), .\rst (\rst ), .\t (\t )
    , .\i$irdy (\creditBack$irdy )
    , .\i$data (\creditBack$data )
    , .\i$trdy (\creditBack$trdy )
    , .\o$irdy (\bus_outs4$irdy )
    , .\o$data (\bus_outs4$data )
    , .\o$trdy (\bus_outs4$trdy )
    , .\PatientSource1$unbound_irdy (\CreditCounter1$PatientSource1$unbound_irdy )
    , .\PatientSource1$unbound_data (\CreditCounter1$PatientSource1$unbound_data )
    , .\PatientSource1$trdy (\CreditCounter1$PatientSource1$trdy )
    , .\Sink1$unbound_trdy (\CreditCounter1$Sink1$unbound_trdy )
    , .\Sink1$irdy (\CreditCounter1$Sink1$irdy )
    , .\Sink1$data (\CreditCounter1$Sink1$data )
  );
  
endmodule


//
// RECEPTION_0_0_3_2 switch functions
//
module \SFUN_0$RECEPTION_0_0_3_2_Switch1 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , output [0:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[1:0] \f$bool$g0  = \i0$data  ;
  wire[1:0] \f$bool$f$arg0$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$arg0$arg0$conj  = \f$bool$f$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$arg0$arg0  = \f$bool$f$arg0$arg0$conj [1:1] ;
  wire[0:0] \f$bool$f$arg0$arg1  = 1'd0 ;
  wire \f$bool$f$arg0  = \f$bool$f$arg0$arg0  == \f$bool$f$arg0$arg1  ;
  wire[1:0] \f$bool$f$arg1$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$arg1$arg0$conj  = \f$bool$f$arg1$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$arg1$arg0  = \f$bool$f$arg1$arg0$conj [0:0] ;
  wire[0:0] \f$bool$f$arg1$arg1  = 1'd0 ;
  wire \f$bool$f$arg1  = \f$bool$f$arg1$arg0  == \f$bool$f$arg1$arg1  ;
  wire \f$bool$f  = \f$bool$f$arg0  && \f$bool$f$arg1  ;
  wire \f$bool  = \f$bool$f  ;
  wire[0:0] \f$true$content  = 1'd0 ;
  wire[0:0] \f$true  = \f$true$content  ;
  wire[1:0] \f$false$bool$g0  = \i0$data  ;
  wire[1:0] \f$false$bool$f$arg0$arg0$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$arg0$arg0$conj  = \f$false$bool$f$arg0$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$arg0$arg0  = \f$false$bool$f$arg0$arg0$arg0$conj [1:1] ;
  wire[0:0] \f$false$bool$f$arg0$arg0$arg1  = 1'd0 ;
  wire \f$false$bool$f$arg0$arg0  = \f$false$bool$f$arg0$arg0$arg0  == \f$false$bool$f$arg0$arg0$arg1  ;
  wire[1:0] \f$false$bool$f$arg0$arg1$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$arg1$arg0$conj  = \f$false$bool$f$arg0$arg1$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$arg1$arg0  = \f$false$bool$f$arg0$arg1$arg0$conj [0:0] ;
  wire[0:0] \f$false$bool$f$arg0$arg1$arg1  = 1'd0 ;
  wire \f$false$bool$f$arg0$arg1  = \f$false$bool$f$arg0$arg1$arg0  == \f$false$bool$f$arg0$arg1$arg1  ;
  wire \f$false$bool$f$arg0  = \f$false$bool$f$arg0$arg0  && \f$false$bool$f$arg0$arg1  ;
  wire \f$false$bool$f  = !\f$false$bool$f$arg0  ;
  wire \f$false$bool  = \f$false$bool$f  ;
  wire[0:0] \f$false$true$content  = 1'd1 ;
  wire[0:0] \f$false$true  = \f$false$true$content  ;
  wire[0:0] \f$false$false$content  = 1'd0 ;
  wire[0:0] \f$false$false  = \f$false$false$content  ;
  wire[0:0] \f$false  = ( \f$false$bool  ? \f$false$true  : \f$false$false  ) ;
  wire[0:0] \f  = ( \f$bool  ? \f$true  : \f$false  ) ;
  
  assign \o0  = \f  ;
endmodule

module \OFUN_1$RECEPTION_0_0_3_2_Switch1 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , output [1:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[1:0] \f  = \i0$data  ;
  
  assign \o0  = \f  ;
endmodule

module \OFUN_2$RECEPTION_0_0_3_2_Switch1 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , output [1:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[1:0] \f  = \i0$data  ;
  
  assign \o0  = \f  ;
endmodule

module \SFUN_0$RECEPTION_0_0_3_2_Switch2 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , output [0:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[1:0] \f$bool$g0  = \i0$data  ;
  wire \f$bool$f$bool  = 1'd0 ;
  wire[1:0] \f$bool$f$true$arg0$arg0$arg0$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$true$arg0$arg0$arg0$arg0$conj  = \f$bool$f$true$arg0$arg0$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$true$arg0$arg0$arg0$arg0  = \f$bool$f$true$arg0$arg0$arg0$arg0$conj [1:1] ;
  wire[0:0] \f$bool$f$true$arg0$arg0$arg0$arg1  = 1'd0 ;
  wire \f$bool$f$true$arg0$arg0$arg0  = \f$bool$f$true$arg0$arg0$arg0$arg0  == \f$bool$f$true$arg0$arg0$arg0$arg1  ;
  wire \f$bool$f$true$arg0$arg0  = !\f$bool$f$true$arg0$arg0$arg0  ;
  wire[1:0] \f$bool$f$true$arg0$arg1$arg0$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$true$arg0$arg1$arg0$arg0$conj  = \f$bool$f$true$arg0$arg1$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$true$arg0$arg1$arg0$arg0  = \f$bool$f$true$arg0$arg1$arg0$arg0$conj [1:1] ;
  wire[0:0] \f$bool$f$true$arg0$arg1$arg0$arg1  = 1'd0 ;
  wire \f$bool$f$true$arg0$arg1$arg0  = \f$bool$f$true$arg0$arg1$arg0$arg0  > \f$bool$f$true$arg0$arg1$arg0$arg1  ;
  wire \f$bool$f$true$arg0$arg1  = !\f$bool$f$true$arg0$arg1$arg0  ;
  wire \f$bool$f$true$arg0  = \f$bool$f$true$arg0$arg0  && \f$bool$f$true$arg0$arg1  ;
  wire \f$bool$f$true$arg1$arg0  = 1'd1 ;
  wire[1:0] \f$bool$f$true$arg1$arg1$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$true$arg1$arg1$arg0$conj  = \f$bool$f$true$arg1$arg1$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$true$arg1$arg1$arg0  = \f$bool$f$true$arg1$arg1$arg0$conj [1:1] ;
  wire[0:0] \f$bool$f$true$arg1$arg1$arg1  = 1'd1 ;
  wire \f$bool$f$true$arg1$arg1  = \f$bool$f$true$arg1$arg1$arg0  == \f$bool$f$true$arg1$arg1$arg1  ;
  wire \f$bool$f$true$arg1  = \f$bool$f$true$arg1$arg0  && \f$bool$f$true$arg1$arg1  ;
  wire \f$bool$f$true  = \f$bool$f$true$arg0  || \f$bool$f$true$arg1  ;
  wire \f$bool$f$false$bool  = 1'd0 ;
  wire[1:0] \f$bool$f$false$true$arg0$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$false$true$arg0$arg0$conj  = \f$bool$f$false$true$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$false$true$arg0$arg0  = \f$bool$f$false$true$arg0$arg0$conj [1:1] ;
  wire[0:0] \f$bool$f$false$true$arg0$arg1  = 1'd0 ;
  wire \f$bool$f$false$true$arg0  = \f$bool$f$false$true$arg0$arg0  > \f$bool$f$false$true$arg0$arg1  ;
  wire \f$bool$f$false$true$arg1  = 1'd0 ;
  wire \f$bool$f$false$true  = \f$bool$f$false$true$arg0  || \f$bool$f$false$true$arg1  ;
  wire \f$bool$f$false$false$bool  = 1'd0 ;
  wire[1:0] \f$bool$f$false$false$true$arg0$arg0$arg0$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$false$false$true$arg0$arg0$arg0$arg0$conj  = \f$bool$f$false$false$true$arg0$arg0$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$false$false$true$arg0$arg0$arg0$arg0  = \f$bool$f$false$false$true$arg0$arg0$arg0$arg0$conj [0:0] ;
  wire[0:0] \f$bool$f$false$false$true$arg0$arg0$arg0$arg1  = 1'd0 ;
  wire \f$bool$f$false$false$true$arg0$arg0$arg0  = \f$bool$f$false$false$true$arg0$arg0$arg0$arg0  == \f$bool$f$false$false$true$arg0$arg0$arg0$arg1  ;
  wire \f$bool$f$false$false$true$arg0$arg0  = !\f$bool$f$false$false$true$arg0$arg0$arg0  ;
  wire[1:0] \f$bool$f$false$false$true$arg0$arg1$arg0$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$false$false$true$arg0$arg1$arg0$arg0$conj  = \f$bool$f$false$false$true$arg0$arg1$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$false$false$true$arg0$arg1$arg0$arg0  = \f$bool$f$false$false$true$arg0$arg1$arg0$arg0$conj [0:0] ;
  wire[0:0] \f$bool$f$false$false$true$arg0$arg1$arg0$arg1  = 1'd0 ;
  wire \f$bool$f$false$false$true$arg0$arg1$arg0  = \f$bool$f$false$false$true$arg0$arg1$arg0$arg0  > \f$bool$f$false$false$true$arg0$arg1$arg0$arg1  ;
  wire \f$bool$f$false$false$true$arg0$arg1  = !\f$bool$f$false$false$true$arg0$arg1$arg0  ;
  wire \f$bool$f$false$false$true$arg0  = \f$bool$f$false$false$true$arg0$arg0  && \f$bool$f$false$false$true$arg0$arg1  ;
  wire \f$bool$f$false$false$true$arg1$arg0  = 1'd1 ;
  wire[1:0] \f$bool$f$false$false$true$arg1$arg1$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$false$false$true$arg1$arg1$arg0$conj  = \f$bool$f$false$false$true$arg1$arg1$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$false$false$true$arg1$arg1$arg0  = \f$bool$f$false$false$true$arg1$arg1$arg0$conj [0:0] ;
  wire[0:0] \f$bool$f$false$false$true$arg1$arg1$arg1  = 1'd1 ;
  wire \f$bool$f$false$false$true$arg1$arg1  = \f$bool$f$false$false$true$arg1$arg1$arg0  == \f$bool$f$false$false$true$arg1$arg1$arg1  ;
  wire \f$bool$f$false$false$true$arg1  = \f$bool$f$false$false$true$arg1$arg0  && \f$bool$f$false$false$true$arg1$arg1  ;
  wire \f$bool$f$false$false$true  = \f$bool$f$false$false$true$arg0  || \f$bool$f$false$false$true$arg1  ;
  wire[1:0] \f$bool$f$false$false$false$arg0$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$false$false$false$arg0$arg0$conj  = \f$bool$f$false$false$false$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$false$false$false$arg0$arg0  = \f$bool$f$false$false$false$arg0$arg0$conj [0:0] ;
  wire[0:0] \f$bool$f$false$false$false$arg0$arg1  = 1'd0 ;
  wire \f$bool$f$false$false$false$arg0  = \f$bool$f$false$false$false$arg0$arg0  > \f$bool$f$false$false$false$arg0$arg1  ;
  wire \f$bool$f$false$false$false$arg1  = 1'd0 ;
  wire \f$bool$f$false$false$false  = \f$bool$f$false$false$false$arg0  || \f$bool$f$false$false$false$arg1  ;
  wire \f$bool$f$false$false  = ( \f$bool$f$false$false$bool  ? \f$bool$f$false$false$true  : \f$bool$f$false$false$false  ) ;
  wire \f$bool$f$false  = ( \f$bool$f$false$bool  ? \f$bool$f$false$true  : \f$bool$f$false$false  ) ;
  wire \f$bool$f  = ( \f$bool$f$bool  ? \f$bool$f$true  : \f$bool$f$false  ) ;
  wire \f$bool  = \f$bool$f  ;
  wire[0:0] \f$true$content  = 1'd0 ;
  wire[0:0] \f$true  = \f$true$content  ;
  wire[1:0] \f$false$bool$g0  = \i0$data  ;
  wire \f$false$bool$f$arg0$bool  = 1'd0 ;
  wire[1:0] \f$false$bool$f$arg0$true$arg0$arg0$arg0$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$true$arg0$arg0$arg0$arg0$conj  = \f$false$bool$f$arg0$true$arg0$arg0$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$true$arg0$arg0$arg0$arg0  = \f$false$bool$f$arg0$true$arg0$arg0$arg0$arg0$conj [1:1] ;
  wire[0:0] \f$false$bool$f$arg0$true$arg0$arg0$arg0$arg1  = 1'd0 ;
  wire \f$false$bool$f$arg0$true$arg0$arg0$arg0  = \f$false$bool$f$arg0$true$arg0$arg0$arg0$arg0  == \f$false$bool$f$arg0$true$arg0$arg0$arg0$arg1  ;
  wire \f$false$bool$f$arg0$true$arg0$arg0  = !\f$false$bool$f$arg0$true$arg0$arg0$arg0  ;
  wire[1:0] \f$false$bool$f$arg0$true$arg0$arg1$arg0$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$true$arg0$arg1$arg0$arg0$conj  = \f$false$bool$f$arg0$true$arg0$arg1$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$true$arg0$arg1$arg0$arg0  = \f$false$bool$f$arg0$true$arg0$arg1$arg0$arg0$conj [1:1] ;
  wire[0:0] \f$false$bool$f$arg0$true$arg0$arg1$arg0$arg1  = 1'd0 ;
  wire \f$false$bool$f$arg0$true$arg0$arg1$arg0  = \f$false$bool$f$arg0$true$arg0$arg1$arg0$arg0  > \f$false$bool$f$arg0$true$arg0$arg1$arg0$arg1  ;
  wire \f$false$bool$f$arg0$true$arg0$arg1  = !\f$false$bool$f$arg0$true$arg0$arg1$arg0  ;
  wire \f$false$bool$f$arg0$true$arg0  = \f$false$bool$f$arg0$true$arg0$arg0  && \f$false$bool$f$arg0$true$arg0$arg1  ;
  wire \f$false$bool$f$arg0$true$arg1$arg0  = 1'd1 ;
  wire[1:0] \f$false$bool$f$arg0$true$arg1$arg1$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$true$arg1$arg1$arg0$conj  = \f$false$bool$f$arg0$true$arg1$arg1$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$true$arg1$arg1$arg0  = \f$false$bool$f$arg0$true$arg1$arg1$arg0$conj [1:1] ;
  wire[0:0] \f$false$bool$f$arg0$true$arg1$arg1$arg1  = 1'd1 ;
  wire \f$false$bool$f$arg0$true$arg1$arg1  = \f$false$bool$f$arg0$true$arg1$arg1$arg0  == \f$false$bool$f$arg0$true$arg1$arg1$arg1  ;
  wire \f$false$bool$f$arg0$true$arg1  = \f$false$bool$f$arg0$true$arg1$arg0  && \f$false$bool$f$arg0$true$arg1$arg1  ;
  wire \f$false$bool$f$arg0$true  = \f$false$bool$f$arg0$true$arg0  || \f$false$bool$f$arg0$true$arg1  ;
  wire \f$false$bool$f$arg0$false$bool  = 1'd0 ;
  wire[1:0] \f$false$bool$f$arg0$false$true$arg0$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$false$true$arg0$arg0$conj  = \f$false$bool$f$arg0$false$true$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$false$true$arg0$arg0  = \f$false$bool$f$arg0$false$true$arg0$arg0$conj [1:1] ;
  wire[0:0] \f$false$bool$f$arg0$false$true$arg0$arg1  = 1'd0 ;
  wire \f$false$bool$f$arg0$false$true$arg0  = \f$false$bool$f$arg0$false$true$arg0$arg0  > \f$false$bool$f$arg0$false$true$arg0$arg1  ;
  wire \f$false$bool$f$arg0$false$true$arg1  = 1'd0 ;
  wire \f$false$bool$f$arg0$false$true  = \f$false$bool$f$arg0$false$true$arg0  || \f$false$bool$f$arg0$false$true$arg1  ;
  wire \f$false$bool$f$arg0$false$false$bool  = 1'd0 ;
  wire[1:0] \f$false$bool$f$arg0$false$false$true$arg0$arg0$arg0$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$false$false$true$arg0$arg0$arg0$arg0$conj  = \f$false$bool$f$arg0$false$false$true$arg0$arg0$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$false$false$true$arg0$arg0$arg0$arg0  = \f$false$bool$f$arg0$false$false$true$arg0$arg0$arg0$arg0$conj [0:0] ;
  wire[0:0] \f$false$bool$f$arg0$false$false$true$arg0$arg0$arg0$arg1  = 1'd0 ;
  wire \f$false$bool$f$arg0$false$false$true$arg0$arg0$arg0  = \f$false$bool$f$arg0$false$false$true$arg0$arg0$arg0$arg0  == \f$false$bool$f$arg0$false$false$true$arg0$arg0$arg0$arg1  ;
  wire \f$false$bool$f$arg0$false$false$true$arg0$arg0  = !\f$false$bool$f$arg0$false$false$true$arg0$arg0$arg0  ;
  wire[1:0] \f$false$bool$f$arg0$false$false$true$arg0$arg1$arg0$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$false$false$true$arg0$arg1$arg0$arg0$conj  = \f$false$bool$f$arg0$false$false$true$arg0$arg1$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$false$false$true$arg0$arg1$arg0$arg0  = \f$false$bool$f$arg0$false$false$true$arg0$arg1$arg0$arg0$conj [0:0] ;
  wire[0:0] \f$false$bool$f$arg0$false$false$true$arg0$arg1$arg0$arg1  = 1'd0 ;
  wire \f$false$bool$f$arg0$false$false$true$arg0$arg1$arg0  = \f$false$bool$f$arg0$false$false$true$arg0$arg1$arg0$arg0  > \f$false$bool$f$arg0$false$false$true$arg0$arg1$arg0$arg1  ;
  wire \f$false$bool$f$arg0$false$false$true$arg0$arg1  = !\f$false$bool$f$arg0$false$false$true$arg0$arg1$arg0  ;
  wire \f$false$bool$f$arg0$false$false$true$arg0  = \f$false$bool$f$arg0$false$false$true$arg0$arg0  && \f$false$bool$f$arg0$false$false$true$arg0$arg1  ;
  wire \f$false$bool$f$arg0$false$false$true$arg1$arg0  = 1'd1 ;
  wire[1:0] \f$false$bool$f$arg0$false$false$true$arg1$arg1$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$false$false$true$arg1$arg1$arg0$conj  = \f$false$bool$f$arg0$false$false$true$arg1$arg1$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$false$false$true$arg1$arg1$arg0  = \f$false$bool$f$arg0$false$false$true$arg1$arg1$arg0$conj [0:0] ;
  wire[0:0] \f$false$bool$f$arg0$false$false$true$arg1$arg1$arg1  = 1'd1 ;
  wire \f$false$bool$f$arg0$false$false$true$arg1$arg1  = \f$false$bool$f$arg0$false$false$true$arg1$arg1$arg0  == \f$false$bool$f$arg0$false$false$true$arg1$arg1$arg1  ;
  wire \f$false$bool$f$arg0$false$false$true$arg1  = \f$false$bool$f$arg0$false$false$true$arg1$arg0  && \f$false$bool$f$arg0$false$false$true$arg1$arg1  ;
  wire \f$false$bool$f$arg0$false$false$true  = \f$false$bool$f$arg0$false$false$true$arg0  || \f$false$bool$f$arg0$false$false$true$arg1  ;
  wire[1:0] \f$false$bool$f$arg0$false$false$false$arg0$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$false$false$false$arg0$arg0$conj  = \f$false$bool$f$arg0$false$false$false$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$false$false$false$arg0$arg0  = \f$false$bool$f$arg0$false$false$false$arg0$arg0$conj [0:0] ;
  wire[0:0] \f$false$bool$f$arg0$false$false$false$arg0$arg1  = 1'd0 ;
  wire \f$false$bool$f$arg0$false$false$false$arg0  = \f$false$bool$f$arg0$false$false$false$arg0$arg0  > \f$false$bool$f$arg0$false$false$false$arg0$arg1  ;
  wire \f$false$bool$f$arg0$false$false$false$arg1  = 1'd0 ;
  wire \f$false$bool$f$arg0$false$false$false  = \f$false$bool$f$arg0$false$false$false$arg0  || \f$false$bool$f$arg0$false$false$false$arg1  ;
  wire \f$false$bool$f$arg0$false$false  = ( \f$false$bool$f$arg0$false$false$bool  ? \f$false$bool$f$arg0$false$false$true  : \f$false$bool$f$arg0$false$false$false  ) ;
  wire \f$false$bool$f$arg0$false  = ( \f$false$bool$f$arg0$false$bool  ? \f$false$bool$f$arg0$false$true  : \f$false$bool$f$arg0$false$false  ) ;
  wire \f$false$bool$f$arg0  = ( \f$false$bool$f$arg0$bool  ? \f$false$bool$f$arg0$true  : \f$false$bool$f$arg0$false  ) ;
  wire \f$false$bool$f  = !\f$false$bool$f$arg0  ;
  wire \f$false$bool  = \f$false$bool$f  ;
  wire[0:0] \f$false$true$content  = 1'd1 ;
  wire[0:0] \f$false$true  = \f$false$true$content  ;
  wire[0:0] \f$false$false$content  = 1'd0 ;
  wire[0:0] \f$false$false  = \f$false$false$content  ;
  wire[0:0] \f$false  = ( \f$false$bool  ? \f$false$true  : \f$false$false  ) ;
  wire[0:0] \f  = ( \f$bool  ? \f$true  : \f$false  ) ;
  
  assign \o0  = \f  ;
endmodule

module \OFUN_1$RECEPTION_0_0_3_2_Switch2 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , output [1:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[1:0] \f  = \i0$data  ;
  
  assign \o0  = \f  ;
endmodule

module \OFUN_2$RECEPTION_0_0_3_2_Switch2 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , output [1:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[1:0] \f  = \i0$data  ;
  
  assign \o0  = \f  ;
endmodule

module \RECEPTION_1_0_2_2 (
      input \clk , input \rst , input [63:0] \t 
    , input \input$irdy , input [1:0] \input$data , output \input$trdy 
    , output \bus_outs1$irdy , output [1:0] \bus_outs1$data , input \bus_outs1$trdy 
    , output \bus_outs2$irdy , output [1:0] \bus_outs2$data , input \bus_outs2$trdy 
    , output \bus_outs3$irdy , output [1:0] \bus_outs3$data , input \bus_outs3$trdy 
    , output \bus_outs4$irdy , output [0:0] \bus_outs4$data , input \bus_outs4$trdy 
    , input \CreditCounter1$PatientSource1$unbound_irdy 
    , input [0:0] \CreditCounter1$PatientSource1$unbound_data 
    , output \CreditCounter1$PatientSource1$trdy 
    , input \CreditCounter1$Sink1$unbound_trdy 
    , output \CreditCounter1$Sink1$irdy 
    , output [0:0] \CreditCounter1$Sink1$data 
  );
  
  //
  // Channel declarations
  //
  wire \noCONS$irdy  ;
  wire [1:0] \noCONS$data  ;
  wire \noCONS$trdy  ;
  wire \toRCP$irdy  ;
  wire [1:0] \toRCP$data  ;
  wire \toRCP$trdy  ;
  wire \creditBack$irdy  ;
  wire [1:0] \creditBack$data  ;
  wire \creditBack$trdy  ;
  wire \channel1$irdy  ;
  wire [1:0] \channel1$data  ;
  wire \channel1$trdy  ;
  
  //
  // Function Channels
  //
  wire \sfunchan_0_Switch1$data  ;
  wire [1:0] \ofunchan_1_Switch1$data  ;
  wire [1:0] \ofunchan_2_Switch1$data  ;
  wire \sfunchan_0_Switch2$data  ;
  wire [1:0] \ofunchan_1_Switch2$data  ;
  wire [1:0] \ofunchan_2_Switch2$data  ;
  
  //
  // Component and Macro instantiations
  //
  \Fork2  #(
    .DATASIZE(2)
  ) \Fork1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\channel1$irdy )
    , .\i0$data (\channel1$data )
    , .\i0$trdy (\channel1$trdy )
    , .\o0$irdy (\toRCP$irdy )
    , .\o0$data (\toRCP$data )
    , .\o0$trdy (\toRCP$trdy )
    , .\o1$irdy (\creditBack$irdy )
    , .\o1$data (\creditBack$data )
    , .\o1$trdy (\creditBack$trdy )
  );
  
  \Queue  #(
    .NUM_DATA(0),
    .DATASIZE(2),
    .LENGTH(2)
  ) \Queue1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\input$irdy )
    , .\i0$data (\input$data )
    , .\i0$trdy (\input$trdy )
    , .\o0$irdy (\channel1$irdy )
    , .\o0$data (\channel1$data )
    , .\o0$trdy (\channel1$trdy )
  );
  
  \Switch2  #(
    .OUTPUTSIZE0(2),
    .OUTPUTSIZE1(2),
    .INPUTSIZE(2)
  ) \Switch1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\toRCP$irdy )
    , .\i0$data (\toRCP$data )
    , .\i0$trdy (\toRCP$trdy )
    , .\o0$irdy (\bus_outs1$irdy )
    , .\o0$data (\bus_outs1$data )
    , .\o0$trdy (\bus_outs1$trdy )
    , .\o1$irdy (\noCONS$irdy )
    , .\o1$data (\noCONS$data )
    , .\o1$trdy (\noCONS$trdy )
    , .\sel$data (\sfunchan_0_Switch1$data )
    , .\f0$data (\ofunchan_1_Switch1$data )
    , .\f1$data (\ofunchan_2_Switch1$data )
  );
  
  \SFUN_0$RECEPTION_1_0_2_2_Switch1  \sfun_0_Switch1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\toRCP$data )
    , .\o0 (\sfunchan_0_Switch1$data )
  );
  
  \OFUN_1$RECEPTION_1_0_2_2_Switch1  \ofun_1_Switch1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\toRCP$data )
    , .\o0 (\ofunchan_1_Switch1$data )
  );
  
  \OFUN_2$RECEPTION_1_0_2_2_Switch1  \ofun_2_Switch1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\toRCP$data )
    , .\o0 (\ofunchan_2_Switch1$data )
  );
  
  \Switch2  #(
    .OUTPUTSIZE0(2),
    .OUTPUTSIZE1(2),
    .INPUTSIZE(2)
  ) \Switch2  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\noCONS$irdy )
    , .\i0$data (\noCONS$data )
    , .\i0$trdy (\noCONS$trdy )
    , .\o0$irdy (\bus_outs2$irdy )
    , .\o0$data (\bus_outs2$data )
    , .\o0$trdy (\bus_outs2$trdy )
    , .\o1$irdy (\bus_outs3$irdy )
    , .\o1$data (\bus_outs3$data )
    , .\o1$trdy (\bus_outs3$trdy )
    , .\sel$data (\sfunchan_0_Switch2$data )
    , .\f0$data (\ofunchan_1_Switch2$data )
    , .\f1$data (\ofunchan_2_Switch2$data )
  );
  
  \SFUN_0$RECEPTION_1_0_2_2_Switch2  \sfun_0_Switch2  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\noCONS$data )
    , .\o0 (\sfunchan_0_Switch2$data )
  );
  
  \OFUN_1$RECEPTION_1_0_2_2_Switch2  \ofun_1_Switch2  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\noCONS$data )
    , .\o0 (\ofunchan_1_Switch2$data )
  );
  
  \OFUN_2$RECEPTION_1_0_2_2_Switch2  \ofun_2_Switch2  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\noCONS$data )
    , .\o0 (\ofunchan_2_Switch2$data )
  );
  
  \CreditCounter_2  \CreditCounter1  (
      .\clk (\clk ), .\rst (\rst ), .\t (\t )
    , .\i$irdy (\creditBack$irdy )
    , .\i$data (\creditBack$data )
    , .\i$trdy (\creditBack$trdy )
    , .\o$irdy (\bus_outs4$irdy )
    , .\o$data (\bus_outs4$data )
    , .\o$trdy (\bus_outs4$trdy )
    , .\PatientSource1$unbound_irdy (\CreditCounter1$PatientSource1$unbound_irdy )
    , .\PatientSource1$unbound_data (\CreditCounter1$PatientSource1$unbound_data )
    , .\PatientSource1$trdy (\CreditCounter1$PatientSource1$trdy )
    , .\Sink1$unbound_trdy (\CreditCounter1$Sink1$unbound_trdy )
    , .\Sink1$irdy (\CreditCounter1$Sink1$irdy )
    , .\Sink1$data (\CreditCounter1$Sink1$data )
  );
  
endmodule


//
// RECEPTION_1_0_2_2 switch functions
//
module \SFUN_0$RECEPTION_1_0_2_2_Switch1 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , output [0:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[1:0] \f$bool$g0  = \i0$data  ;
  wire[1:0] \f$bool$f$arg0$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$arg0$arg0$conj  = \f$bool$f$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$arg0$arg0  = \f$bool$f$arg0$arg0$conj [1:1] ;
  wire[0:0] \f$bool$f$arg0$arg1  = 1'd1 ;
  wire \f$bool$f$arg0  = \f$bool$f$arg0$arg0  == \f$bool$f$arg0$arg1  ;
  wire[1:0] \f$bool$f$arg1$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$arg1$arg0$conj  = \f$bool$f$arg1$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$arg1$arg0  = \f$bool$f$arg1$arg0$conj [0:0] ;
  wire[0:0] \f$bool$f$arg1$arg1  = 1'd0 ;
  wire \f$bool$f$arg1  = \f$bool$f$arg1$arg0  == \f$bool$f$arg1$arg1  ;
  wire \f$bool$f  = \f$bool$f$arg0  && \f$bool$f$arg1  ;
  wire \f$bool  = \f$bool$f  ;
  wire[0:0] \f$true$content  = 1'd0 ;
  wire[0:0] \f$true  = \f$true$content  ;
  wire[1:0] \f$false$bool$g0  = \i0$data  ;
  wire[1:0] \f$false$bool$f$arg0$arg0$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$arg0$arg0$conj  = \f$false$bool$f$arg0$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$arg0$arg0  = \f$false$bool$f$arg0$arg0$arg0$conj [1:1] ;
  wire[0:0] \f$false$bool$f$arg0$arg0$arg1  = 1'd1 ;
  wire \f$false$bool$f$arg0$arg0  = \f$false$bool$f$arg0$arg0$arg0  == \f$false$bool$f$arg0$arg0$arg1  ;
  wire[1:0] \f$false$bool$f$arg0$arg1$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$arg1$arg0$conj  = \f$false$bool$f$arg0$arg1$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$arg1$arg0  = \f$false$bool$f$arg0$arg1$arg0$conj [0:0] ;
  wire[0:0] \f$false$bool$f$arg0$arg1$arg1  = 1'd0 ;
  wire \f$false$bool$f$arg0$arg1  = \f$false$bool$f$arg0$arg1$arg0  == \f$false$bool$f$arg0$arg1$arg1  ;
  wire \f$false$bool$f$arg0  = \f$false$bool$f$arg0$arg0  && \f$false$bool$f$arg0$arg1  ;
  wire \f$false$bool$f  = !\f$false$bool$f$arg0  ;
  wire \f$false$bool  = \f$false$bool$f  ;
  wire[0:0] \f$false$true$content  = 1'd1 ;
  wire[0:0] \f$false$true  = \f$false$true$content  ;
  wire[0:0] \f$false$false$content  = 1'd0 ;
  wire[0:0] \f$false$false  = \f$false$false$content  ;
  wire[0:0] \f$false  = ( \f$false$bool  ? \f$false$true  : \f$false$false  ) ;
  wire[0:0] \f  = ( \f$bool  ? \f$true  : \f$false  ) ;
  
  assign \o0  = \f  ;
endmodule

module \OFUN_1$RECEPTION_1_0_2_2_Switch1 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , output [1:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[1:0] \f  = \i0$data  ;
  
  assign \o0  = \f  ;
endmodule

module \OFUN_2$RECEPTION_1_0_2_2_Switch1 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , output [1:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[1:0] \f  = \i0$data  ;
  
  assign \o0  = \f  ;
endmodule

module \SFUN_0$RECEPTION_1_0_2_2_Switch2 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , output [0:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[1:0] \f$bool$g0  = \i0$data  ;
  wire \f$bool$f$bool  = 1'd0 ;
  wire[1:0] \f$bool$f$true$arg0$arg0$arg0$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$true$arg0$arg0$arg0$arg0$conj  = \f$bool$f$true$arg0$arg0$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$true$arg0$arg0$arg0$arg0  = \f$bool$f$true$arg0$arg0$arg0$arg0$conj [1:1] ;
  wire[0:0] \f$bool$f$true$arg0$arg0$arg0$arg1  = 1'd1 ;
  wire \f$bool$f$true$arg0$arg0$arg0  = \f$bool$f$true$arg0$arg0$arg0$arg0  == \f$bool$f$true$arg0$arg0$arg0$arg1  ;
  wire \f$bool$f$true$arg0$arg0  = !\f$bool$f$true$arg0$arg0$arg0  ;
  wire[1:0] \f$bool$f$true$arg0$arg1$arg0$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$true$arg0$arg1$arg0$arg0$conj  = \f$bool$f$true$arg0$arg1$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$true$arg0$arg1$arg0$arg0  = \f$bool$f$true$arg0$arg1$arg0$arg0$conj [1:1] ;
  wire[0:0] \f$bool$f$true$arg0$arg1$arg0$arg1  = 1'd1 ;
  wire \f$bool$f$true$arg0$arg1$arg0  = \f$bool$f$true$arg0$arg1$arg0$arg0  > \f$bool$f$true$arg0$arg1$arg0$arg1  ;
  wire \f$bool$f$true$arg0$arg1  = !\f$bool$f$true$arg0$arg1$arg0  ;
  wire \f$bool$f$true$arg0  = \f$bool$f$true$arg0$arg0  && \f$bool$f$true$arg0$arg1  ;
  wire \f$bool$f$true$arg1  = 1'd0 ;
  wire \f$bool$f$true  = \f$bool$f$true$arg0  || \f$bool$f$true$arg1  ;
  wire \f$bool$f$false$bool  = 1'd0 ;
  wire[1:0] \f$bool$f$false$true$arg0$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$false$true$arg0$arg0$conj  = \f$bool$f$false$true$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$false$true$arg0$arg0  = \f$bool$f$false$true$arg0$arg0$conj [1:1] ;
  wire[0:0] \f$bool$f$false$true$arg0$arg1  = 1'd1 ;
  wire \f$bool$f$false$true$arg0  = \f$bool$f$false$true$arg0$arg0  > \f$bool$f$false$true$arg0$arg1  ;
  wire \f$bool$f$false$true$arg1$arg0  = 1'd1 ;
  wire[1:0] \f$bool$f$false$true$arg1$arg1$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$false$true$arg1$arg1$arg0$conj  = \f$bool$f$false$true$arg1$arg1$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$false$true$arg1$arg1$arg0  = \f$bool$f$false$true$arg1$arg1$arg0$conj [1:1] ;
  wire[0:0] \f$bool$f$false$true$arg1$arg1$arg1  = 1'd0 ;
  wire \f$bool$f$false$true$arg1$arg1  = \f$bool$f$false$true$arg1$arg1$arg0  == \f$bool$f$false$true$arg1$arg1$arg1  ;
  wire \f$bool$f$false$true$arg1  = \f$bool$f$false$true$arg1$arg0  && \f$bool$f$false$true$arg1$arg1  ;
  wire \f$bool$f$false$true  = \f$bool$f$false$true$arg0  || \f$bool$f$false$true$arg1  ;
  wire \f$bool$f$false$false$bool  = 1'd1 ;
  wire[1:0] \f$bool$f$false$false$true$arg0$arg0$arg0$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$false$false$true$arg0$arg0$arg0$arg0$conj  = \f$bool$f$false$false$true$arg0$arg0$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$false$false$true$arg0$arg0$arg0$arg0  = \f$bool$f$false$false$true$arg0$arg0$arg0$arg0$conj [0:0] ;
  wire[0:0] \f$bool$f$false$false$true$arg0$arg0$arg0$arg1  = 1'd0 ;
  wire \f$bool$f$false$false$true$arg0$arg0$arg0  = \f$bool$f$false$false$true$arg0$arg0$arg0$arg0  == \f$bool$f$false$false$true$arg0$arg0$arg0$arg1  ;
  wire \f$bool$f$false$false$true$arg0$arg0  = !\f$bool$f$false$false$true$arg0$arg0$arg0  ;
  wire[1:0] \f$bool$f$false$false$true$arg0$arg1$arg0$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$false$false$true$arg0$arg1$arg0$arg0$conj  = \f$bool$f$false$false$true$arg0$arg1$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$false$false$true$arg0$arg1$arg0$arg0  = \f$bool$f$false$false$true$arg0$arg1$arg0$arg0$conj [0:0] ;
  wire[0:0] \f$bool$f$false$false$true$arg0$arg1$arg0$arg1  = 1'd0 ;
  wire \f$bool$f$false$false$true$arg0$arg1$arg0  = \f$bool$f$false$false$true$arg0$arg1$arg0$arg0  > \f$bool$f$false$false$true$arg0$arg1$arg0$arg1  ;
  wire \f$bool$f$false$false$true$arg0$arg1  = !\f$bool$f$false$false$true$arg0$arg1$arg0  ;
  wire \f$bool$f$false$false$true$arg0  = \f$bool$f$false$false$true$arg0$arg0  && \f$bool$f$false$false$true$arg0$arg1  ;
  wire \f$bool$f$false$false$true$arg1$arg0  = 1'd1 ;
  wire[1:0] \f$bool$f$false$false$true$arg1$arg1$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$false$false$true$arg1$arg1$arg0$conj  = \f$bool$f$false$false$true$arg1$arg1$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$false$false$true$arg1$arg1$arg0  = \f$bool$f$false$false$true$arg1$arg1$arg0$conj [0:0] ;
  wire[0:0] \f$bool$f$false$false$true$arg1$arg1$arg1  = 1'd1 ;
  wire \f$bool$f$false$false$true$arg1$arg1  = \f$bool$f$false$false$true$arg1$arg1$arg0  == \f$bool$f$false$false$true$arg1$arg1$arg1  ;
  wire \f$bool$f$false$false$true$arg1  = \f$bool$f$false$false$true$arg1$arg0  && \f$bool$f$false$false$true$arg1$arg1  ;
  wire \f$bool$f$false$false$true  = \f$bool$f$false$false$true$arg0  || \f$bool$f$false$false$true$arg1  ;
  wire[1:0] \f$bool$f$false$false$false$arg0$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$false$false$false$arg0$arg0$conj  = \f$bool$f$false$false$false$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$false$false$false$arg0$arg0  = \f$bool$f$false$false$false$arg0$arg0$conj [0:0] ;
  wire[0:0] \f$bool$f$false$false$false$arg0$arg1  = 1'd0 ;
  wire \f$bool$f$false$false$false$arg0  = \f$bool$f$false$false$false$arg0$arg0  > \f$bool$f$false$false$false$arg0$arg1  ;
  wire \f$bool$f$false$false$false$arg1  = 1'd0 ;
  wire \f$bool$f$false$false$false  = \f$bool$f$false$false$false$arg0  || \f$bool$f$false$false$false$arg1  ;
  wire \f$bool$f$false$false  = ( \f$bool$f$false$false$bool  ? \f$bool$f$false$false$true  : \f$bool$f$false$false$false  ) ;
  wire \f$bool$f$false  = ( \f$bool$f$false$bool  ? \f$bool$f$false$true  : \f$bool$f$false$false  ) ;
  wire \f$bool$f  = ( \f$bool$f$bool  ? \f$bool$f$true  : \f$bool$f$false  ) ;
  wire \f$bool  = \f$bool$f  ;
  wire[0:0] \f$true$content  = 1'd0 ;
  wire[0:0] \f$true  = \f$true$content  ;
  wire[1:0] \f$false$bool$g0  = \i0$data  ;
  wire \f$false$bool$f$arg0$bool  = 1'd0 ;
  wire[1:0] \f$false$bool$f$arg0$true$arg0$arg0$arg0$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$true$arg0$arg0$arg0$arg0$conj  = \f$false$bool$f$arg0$true$arg0$arg0$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$true$arg0$arg0$arg0$arg0  = \f$false$bool$f$arg0$true$arg0$arg0$arg0$arg0$conj [1:1] ;
  wire[0:0] \f$false$bool$f$arg0$true$arg0$arg0$arg0$arg1  = 1'd1 ;
  wire \f$false$bool$f$arg0$true$arg0$arg0$arg0  = \f$false$bool$f$arg0$true$arg0$arg0$arg0$arg0  == \f$false$bool$f$arg0$true$arg0$arg0$arg0$arg1  ;
  wire \f$false$bool$f$arg0$true$arg0$arg0  = !\f$false$bool$f$arg0$true$arg0$arg0$arg0  ;
  wire[1:0] \f$false$bool$f$arg0$true$arg0$arg1$arg0$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$true$arg0$arg1$arg0$arg0$conj  = \f$false$bool$f$arg0$true$arg0$arg1$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$true$arg0$arg1$arg0$arg0  = \f$false$bool$f$arg0$true$arg0$arg1$arg0$arg0$conj [1:1] ;
  wire[0:0] \f$false$bool$f$arg0$true$arg0$arg1$arg0$arg1  = 1'd1 ;
  wire \f$false$bool$f$arg0$true$arg0$arg1$arg0  = \f$false$bool$f$arg0$true$arg0$arg1$arg0$arg0  > \f$false$bool$f$arg0$true$arg0$arg1$arg0$arg1  ;
  wire \f$false$bool$f$arg0$true$arg0$arg1  = !\f$false$bool$f$arg0$true$arg0$arg1$arg0  ;
  wire \f$false$bool$f$arg0$true$arg0  = \f$false$bool$f$arg0$true$arg0$arg0  && \f$false$bool$f$arg0$true$arg0$arg1  ;
  wire \f$false$bool$f$arg0$true$arg1  = 1'd0 ;
  wire \f$false$bool$f$arg0$true  = \f$false$bool$f$arg0$true$arg0  || \f$false$bool$f$arg0$true$arg1  ;
  wire \f$false$bool$f$arg0$false$bool  = 1'd0 ;
  wire[1:0] \f$false$bool$f$arg0$false$true$arg0$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$false$true$arg0$arg0$conj  = \f$false$bool$f$arg0$false$true$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$false$true$arg0$arg0  = \f$false$bool$f$arg0$false$true$arg0$arg0$conj [1:1] ;
  wire[0:0] \f$false$bool$f$arg0$false$true$arg0$arg1  = 1'd1 ;
  wire \f$false$bool$f$arg0$false$true$arg0  = \f$false$bool$f$arg0$false$true$arg0$arg0  > \f$false$bool$f$arg0$false$true$arg0$arg1  ;
  wire \f$false$bool$f$arg0$false$true$arg1$arg0  = 1'd1 ;
  wire[1:0] \f$false$bool$f$arg0$false$true$arg1$arg1$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$false$true$arg1$arg1$arg0$conj  = \f$false$bool$f$arg0$false$true$arg1$arg1$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$false$true$arg1$arg1$arg0  = \f$false$bool$f$arg0$false$true$arg1$arg1$arg0$conj [1:1] ;
  wire[0:0] \f$false$bool$f$arg0$false$true$arg1$arg1$arg1  = 1'd0 ;
  wire \f$false$bool$f$arg0$false$true$arg1$arg1  = \f$false$bool$f$arg0$false$true$arg1$arg1$arg0  == \f$false$bool$f$arg0$false$true$arg1$arg1$arg1  ;
  wire \f$false$bool$f$arg0$false$true$arg1  = \f$false$bool$f$arg0$false$true$arg1$arg0  && \f$false$bool$f$arg0$false$true$arg1$arg1  ;
  wire \f$false$bool$f$arg0$false$true  = \f$false$bool$f$arg0$false$true$arg0  || \f$false$bool$f$arg0$false$true$arg1  ;
  wire \f$false$bool$f$arg0$false$false$bool  = 1'd1 ;
  wire[1:0] \f$false$bool$f$arg0$false$false$true$arg0$arg0$arg0$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$false$false$true$arg0$arg0$arg0$arg0$conj  = \f$false$bool$f$arg0$false$false$true$arg0$arg0$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$false$false$true$arg0$arg0$arg0$arg0  = \f$false$bool$f$arg0$false$false$true$arg0$arg0$arg0$arg0$conj [0:0] ;
  wire[0:0] \f$false$bool$f$arg0$false$false$true$arg0$arg0$arg0$arg1  = 1'd0 ;
  wire \f$false$bool$f$arg0$false$false$true$arg0$arg0$arg0  = \f$false$bool$f$arg0$false$false$true$arg0$arg0$arg0$arg0  == \f$false$bool$f$arg0$false$false$true$arg0$arg0$arg0$arg1  ;
  wire \f$false$bool$f$arg0$false$false$true$arg0$arg0  = !\f$false$bool$f$arg0$false$false$true$arg0$arg0$arg0  ;
  wire[1:0] \f$false$bool$f$arg0$false$false$true$arg0$arg1$arg0$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$false$false$true$arg0$arg1$arg0$arg0$conj  = \f$false$bool$f$arg0$false$false$true$arg0$arg1$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$false$false$true$arg0$arg1$arg0$arg0  = \f$false$bool$f$arg0$false$false$true$arg0$arg1$arg0$arg0$conj [0:0] ;
  wire[0:0] \f$false$bool$f$arg0$false$false$true$arg0$arg1$arg0$arg1  = 1'd0 ;
  wire \f$false$bool$f$arg0$false$false$true$arg0$arg1$arg0  = \f$false$bool$f$arg0$false$false$true$arg0$arg1$arg0$arg0  > \f$false$bool$f$arg0$false$false$true$arg0$arg1$arg0$arg1  ;
  wire \f$false$bool$f$arg0$false$false$true$arg0$arg1  = !\f$false$bool$f$arg0$false$false$true$arg0$arg1$arg0  ;
  wire \f$false$bool$f$arg0$false$false$true$arg0  = \f$false$bool$f$arg0$false$false$true$arg0$arg0  && \f$false$bool$f$arg0$false$false$true$arg0$arg1  ;
  wire \f$false$bool$f$arg0$false$false$true$arg1$arg0  = 1'd1 ;
  wire[1:0] \f$false$bool$f$arg0$false$false$true$arg1$arg1$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$false$false$true$arg1$arg1$arg0$conj  = \f$false$bool$f$arg0$false$false$true$arg1$arg1$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$false$false$true$arg1$arg1$arg0  = \f$false$bool$f$arg0$false$false$true$arg1$arg1$arg0$conj [0:0] ;
  wire[0:0] \f$false$bool$f$arg0$false$false$true$arg1$arg1$arg1  = 1'd1 ;
  wire \f$false$bool$f$arg0$false$false$true$arg1$arg1  = \f$false$bool$f$arg0$false$false$true$arg1$arg1$arg0  == \f$false$bool$f$arg0$false$false$true$arg1$arg1$arg1  ;
  wire \f$false$bool$f$arg0$false$false$true$arg1  = \f$false$bool$f$arg0$false$false$true$arg1$arg0  && \f$false$bool$f$arg0$false$false$true$arg1$arg1  ;
  wire \f$false$bool$f$arg0$false$false$true  = \f$false$bool$f$arg0$false$false$true$arg0  || \f$false$bool$f$arg0$false$false$true$arg1  ;
  wire[1:0] \f$false$bool$f$arg0$false$false$false$arg0$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$false$false$false$arg0$arg0$conj  = \f$false$bool$f$arg0$false$false$false$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$false$false$false$arg0$arg0  = \f$false$bool$f$arg0$false$false$false$arg0$arg0$conj [0:0] ;
  wire[0:0] \f$false$bool$f$arg0$false$false$false$arg0$arg1  = 1'd0 ;
  wire \f$false$bool$f$arg0$false$false$false$arg0  = \f$false$bool$f$arg0$false$false$false$arg0$arg0  > \f$false$bool$f$arg0$false$false$false$arg0$arg1  ;
  wire \f$false$bool$f$arg0$false$false$false$arg1  = 1'd0 ;
  wire \f$false$bool$f$arg0$false$false$false  = \f$false$bool$f$arg0$false$false$false$arg0  || \f$false$bool$f$arg0$false$false$false$arg1  ;
  wire \f$false$bool$f$arg0$false$false  = ( \f$false$bool$f$arg0$false$false$bool  ? \f$false$bool$f$arg0$false$false$true  : \f$false$bool$f$arg0$false$false$false  ) ;
  wire \f$false$bool$f$arg0$false  = ( \f$false$bool$f$arg0$false$bool  ? \f$false$bool$f$arg0$false$true  : \f$false$bool$f$arg0$false$false  ) ;
  wire \f$false$bool$f$arg0  = ( \f$false$bool$f$arg0$bool  ? \f$false$bool$f$arg0$true  : \f$false$bool$f$arg0$false  ) ;
  wire \f$false$bool$f  = !\f$false$bool$f$arg0  ;
  wire \f$false$bool  = \f$false$bool$f  ;
  wire[0:0] \f$false$true$content  = 1'd1 ;
  wire[0:0] \f$false$true  = \f$false$true$content  ;
  wire[0:0] \f$false$false$content  = 1'd0 ;
  wire[0:0] \f$false$false  = \f$false$false$content  ;
  wire[0:0] \f$false  = ( \f$false$bool  ? \f$false$true  : \f$false$false  ) ;
  wire[0:0] \f  = ( \f$bool  ? \f$true  : \f$false  ) ;
  
  assign \o0  = \f  ;
endmodule

module \OFUN_1$RECEPTION_1_0_2_2_Switch2 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , output [1:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[1:0] \f  = \i0$data  ;
  
  assign \o0  = \f  ;
endmodule

module \OFUN_2$RECEPTION_1_0_2_2_Switch2 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , output [1:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[1:0] \f  = \i0$data  ;
  
  assign \o0  = \f  ;
endmodule

module \DFIFO_2$type0 (
      input \clk , input \rst 
    , input \bus_ins1$irdy , input [1:0] \bus_ins1$data , output \bus_ins1$trdy 
    , input \bus_ins2$irdy , input [1:0] \bus_ins2$data , output \bus_ins2$trdy 
    , output \bus_outs1$irdy , output [1:0] \bus_outs1$data , input \bus_outs1$trdy 
    , output \bus_outs2$irdy , output [1:0] \bus_outs2$data , input \bus_outs2$trdy 
  );
  
  //
  // Channel declarations
  //
  wire \toQueueUp1$irdy  ;
  wire [1:0] \toQueueUp1$data  ;
  wire \toQueueUp1$trdy  ;
  wire \toQueueDown1$irdy  ;
  wire [1:0] \toQueueDown1$data  ;
  wire \toQueueDown1$trdy  ;
  wire \channel1$irdy  ;
  wire [1:0] \channel1$data  ;
  wire \channel1$trdy  ;
  wire \toQueueUp2$irdy  ;
  wire [1:0] \toQueueUp2$data  ;
  wire \toQueueUp2$trdy  ;
  wire \toQueueDown2$irdy  ;
  wire [1:0] \toQueueDown2$data  ;
  wire \toQueueDown2$trdy  ;
  wire \channel2$irdy  ;
  wire [1:0] \channel2$data  ;
  wire \channel2$trdy  ;
  wire \in0up$irdy  ;
  wire [1:0] \in0up$data  ;
  wire \in0up$trdy  ;
  wire \in0down$irdy  ;
  wire [1:0] \in0down$data  ;
  wire \in0down$trdy  ;
  wire \channel6$irdy  ;
  wire [1:0] \channel6$data  ;
  wire \channel6$trdy  ;
  wire \channel5$irdy  ;
  wire [1:0] \channel5$data  ;
  wire \channel5$trdy  ;
  wire \channel3$irdy  ;
  wire [1:0] \channel3$data  ;
  wire \channel3$trdy  ;
  wire \channel4$irdy  ;
  wire [1:0] \channel4$data  ;
  wire \channel4$trdy  ;
  wire \in1up$irdy  ;
  wire [1:0] \in1up$data  ;
  wire \in1up$trdy  ;
  wire \in1down$irdy  ;
  wire [1:0] \in1down$data  ;
  wire \in1down$trdy  ;
  wire \channel10$irdy  ;
  wire [1:0] \channel10$data  ;
  wire \channel10$trdy  ;
  wire \channel9$irdy  ;
  wire [1:0] \channel9$data  ;
  wire \channel9$trdy  ;
  wire \channel7$irdy  ;
  wire [1:0] \channel7$data  ;
  wire \channel7$trdy  ;
  wire \channel8$irdy  ;
  wire [1:0] \channel8$data  ;
  wire \channel8$trdy  ;
  wire \channel11$irdy  ;
  wire [1:0] \channel11$data  ;
  wire \channel11$trdy  ;
  wire \channel12$irdy  ;
  wire [1:0] \channel12$data  ;
  wire \channel12$trdy  ;
  wire \channel13$irdy  ;
  wire [1:0] \channel13$data  ;
  wire \channel13$trdy  ;
  wire \channel14$irdy  ;
  wire [1:0] \channel14$data  ;
  wire \channel14$trdy  ;
  
  //
  // Function Channels
  //
  wire [1:0] \ofunchan_0_Merge1$data  ;
  wire \sel_Merge1  ;
  wire [1:0] \ofunchan_0_Merge2$data  ;
  wire \sel_Merge2  ;
  wire [1:0] \ofunchan_0_Merge3$data  ;
  wire \sel_Merge3  ;
  wire [1:0] \ofunchan_0_Merge4$data  ;
  wire \sel_Merge4  ;
  
  //
  // Component and Macro instantiations
  //
  \LoadBalancer2  #(
    .DATASIZE(2)
  ) \LoadBalancer1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\channel1$irdy )
    , .\i0$data (\channel1$data )
    , .\i0$trdy (\channel1$trdy )
    , .\o0$irdy (\toQueueUp1$irdy )
    , .\o0$data (\toQueueUp1$data )
    , .\o0$trdy (\toQueueUp1$trdy )
    , .\o1$irdy (\toQueueDown1$irdy )
    , .\o1$data (\toQueueDown1$data )
    , .\o1$trdy (\toQueueDown1$trdy )
  );
  
  \LoadBalancer2  #(
    .DATASIZE(2)
  ) \LoadBalancer2  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\channel2$irdy )
    , .\i0$data (\channel2$data )
    , .\i0$trdy (\channel2$trdy )
    , .\o0$irdy (\toQueueUp2$irdy )
    , .\o0$data (\toQueueUp2$data )
    , .\o0$trdy (\toQueueUp2$trdy )
    , .\o1$irdy (\toQueueDown2$irdy )
    , .\o1$data (\toQueueDown2$data )
    , .\o1$trdy (\toQueueDown2$trdy )
  );
  
  \LoadBalancer2  #(
    .DATASIZE(2)
  ) \LoadBalancer3  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\channel6$irdy )
    , .\i0$data (\channel6$data )
    , .\i0$trdy (\channel6$trdy )
    , .\o0$irdy (\in0up$irdy )
    , .\o0$data (\in0up$data )
    , .\o0$trdy (\in0up$trdy )
    , .\o1$irdy (\in0down$irdy )
    , .\o1$data (\in0down$data )
    , .\o1$trdy (\in0down$trdy )
  );
  
  \Queue  #(
    .NUM_DATA(0),
    .DATASIZE(2),
    .LENGTH(2)
  ) \Queue1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\channel5$irdy )
    , .\i0$data (\channel5$data )
    , .\i0$trdy (\channel5$trdy )
    , .\o0$irdy (\channel6$irdy )
    , .\o0$data (\channel6$data )
    , .\o0$trdy (\channel6$trdy )
  );
  
  \Merge2  #(
    .INPUTSIZE1(2),
    .OUTPUTSIZE(2),
    .INPUTSIZE0(2)
  ) \Merge1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\channel3$irdy )
    , .\i0$data (\channel3$data )
    , .\i0$trdy (\channel3$trdy )
    , .\i1$irdy (\channel4$irdy )
    , .\i1$data (\channel4$data )
    , .\i1$trdy (\channel4$trdy )
    , .\o0$irdy (\channel5$irdy )
    , .\o0$data (\channel5$data )
    , .\o0$trdy (\channel5$trdy )
    , .\f$data (\ofunchan_0_Merge1$data )
    , .\sel (\sel_Merge1 )
  );
  
  \OFUN_0$DFIFO_2_Merge1  \ofun_0_Merge1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\channel3$data )
    , .\i1$data (\channel4$data )
    , .\sel (\sel_Merge1 )
    , .\o0 (\ofunchan_0_Merge1$data )
  );
  
  \LoadBalancer2  #(
    .DATASIZE(2)
  ) \LoadBalancer4  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\channel10$irdy )
    , .\i0$data (\channel10$data )
    , .\i0$trdy (\channel10$trdy )
    , .\o0$irdy (\in1up$irdy )
    , .\o0$data (\in1up$data )
    , .\o0$trdy (\in1up$trdy )
    , .\o1$irdy (\in1down$irdy )
    , .\o1$data (\in1down$data )
    , .\o1$trdy (\in1down$trdy )
  );
  
  \Queue  #(
    .NUM_DATA(0),
    .DATASIZE(2),
    .LENGTH(2)
  ) \Queue2  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\channel9$irdy )
    , .\i0$data (\channel9$data )
    , .\i0$trdy (\channel9$trdy )
    , .\o0$irdy (\channel10$irdy )
    , .\o0$data (\channel10$data )
    , .\o0$trdy (\channel10$trdy )
  );
  
  \Merge2  #(
    .INPUTSIZE1(2),
    .OUTPUTSIZE(2),
    .INPUTSIZE0(2)
  ) \Merge2  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\channel7$irdy )
    , .\i0$data (\channel7$data )
    , .\i0$trdy (\channel7$trdy )
    , .\i1$irdy (\channel8$irdy )
    , .\i1$data (\channel8$data )
    , .\i1$trdy (\channel8$trdy )
    , .\o0$irdy (\channel9$irdy )
    , .\o0$data (\channel9$data )
    , .\o0$trdy (\channel9$trdy )
    , .\f$data (\ofunchan_0_Merge2$data )
    , .\sel (\sel_Merge2 )
  );
  
  \OFUN_0$DFIFO_2_Merge2  \ofun_0_Merge2  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\channel7$data )
    , .\i1$data (\channel8$data )
    , .\sel (\sel_Merge2 )
    , .\o0 (\ofunchan_0_Merge2$data )
  );
  
  \Merge2  #(
    .INPUTSIZE1(2),
    .OUTPUTSIZE(2),
    .INPUTSIZE0(2)
  ) \Merge3  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\channel11$irdy )
    , .\i0$data (\channel11$data )
    , .\i0$trdy (\channel11$trdy )
    , .\i1$irdy (\channel12$irdy )
    , .\i1$data (\channel12$data )
    , .\i1$trdy (\channel12$trdy )
    , .\o0$irdy (\bus_outs1$irdy )
    , .\o0$data (\bus_outs1$data )
    , .\o0$trdy (\bus_outs1$trdy )
    , .\f$data (\ofunchan_0_Merge3$data )
    , .\sel (\sel_Merge3 )
  );
  
  \OFUN_0$DFIFO_2_Merge3  \ofun_0_Merge3  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\channel11$data )
    , .\i1$data (\channel12$data )
    , .\sel (\sel_Merge3 )
    , .\o0 (\ofunchan_0_Merge3$data )
  );
  
  \Merge2  #(
    .INPUTSIZE1(2),
    .OUTPUTSIZE(2),
    .INPUTSIZE0(2)
  ) \Merge4  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\channel13$irdy )
    , .\i0$data (\channel13$data )
    , .\i0$trdy (\channel13$trdy )
    , .\i1$irdy (\channel14$irdy )
    , .\i1$data (\channel14$data )
    , .\i1$trdy (\channel14$trdy )
    , .\o0$irdy (\bus_outs2$irdy )
    , .\o0$data (\bus_outs2$data )
    , .\o0$trdy (\bus_outs2$trdy )
    , .\f$data (\ofunchan_0_Merge4$data )
    , .\sel (\sel_Merge4 )
  );
  
  \OFUN_0$DFIFO_2_Merge4  \ofun_0_Merge4  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\channel13$data )
    , .\i1$data (\channel14$data )
    , .\sel (\sel_Merge4 )
    , .\o0 (\ofunchan_0_Merge4$data )
  );
  
  \Latch$type1  \Latch1  (
      .\clk (\clk ), .\rst (\rst )
    , .\input$irdy (\bus_ins1$irdy )
    , .\input$data (\bus_ins1$data )
    , .\input$trdy (\bus_ins1$trdy )
    , .\output$irdy (\channel1$irdy )
    , .\output$data (\channel1$data )
    , .\output$trdy (\channel1$trdy )
  );
  
  \Latch$type4  \Latch2  (
      .\clk (\clk ), .\rst (\rst )
    , .\input$irdy (\bus_ins2$irdy )
    , .\input$data (\bus_ins2$data )
    , .\input$trdy (\bus_ins2$trdy )
    , .\output$irdy (\channel2$irdy )
    , .\output$data (\channel2$data )
    , .\output$trdy (\channel2$trdy )
  );
  
  \Latch$type1  \Latch3  (
      .\clk (\clk ), .\rst (\rst )
    , .\input$irdy (\toQueueUp1$irdy )
    , .\input$data (\toQueueUp1$data )
    , .\input$trdy (\toQueueUp1$trdy )
    , .\output$irdy (\channel3$irdy )
    , .\output$data (\channel3$data )
    , .\output$trdy (\channel3$trdy )
  );
  
  \Latch$type4  \Latch4  (
      .\clk (\clk ), .\rst (\rst )
    , .\input$irdy (\toQueueUp2$irdy )
    , .\input$data (\toQueueUp2$data )
    , .\input$trdy (\toQueueUp2$trdy )
    , .\output$irdy (\channel4$irdy )
    , .\output$data (\channel4$data )
    , .\output$trdy (\channel4$trdy )
  );
  
  \Latch$type1  \Latch5  (
      .\clk (\clk ), .\rst (\rst )
    , .\input$irdy (\toQueueDown1$irdy )
    , .\input$data (\toQueueDown1$data )
    , .\input$trdy (\toQueueDown1$trdy )
    , .\output$irdy (\channel7$irdy )
    , .\output$data (\channel7$data )
    , .\output$trdy (\channel7$trdy )
  );
  
  \Latch$type4  \Latch6  (
      .\clk (\clk ), .\rst (\rst )
    , .\input$irdy (\toQueueDown2$irdy )
    , .\input$data (\toQueueDown2$data )
    , .\input$trdy (\toQueueDown2$trdy )
    , .\output$irdy (\channel8$irdy )
    , .\output$data (\channel8$data )
    , .\output$trdy (\channel8$trdy )
  );
  
  \Latch$type4  \Latch7  (
      .\clk (\clk ), .\rst (\rst )
    , .\input$irdy (\in0up$irdy )
    , .\input$data (\in0up$data )
    , .\input$trdy (\in0up$trdy )
    , .\output$irdy (\channel11$irdy )
    , .\output$data (\channel11$data )
    , .\output$trdy (\channel11$trdy )
  );
  
  \Latch$type4  \Latch8  (
      .\clk (\clk ), .\rst (\rst )
    , .\input$irdy (\in1up$irdy )
    , .\input$data (\in1up$data )
    , .\input$trdy (\in1up$trdy )
    , .\output$irdy (\channel12$irdy )
    , .\output$data (\channel12$data )
    , .\output$trdy (\channel12$trdy )
  );
  
  \Latch$type4  \Latch9  (
      .\clk (\clk ), .\rst (\rst )
    , .\input$irdy (\in0down$irdy )
    , .\input$data (\in0down$data )
    , .\input$trdy (\in0down$trdy )
    , .\output$irdy (\channel13$irdy )
    , .\output$data (\channel13$data )
    , .\output$trdy (\channel13$trdy )
  );
  
  \Latch$type4  \Latch10  (
      .\clk (\clk ), .\rst (\rst )
    , .\input$irdy (\in1down$irdy )
    , .\input$data (\in1down$data )
    , .\input$trdy (\in1down$trdy )
    , .\output$irdy (\channel14$irdy )
    , .\output$data (\channel14$data )
    , .\output$trdy (\channel14$trdy )
  );
  
endmodule


//
// DFIFO_2 switch functions
//
module \OFUN_0$DFIFO_2_Merge1 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , input [1:0] \i1$data 
    , input \sel 
    , output [1:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[0:0] \f$bool$arg0$disj  = \sel  ;
  wire[0:0] \f$bool$arg0  = \f$bool$arg0$disj [0:0] ;
  wire[0:0] \f$bool$arg1  = 1'd0 ;
  wire \f$bool  = \f$bool$arg0  == \f$bool$arg1  ;
  wire[1:0] \f$true  = \i0$data  ;
  wire[0:0] \f$false$bool$arg0$disj  = \sel  ;
  wire[0:0] \f$false$bool$arg0  = \f$false$bool$arg0$disj [0:0] ;
  wire[0:0] \f$false$bool$arg1  = 1'd1 ;
  wire \f$false$bool  = \f$false$bool$arg0  == \f$false$bool$arg1  ;
  wire[1:0] \f$false$true  = \i1$data  ;
  wire[1:0] \f$false$false  = \i0$data  ;
  wire[1:0] \f$false  = ( \f$false$bool  ? \f$false$true  : \f$false$false  ) ;
  wire[1:0] \f  = ( \f$bool  ? \f$true  : \f$false  ) ;
  
  assign \o0  = \f  ;
endmodule

module \OFUN_0$DFIFO_2_Merge2 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , input [1:0] \i1$data 
    , input \sel 
    , output [1:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[0:0] \f$bool$arg0$disj  = \sel  ;
  wire[0:0] \f$bool$arg0  = \f$bool$arg0$disj [0:0] ;
  wire[0:0] \f$bool$arg1  = 1'd0 ;
  wire \f$bool  = \f$bool$arg0  == \f$bool$arg1  ;
  wire[1:0] \f$true  = \i0$data  ;
  wire[0:0] \f$false$bool$arg0$disj  = \sel  ;
  wire[0:0] \f$false$bool$arg0  = \f$false$bool$arg0$disj [0:0] ;
  wire[0:0] \f$false$bool$arg1  = 1'd1 ;
  wire \f$false$bool  = \f$false$bool$arg0  == \f$false$bool$arg1  ;
  wire[1:0] \f$false$true  = \i1$data  ;
  wire[1:0] \f$false$false  = \i0$data  ;
  wire[1:0] \f$false  = ( \f$false$bool  ? \f$false$true  : \f$false$false  ) ;
  wire[1:0] \f  = ( \f$bool  ? \f$true  : \f$false  ) ;
  
  assign \o0  = \f  ;
endmodule

module \OFUN_0$DFIFO_2_Merge3 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , input [1:0] \i1$data 
    , input \sel 
    , output [1:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[0:0] \f$bool$arg0$disj  = \sel  ;
  wire[0:0] \f$bool$arg0  = \f$bool$arg0$disj [0:0] ;
  wire[0:0] \f$bool$arg1  = 1'd0 ;
  wire \f$bool  = \f$bool$arg0  == \f$bool$arg1  ;
  wire[1:0] \f$true  = \i0$data  ;
  wire[0:0] \f$false$bool$arg0$disj  = \sel  ;
  wire[0:0] \f$false$bool$arg0  = \f$false$bool$arg0$disj [0:0] ;
  wire[0:0] \f$false$bool$arg1  = 1'd1 ;
  wire \f$false$bool  = \f$false$bool$arg0  == \f$false$bool$arg1  ;
  wire[1:0] \f$false$true  = \i1$data  ;
  wire[1:0] \f$false$false  = \i0$data  ;
  wire[1:0] \f$false  = ( \f$false$bool  ? \f$false$true  : \f$false$false  ) ;
  wire[1:0] \f  = ( \f$bool  ? \f$true  : \f$false  ) ;
  
  assign \o0  = \f  ;
endmodule

module \OFUN_0$DFIFO_2_Merge4 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , input [1:0] \i1$data 
    , input \sel 
    , output [1:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[0:0] \f$bool$arg0$disj  = \sel  ;
  wire[0:0] \f$bool$arg0  = \f$bool$arg0$disj [0:0] ;
  wire[0:0] \f$bool$arg1  = 1'd0 ;
  wire \f$bool  = \f$bool$arg0  == \f$bool$arg1  ;
  wire[1:0] \f$true  = \i0$data  ;
  wire[0:0] \f$false$bool$arg0$disj  = \sel  ;
  wire[0:0] \f$false$bool$arg0  = \f$false$bool$arg0$disj [0:0] ;
  wire[0:0] \f$false$bool$arg1  = 1'd1 ;
  wire \f$false$bool  = \f$false$bool$arg0  == \f$false$bool$arg1  ;
  wire[1:0] \f$false$true  = \i1$data  ;
  wire[1:0] \f$false$false  = \i0$data  ;
  wire[1:0] \f$false  = ( \f$false$bool  ? \f$false$true  : \f$false$false  ) ;
  wire[1:0] \f  = ( \f$bool  ? \f$true  : \f$false  ) ;
  
  assign \o0  = \f  ;
endmodule

module \DFIFO_2$type1 (
      input \clk , input \rst 
    , input \bus_ins1$irdy , input [1:0] \bus_ins1$data , output \bus_ins1$trdy 
    , input \bus_ins2$irdy , input [1:0] \bus_ins2$data , output \bus_ins2$trdy 
    , output \bus_outs1$irdy , output [1:0] \bus_outs1$data , input \bus_outs1$trdy 
    , output \bus_outs2$irdy , output [1:0] \bus_outs2$data , input \bus_outs2$trdy 
  );
  
  //
  // Channel declarations
  //
  wire \toQueueUp1$irdy  ;
  wire [1:0] \toQueueUp1$data  ;
  wire \toQueueUp1$trdy  ;
  wire \toQueueDown1$irdy  ;
  wire [1:0] \toQueueDown1$data  ;
  wire \toQueueDown1$trdy  ;
  wire \channel1$irdy  ;
  wire [1:0] \channel1$data  ;
  wire \channel1$trdy  ;
  wire \toQueueUp2$irdy  ;
  wire [1:0] \toQueueUp2$data  ;
  wire \toQueueUp2$trdy  ;
  wire \toQueueDown2$irdy  ;
  wire [1:0] \toQueueDown2$data  ;
  wire \toQueueDown2$trdy  ;
  wire \channel2$irdy  ;
  wire [1:0] \channel2$data  ;
  wire \channel2$trdy  ;
  wire \in0up$irdy  ;
  wire [1:0] \in0up$data  ;
  wire \in0up$trdy  ;
  wire \in0down$irdy  ;
  wire [1:0] \in0down$data  ;
  wire \in0down$trdy  ;
  wire \channel6$irdy  ;
  wire [1:0] \channel6$data  ;
  wire \channel6$trdy  ;
  wire \channel5$irdy  ;
  wire [1:0] \channel5$data  ;
  wire \channel5$trdy  ;
  wire \channel3$irdy  ;
  wire [1:0] \channel3$data  ;
  wire \channel3$trdy  ;
  wire \channel4$irdy  ;
  wire [1:0] \channel4$data  ;
  wire \channel4$trdy  ;
  wire \in1up$irdy  ;
  wire [1:0] \in1up$data  ;
  wire \in1up$trdy  ;
  wire \in1down$irdy  ;
  wire [1:0] \in1down$data  ;
  wire \in1down$trdy  ;
  wire \channel10$irdy  ;
  wire [1:0] \channel10$data  ;
  wire \channel10$trdy  ;
  wire \channel9$irdy  ;
  wire [1:0] \channel9$data  ;
  wire \channel9$trdy  ;
  wire \channel7$irdy  ;
  wire [1:0] \channel7$data  ;
  wire \channel7$trdy  ;
  wire \channel8$irdy  ;
  wire [1:0] \channel8$data  ;
  wire \channel8$trdy  ;
  wire \channel11$irdy  ;
  wire [1:0] \channel11$data  ;
  wire \channel11$trdy  ;
  wire \channel12$irdy  ;
  wire [1:0] \channel12$data  ;
  wire \channel12$trdy  ;
  wire \channel13$irdy  ;
  wire [1:0] \channel13$data  ;
  wire \channel13$trdy  ;
  wire \channel14$irdy  ;
  wire [1:0] \channel14$data  ;
  wire \channel14$trdy  ;
  
  //
  // Function Channels
  //
  wire [1:0] \ofunchan_0_Merge1$data  ;
  wire \sel_Merge1  ;
  wire [1:0] \ofunchan_0_Merge2$data  ;
  wire \sel_Merge2  ;
  wire [1:0] \ofunchan_0_Merge3$data  ;
  wire \sel_Merge3  ;
  wire [1:0] \ofunchan_0_Merge4$data  ;
  wire \sel_Merge4  ;
  
  //
  // Component and Macro instantiations
  //
  \LoadBalancer2  #(
    .DATASIZE(2)
  ) \LoadBalancer1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\channel1$irdy )
    , .\i0$data (\channel1$data )
    , .\i0$trdy (\channel1$trdy )
    , .\o0$irdy (\toQueueUp1$irdy )
    , .\o0$data (\toQueueUp1$data )
    , .\o0$trdy (\toQueueUp1$trdy )
    , .\o1$irdy (\toQueueDown1$irdy )
    , .\o1$data (\toQueueDown1$data )
    , .\o1$trdy (\toQueueDown1$trdy )
  );
  
  \LoadBalancer2  #(
    .DATASIZE(2)
  ) \LoadBalancer2  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\channel2$irdy )
    , .\i0$data (\channel2$data )
    , .\i0$trdy (\channel2$trdy )
    , .\o0$irdy (\toQueueUp2$irdy )
    , .\o0$data (\toQueueUp2$data )
    , .\o0$trdy (\toQueueUp2$trdy )
    , .\o1$irdy (\toQueueDown2$irdy )
    , .\o1$data (\toQueueDown2$data )
    , .\o1$trdy (\toQueueDown2$trdy )
  );
  
  \LoadBalancer2  #(
    .DATASIZE(2)
  ) \LoadBalancer3  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\channel6$irdy )
    , .\i0$data (\channel6$data )
    , .\i0$trdy (\channel6$trdy )
    , .\o0$irdy (\in0up$irdy )
    , .\o0$data (\in0up$data )
    , .\o0$trdy (\in0up$trdy )
    , .\o1$irdy (\in0down$irdy )
    , .\o1$data (\in0down$data )
    , .\o1$trdy (\in0down$trdy )
  );
  
  \Queue  #(
    .NUM_DATA(0),
    .DATASIZE(2),
    .LENGTH(2)
  ) \Queue1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\channel5$irdy )
    , .\i0$data (\channel5$data )
    , .\i0$trdy (\channel5$trdy )
    , .\o0$irdy (\channel6$irdy )
    , .\o0$data (\channel6$data )
    , .\o0$trdy (\channel6$trdy )
  );
  
  \Merge2  #(
    .INPUTSIZE1(2),
    .OUTPUTSIZE(2),
    .INPUTSIZE0(2)
  ) \Merge1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\channel3$irdy )
    , .\i0$data (\channel3$data )
    , .\i0$trdy (\channel3$trdy )
    , .\i1$irdy (\channel4$irdy )
    , .\i1$data (\channel4$data )
    , .\i1$trdy (\channel4$trdy )
    , .\o0$irdy (\channel5$irdy )
    , .\o0$data (\channel5$data )
    , .\o0$trdy (\channel5$trdy )
    , .\f$data (\ofunchan_0_Merge1$data )
    , .\sel (\sel_Merge1 )
  );
  
  \OFUN_0$DFIFO_2_Merge1  \ofun_0_Merge1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\channel3$data )
    , .\i1$data (\channel4$data )
    , .\sel (\sel_Merge1 )
    , .\o0 (\ofunchan_0_Merge1$data )
  );
  
  \LoadBalancer2  #(
    .DATASIZE(2)
  ) \LoadBalancer4  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\channel10$irdy )
    , .\i0$data (\channel10$data )
    , .\i0$trdy (\channel10$trdy )
    , .\o0$irdy (\in1up$irdy )
    , .\o0$data (\in1up$data )
    , .\o0$trdy (\in1up$trdy )
    , .\o1$irdy (\in1down$irdy )
    , .\o1$data (\in1down$data )
    , .\o1$trdy (\in1down$trdy )
  );
  
  \Queue  #(
    .NUM_DATA(0),
    .DATASIZE(2),
    .LENGTH(2)
  ) \Queue2  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\channel9$irdy )
    , .\i0$data (\channel9$data )
    , .\i0$trdy (\channel9$trdy )
    , .\o0$irdy (\channel10$irdy )
    , .\o0$data (\channel10$data )
    , .\o0$trdy (\channel10$trdy )
  );
  
  \Merge2  #(
    .INPUTSIZE1(2),
    .OUTPUTSIZE(2),
    .INPUTSIZE0(2)
  ) \Merge2  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\channel7$irdy )
    , .\i0$data (\channel7$data )
    , .\i0$trdy (\channel7$trdy )
    , .\i1$irdy (\channel8$irdy )
    , .\i1$data (\channel8$data )
    , .\i1$trdy (\channel8$trdy )
    , .\o0$irdy (\channel9$irdy )
    , .\o0$data (\channel9$data )
    , .\o0$trdy (\channel9$trdy )
    , .\f$data (\ofunchan_0_Merge2$data )
    , .\sel (\sel_Merge2 )
  );
  
  \OFUN_0$DFIFO_2_Merge2  \ofun_0_Merge2  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\channel7$data )
    , .\i1$data (\channel8$data )
    , .\sel (\sel_Merge2 )
    , .\o0 (\ofunchan_0_Merge2$data )
  );
  
  \Merge2  #(
    .INPUTSIZE1(2),
    .OUTPUTSIZE(2),
    .INPUTSIZE0(2)
  ) \Merge3  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\channel11$irdy )
    , .\i0$data (\channel11$data )
    , .\i0$trdy (\channel11$trdy )
    , .\i1$irdy (\channel12$irdy )
    , .\i1$data (\channel12$data )
    , .\i1$trdy (\channel12$trdy )
    , .\o0$irdy (\bus_outs1$irdy )
    , .\o0$data (\bus_outs1$data )
    , .\o0$trdy (\bus_outs1$trdy )
    , .\f$data (\ofunchan_0_Merge3$data )
    , .\sel (\sel_Merge3 )
  );
  
  \OFUN_0$DFIFO_2_Merge3  \ofun_0_Merge3  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\channel11$data )
    , .\i1$data (\channel12$data )
    , .\sel (\sel_Merge3 )
    , .\o0 (\ofunchan_0_Merge3$data )
  );
  
  \Merge2  #(
    .INPUTSIZE1(2),
    .OUTPUTSIZE(2),
    .INPUTSIZE0(2)
  ) \Merge4  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\channel13$irdy )
    , .\i0$data (\channel13$data )
    , .\i0$trdy (\channel13$trdy )
    , .\i1$irdy (\channel14$irdy )
    , .\i1$data (\channel14$data )
    , .\i1$trdy (\channel14$trdy )
    , .\o0$irdy (\bus_outs2$irdy )
    , .\o0$data (\bus_outs2$data )
    , .\o0$trdy (\bus_outs2$trdy )
    , .\f$data (\ofunchan_0_Merge4$data )
    , .\sel (\sel_Merge4 )
  );
  
  \OFUN_0$DFIFO_2_Merge4  \ofun_0_Merge4  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\channel13$data )
    , .\i1$data (\channel14$data )
    , .\sel (\sel_Merge4 )
    , .\o0 (\ofunchan_0_Merge4$data )
  );
  
  \Latch$type3  \Latch1  (
      .\clk (\clk ), .\rst (\rst )
    , .\input$irdy (\bus_ins1$irdy )
    , .\input$data (\bus_ins1$data )
    , .\input$trdy (\bus_ins1$trdy )
    , .\output$irdy (\channel1$irdy )
    , .\output$data (\channel1$data )
    , .\output$trdy (\channel1$trdy )
  );
  
  \Latch$type4  \Latch2  (
      .\clk (\clk ), .\rst (\rst )
    , .\input$irdy (\bus_ins2$irdy )
    , .\input$data (\bus_ins2$data )
    , .\input$trdy (\bus_ins2$trdy )
    , .\output$irdy (\channel2$irdy )
    , .\output$data (\channel2$data )
    , .\output$trdy (\channel2$trdy )
  );
  
  \Latch$type3  \Latch3  (
      .\clk (\clk ), .\rst (\rst )
    , .\input$irdy (\toQueueUp1$irdy )
    , .\input$data (\toQueueUp1$data )
    , .\input$trdy (\toQueueUp1$trdy )
    , .\output$irdy (\channel3$irdy )
    , .\output$data (\channel3$data )
    , .\output$trdy (\channel3$trdy )
  );
  
  \Latch$type4  \Latch4  (
      .\clk (\clk ), .\rst (\rst )
    , .\input$irdy (\toQueueUp2$irdy )
    , .\input$data (\toQueueUp2$data )
    , .\input$trdy (\toQueueUp2$trdy )
    , .\output$irdy (\channel4$irdy )
    , .\output$data (\channel4$data )
    , .\output$trdy (\channel4$trdy )
  );
  
  \Latch$type3  \Latch5  (
      .\clk (\clk ), .\rst (\rst )
    , .\input$irdy (\toQueueDown1$irdy )
    , .\input$data (\toQueueDown1$data )
    , .\input$trdy (\toQueueDown1$trdy )
    , .\output$irdy (\channel7$irdy )
    , .\output$data (\channel7$data )
    , .\output$trdy (\channel7$trdy )
  );
  
  \Latch$type4  \Latch6  (
      .\clk (\clk ), .\rst (\rst )
    , .\input$irdy (\toQueueDown2$irdy )
    , .\input$data (\toQueueDown2$data )
    , .\input$trdy (\toQueueDown2$trdy )
    , .\output$irdy (\channel8$irdy )
    , .\output$data (\channel8$data )
    , .\output$trdy (\channel8$trdy )
  );
  
  \Latch$type4  \Latch7  (
      .\clk (\clk ), .\rst (\rst )
    , .\input$irdy (\in0up$irdy )
    , .\input$data (\in0up$data )
    , .\input$trdy (\in0up$trdy )
    , .\output$irdy (\channel11$irdy )
    , .\output$data (\channel11$data )
    , .\output$trdy (\channel11$trdy )
  );
  
  \Latch$type4  \Latch8  (
      .\clk (\clk ), .\rst (\rst )
    , .\input$irdy (\in1up$irdy )
    , .\input$data (\in1up$data )
    , .\input$trdy (\in1up$trdy )
    , .\output$irdy (\channel12$irdy )
    , .\output$data (\channel12$data )
    , .\output$trdy (\channel12$trdy )
  );
  
  \Latch$type4  \Latch9  (
      .\clk (\clk ), .\rst (\rst )
    , .\input$irdy (\in0down$irdy )
    , .\input$data (\in0down$data )
    , .\input$trdy (\in0down$trdy )
    , .\output$irdy (\channel13$irdy )
    , .\output$data (\channel13$data )
    , .\output$trdy (\channel13$trdy )
  );
  
  \Latch$type4  \Latch10  (
      .\clk (\clk ), .\rst (\rst )
    , .\input$irdy (\in1down$irdy )
    , .\input$data (\in1down$data )
    , .\input$trdy (\in1down$trdy )
    , .\output$irdy (\channel14$irdy )
    , .\output$data (\channel14$data )
    , .\output$trdy (\channel14$trdy )
  );
  
endmodule


//
// DFIFO_2 switch functions
//
module \OFUN_0$DFIFO_2_Merge1 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , input [1:0] \i1$data 
    , input \sel 
    , output [1:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[0:0] \f$bool$arg0$disj  = \sel  ;
  wire[0:0] \f$bool$arg0  = \f$bool$arg0$disj [0:0] ;
  wire[0:0] \f$bool$arg1  = 1'd0 ;
  wire \f$bool  = \f$bool$arg0  == \f$bool$arg1  ;
  wire[1:0] \f$true  = \i0$data  ;
  wire[0:0] \f$false$bool$arg0$disj  = \sel  ;
  wire[0:0] \f$false$bool$arg0  = \f$false$bool$arg0$disj [0:0] ;
  wire[0:0] \f$false$bool$arg1  = 1'd1 ;
  wire \f$false$bool  = \f$false$bool$arg0  == \f$false$bool$arg1  ;
  wire[1:0] \f$false$true  = \i1$data  ;
  wire[1:0] \f$false$false  = \i0$data  ;
  wire[1:0] \f$false  = ( \f$false$bool  ? \f$false$true  : \f$false$false  ) ;
  wire[1:0] \f  = ( \f$bool  ? \f$true  : \f$false  ) ;
  
  assign \o0  = \f  ;
endmodule

module \OFUN_0$DFIFO_2_Merge2 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , input [1:0] \i1$data 
    , input \sel 
    , output [1:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[0:0] \f$bool$arg0$disj  = \sel  ;
  wire[0:0] \f$bool$arg0  = \f$bool$arg0$disj [0:0] ;
  wire[0:0] \f$bool$arg1  = 1'd0 ;
  wire \f$bool  = \f$bool$arg0  == \f$bool$arg1  ;
  wire[1:0] \f$true  = \i0$data  ;
  wire[0:0] \f$false$bool$arg0$disj  = \sel  ;
  wire[0:0] \f$false$bool$arg0  = \f$false$bool$arg0$disj [0:0] ;
  wire[0:0] \f$false$bool$arg1  = 1'd1 ;
  wire \f$false$bool  = \f$false$bool$arg0  == \f$false$bool$arg1  ;
  wire[1:0] \f$false$true  = \i1$data  ;
  wire[1:0] \f$false$false  = \i0$data  ;
  wire[1:0] \f$false  = ( \f$false$bool  ? \f$false$true  : \f$false$false  ) ;
  wire[1:0] \f  = ( \f$bool  ? \f$true  : \f$false  ) ;
  
  assign \o0  = \f  ;
endmodule

module \OFUN_0$DFIFO_2_Merge3 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , input [1:0] \i1$data 
    , input \sel 
    , output [1:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[0:0] \f$bool$arg0$disj  = \sel  ;
  wire[0:0] \f$bool$arg0  = \f$bool$arg0$disj [0:0] ;
  wire[0:0] \f$bool$arg1  = 1'd0 ;
  wire \f$bool  = \f$bool$arg0  == \f$bool$arg1  ;
  wire[1:0] \f$true  = \i0$data  ;
  wire[0:0] \f$false$bool$arg0$disj  = \sel  ;
  wire[0:0] \f$false$bool$arg0  = \f$false$bool$arg0$disj [0:0] ;
  wire[0:0] \f$false$bool$arg1  = 1'd1 ;
  wire \f$false$bool  = \f$false$bool$arg0  == \f$false$bool$arg1  ;
  wire[1:0] \f$false$true  = \i1$data  ;
  wire[1:0] \f$false$false  = \i0$data  ;
  wire[1:0] \f$false  = ( \f$false$bool  ? \f$false$true  : \f$false$false  ) ;
  wire[1:0] \f  = ( \f$bool  ? \f$true  : \f$false  ) ;
  
  assign \o0  = \f  ;
endmodule

module \OFUN_0$DFIFO_2_Merge4 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , input [1:0] \i1$data 
    , input \sel 
    , output [1:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[0:0] \f$bool$arg0$disj  = \sel  ;
  wire[0:0] \f$bool$arg0  = \f$bool$arg0$disj [0:0] ;
  wire[0:0] \f$bool$arg1  = 1'd0 ;
  wire \f$bool  = \f$bool$arg0  == \f$bool$arg1  ;
  wire[1:0] \f$true  = \i0$data  ;
  wire[0:0] \f$false$bool$arg0$disj  = \sel  ;
  wire[0:0] \f$false$bool$arg0  = \f$false$bool$arg0$disj [0:0] ;
  wire[0:0] \f$false$bool$arg1  = 1'd1 ;
  wire \f$false$bool  = \f$false$bool$arg0  == \f$false$bool$arg1  ;
  wire[1:0] \f$false$true  = \i1$data  ;
  wire[1:0] \f$false$false  = \i0$data  ;
  wire[1:0] \f$false  = ( \f$false$bool  ? \f$false$true  : \f$false$false  ) ;
  wire[1:0] \f  = ( \f$bool  ? \f$true  : \f$false  ) ;
  
  assign \o0  = \f  ;
endmodule

module \DFIFO_2$type2 (
      input \clk , input \rst 
    , input \bus_ins1$irdy , input [1:0] \bus_ins1$data , output \bus_ins1$trdy 
    , input \bus_ins2$irdy , input [1:0] \bus_ins2$data , output \bus_ins2$trdy 
    , output \bus_outs1$irdy , output [1:0] \bus_outs1$data , input \bus_outs1$trdy 
    , output \bus_outs2$irdy , output [1:0] \bus_outs2$data , input \bus_outs2$trdy 
  );
  
  //
  // Channel declarations
  //
  wire \toQueueUp1$irdy  ;
  wire [1:0] \toQueueUp1$data  ;
  wire \toQueueUp1$trdy  ;
  wire \toQueueDown1$irdy  ;
  wire [1:0] \toQueueDown1$data  ;
  wire \toQueueDown1$trdy  ;
  wire \channel1$irdy  ;
  wire [1:0] \channel1$data  ;
  wire \channel1$trdy  ;
  wire \toQueueUp2$irdy  ;
  wire [1:0] \toQueueUp2$data  ;
  wire \toQueueUp2$trdy  ;
  wire \toQueueDown2$irdy  ;
  wire [1:0] \toQueueDown2$data  ;
  wire \toQueueDown2$trdy  ;
  wire \channel2$irdy  ;
  wire [1:0] \channel2$data  ;
  wire \channel2$trdy  ;
  wire \in0up$irdy  ;
  wire [1:0] \in0up$data  ;
  wire \in0up$trdy  ;
  wire \in0down$irdy  ;
  wire [1:0] \in0down$data  ;
  wire \in0down$trdy  ;
  wire \channel6$irdy  ;
  wire [1:0] \channel6$data  ;
  wire \channel6$trdy  ;
  wire \channel5$irdy  ;
  wire [1:0] \channel5$data  ;
  wire \channel5$trdy  ;
  wire \channel3$irdy  ;
  wire [1:0] \channel3$data  ;
  wire \channel3$trdy  ;
  wire \channel4$irdy  ;
  wire [1:0] \channel4$data  ;
  wire \channel4$trdy  ;
  wire \in1up$irdy  ;
  wire [1:0] \in1up$data  ;
  wire \in1up$trdy  ;
  wire \in1down$irdy  ;
  wire [1:0] \in1down$data  ;
  wire \in1down$trdy  ;
  wire \channel10$irdy  ;
  wire [1:0] \channel10$data  ;
  wire \channel10$trdy  ;
  wire \channel9$irdy  ;
  wire [1:0] \channel9$data  ;
  wire \channel9$trdy  ;
  wire \channel7$irdy  ;
  wire [1:0] \channel7$data  ;
  wire \channel7$trdy  ;
  wire \channel8$irdy  ;
  wire [1:0] \channel8$data  ;
  wire \channel8$trdy  ;
  wire \channel11$irdy  ;
  wire [1:0] \channel11$data  ;
  wire \channel11$trdy  ;
  wire \channel12$irdy  ;
  wire [1:0] \channel12$data  ;
  wire \channel12$trdy  ;
  wire \channel13$irdy  ;
  wire [1:0] \channel13$data  ;
  wire \channel13$trdy  ;
  wire \channel14$irdy  ;
  wire [1:0] \channel14$data  ;
  wire \channel14$trdy  ;
  
  //
  // Function Channels
  //
  wire [1:0] \ofunchan_0_Merge1$data  ;
  wire \sel_Merge1  ;
  wire [1:0] \ofunchan_0_Merge2$data  ;
  wire \sel_Merge2  ;
  wire [1:0] \ofunchan_0_Merge3$data  ;
  wire \sel_Merge3  ;
  wire [1:0] \ofunchan_0_Merge4$data  ;
  wire \sel_Merge4  ;
  
  //
  // Component and Macro instantiations
  //
  \LoadBalancer2  #(
    .DATASIZE(2)
  ) \LoadBalancer1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\channel1$irdy )
    , .\i0$data (\channel1$data )
    , .\i0$trdy (\channel1$trdy )
    , .\o0$irdy (\toQueueUp1$irdy )
    , .\o0$data (\toQueueUp1$data )
    , .\o0$trdy (\toQueueUp1$trdy )
    , .\o1$irdy (\toQueueDown1$irdy )
    , .\o1$data (\toQueueDown1$data )
    , .\o1$trdy (\toQueueDown1$trdy )
  );
  
  \LoadBalancer2  #(
    .DATASIZE(2)
  ) \LoadBalancer2  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\channel2$irdy )
    , .\i0$data (\channel2$data )
    , .\i0$trdy (\channel2$trdy )
    , .\o0$irdy (\toQueueUp2$irdy )
    , .\o0$data (\toQueueUp2$data )
    , .\o0$trdy (\toQueueUp2$trdy )
    , .\o1$irdy (\toQueueDown2$irdy )
    , .\o1$data (\toQueueDown2$data )
    , .\o1$trdy (\toQueueDown2$trdy )
  );
  
  \LoadBalancer2  #(
    .DATASIZE(2)
  ) \LoadBalancer3  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\channel6$irdy )
    , .\i0$data (\channel6$data )
    , .\i0$trdy (\channel6$trdy )
    , .\o0$irdy (\in0up$irdy )
    , .\o0$data (\in0up$data )
    , .\o0$trdy (\in0up$trdy )
    , .\o1$irdy (\in0down$irdy )
    , .\o1$data (\in0down$data )
    , .\o1$trdy (\in0down$trdy )
  );
  
  \Queue  #(
    .NUM_DATA(0),
    .DATASIZE(2),
    .LENGTH(2)
  ) \Queue1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\channel5$irdy )
    , .\i0$data (\channel5$data )
    , .\i0$trdy (\channel5$trdy )
    , .\o0$irdy (\channel6$irdy )
    , .\o0$data (\channel6$data )
    , .\o0$trdy (\channel6$trdy )
  );
  
  \Merge2  #(
    .INPUTSIZE1(2),
    .OUTPUTSIZE(2),
    .INPUTSIZE0(2)
  ) \Merge1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\channel3$irdy )
    , .\i0$data (\channel3$data )
    , .\i0$trdy (\channel3$trdy )
    , .\i1$irdy (\channel4$irdy )
    , .\i1$data (\channel4$data )
    , .\i1$trdy (\channel4$trdy )
    , .\o0$irdy (\channel5$irdy )
    , .\o0$data (\channel5$data )
    , .\o0$trdy (\channel5$trdy )
    , .\f$data (\ofunchan_0_Merge1$data )
    , .\sel (\sel_Merge1 )
  );
  
  \OFUN_0$DFIFO_2_Merge1  \ofun_0_Merge1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\channel3$data )
    , .\i1$data (\channel4$data )
    , .\sel (\sel_Merge1 )
    , .\o0 (\ofunchan_0_Merge1$data )
  );
  
  \LoadBalancer2  #(
    .DATASIZE(2)
  ) \LoadBalancer4  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\channel10$irdy )
    , .\i0$data (\channel10$data )
    , .\i0$trdy (\channel10$trdy )
    , .\o0$irdy (\in1up$irdy )
    , .\o0$data (\in1up$data )
    , .\o0$trdy (\in1up$trdy )
    , .\o1$irdy (\in1down$irdy )
    , .\o1$data (\in1down$data )
    , .\o1$trdy (\in1down$trdy )
  );
  
  \Queue  #(
    .NUM_DATA(0),
    .DATASIZE(2),
    .LENGTH(2)
  ) \Queue2  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\channel9$irdy )
    , .\i0$data (\channel9$data )
    , .\i0$trdy (\channel9$trdy )
    , .\o0$irdy (\channel10$irdy )
    , .\o0$data (\channel10$data )
    , .\o0$trdy (\channel10$trdy )
  );
  
  \Merge2  #(
    .INPUTSIZE1(2),
    .OUTPUTSIZE(2),
    .INPUTSIZE0(2)
  ) \Merge2  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\channel7$irdy )
    , .\i0$data (\channel7$data )
    , .\i0$trdy (\channel7$trdy )
    , .\i1$irdy (\channel8$irdy )
    , .\i1$data (\channel8$data )
    , .\i1$trdy (\channel8$trdy )
    , .\o0$irdy (\channel9$irdy )
    , .\o0$data (\channel9$data )
    , .\o0$trdy (\channel9$trdy )
    , .\f$data (\ofunchan_0_Merge2$data )
    , .\sel (\sel_Merge2 )
  );
  
  \OFUN_0$DFIFO_2_Merge2  \ofun_0_Merge2  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\channel7$data )
    , .\i1$data (\channel8$data )
    , .\sel (\sel_Merge2 )
    , .\o0 (\ofunchan_0_Merge2$data )
  );
  
  \Merge2  #(
    .INPUTSIZE1(2),
    .OUTPUTSIZE(2),
    .INPUTSIZE0(2)
  ) \Merge3  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\channel11$irdy )
    , .\i0$data (\channel11$data )
    , .\i0$trdy (\channel11$trdy )
    , .\i1$irdy (\channel12$irdy )
    , .\i1$data (\channel12$data )
    , .\i1$trdy (\channel12$trdy )
    , .\o0$irdy (\bus_outs1$irdy )
    , .\o0$data (\bus_outs1$data )
    , .\o0$trdy (\bus_outs1$trdy )
    , .\f$data (\ofunchan_0_Merge3$data )
    , .\sel (\sel_Merge3 )
  );
  
  \OFUN_0$DFIFO_2_Merge3  \ofun_0_Merge3  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\channel11$data )
    , .\i1$data (\channel12$data )
    , .\sel (\sel_Merge3 )
    , .\o0 (\ofunchan_0_Merge3$data )
  );
  
  \Merge2  #(
    .INPUTSIZE1(2),
    .OUTPUTSIZE(2),
    .INPUTSIZE0(2)
  ) \Merge4  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\channel13$irdy )
    , .\i0$data (\channel13$data )
    , .\i0$trdy (\channel13$trdy )
    , .\i1$irdy (\channel14$irdy )
    , .\i1$data (\channel14$data )
    , .\i1$trdy (\channel14$trdy )
    , .\o0$irdy (\bus_outs2$irdy )
    , .\o0$data (\bus_outs2$data )
    , .\o0$trdy (\bus_outs2$trdy )
    , .\f$data (\ofunchan_0_Merge4$data )
    , .\sel (\sel_Merge4 )
  );
  
  \OFUN_0$DFIFO_2_Merge4  \ofun_0_Merge4  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\channel13$data )
    , .\i1$data (\channel14$data )
    , .\sel (\sel_Merge4 )
    , .\o0 (\ofunchan_0_Merge4$data )
  );
  
  \Latch$type5  \Latch1  (
      .\clk (\clk ), .\rst (\rst )
    , .\input$irdy (\bus_ins1$irdy )
    , .\input$data (\bus_ins1$data )
    , .\input$trdy (\bus_ins1$trdy )
    , .\output$irdy (\channel1$irdy )
    , .\output$data (\channel1$data )
    , .\output$trdy (\channel1$trdy )
  );
  
  \Latch$type4  \Latch2  (
      .\clk (\clk ), .\rst (\rst )
    , .\input$irdy (\bus_ins2$irdy )
    , .\input$data (\bus_ins2$data )
    , .\input$trdy (\bus_ins2$trdy )
    , .\output$irdy (\channel2$irdy )
    , .\output$data (\channel2$data )
    , .\output$trdy (\channel2$trdy )
  );
  
  \Latch$type5  \Latch3  (
      .\clk (\clk ), .\rst (\rst )
    , .\input$irdy (\toQueueUp1$irdy )
    , .\input$data (\toQueueUp1$data )
    , .\input$trdy (\toQueueUp1$trdy )
    , .\output$irdy (\channel3$irdy )
    , .\output$data (\channel3$data )
    , .\output$trdy (\channel3$trdy )
  );
  
  \Latch$type4  \Latch4  (
      .\clk (\clk ), .\rst (\rst )
    , .\input$irdy (\toQueueUp2$irdy )
    , .\input$data (\toQueueUp2$data )
    , .\input$trdy (\toQueueUp2$trdy )
    , .\output$irdy (\channel4$irdy )
    , .\output$data (\channel4$data )
    , .\output$trdy (\channel4$trdy )
  );
  
  \Latch$type5  \Latch5  (
      .\clk (\clk ), .\rst (\rst )
    , .\input$irdy (\toQueueDown1$irdy )
    , .\input$data (\toQueueDown1$data )
    , .\input$trdy (\toQueueDown1$trdy )
    , .\output$irdy (\channel7$irdy )
    , .\output$data (\channel7$data )
    , .\output$trdy (\channel7$trdy )
  );
  
  \Latch$type4  \Latch6  (
      .\clk (\clk ), .\rst (\rst )
    , .\input$irdy (\toQueueDown2$irdy )
    , .\input$data (\toQueueDown2$data )
    , .\input$trdy (\toQueueDown2$trdy )
    , .\output$irdy (\channel8$irdy )
    , .\output$data (\channel8$data )
    , .\output$trdy (\channel8$trdy )
  );
  
  \Latch$type4  \Latch7  (
      .\clk (\clk ), .\rst (\rst )
    , .\input$irdy (\in0up$irdy )
    , .\input$data (\in0up$data )
    , .\input$trdy (\in0up$trdy )
    , .\output$irdy (\channel11$irdy )
    , .\output$data (\channel11$data )
    , .\output$trdy (\channel11$trdy )
  );
  
  \Latch$type4  \Latch8  (
      .\clk (\clk ), .\rst (\rst )
    , .\input$irdy (\in1up$irdy )
    , .\input$data (\in1up$data )
    , .\input$trdy (\in1up$trdy )
    , .\output$irdy (\channel12$irdy )
    , .\output$data (\channel12$data )
    , .\output$trdy (\channel12$trdy )
  );
  
  \Latch$type4  \Latch9  (
      .\clk (\clk ), .\rst (\rst )
    , .\input$irdy (\in0down$irdy )
    , .\input$data (\in0down$data )
    , .\input$trdy (\in0down$trdy )
    , .\output$irdy (\channel13$irdy )
    , .\output$data (\channel13$data )
    , .\output$trdy (\channel13$trdy )
  );
  
  \Latch$type4  \Latch10  (
      .\clk (\clk ), .\rst (\rst )
    , .\input$irdy (\in1down$irdy )
    , .\input$data (\in1down$data )
    , .\input$trdy (\in1down$trdy )
    , .\output$irdy (\channel14$irdy )
    , .\output$data (\channel14$data )
    , .\output$trdy (\channel14$trdy )
  );
  
endmodule


//
// DFIFO_2 switch functions
//
module \OFUN_0$DFIFO_2_Merge1 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , input [1:0] \i1$data 
    , input \sel 
    , output [1:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[0:0] \f$bool$arg0$disj  = \sel  ;
  wire[0:0] \f$bool$arg0  = \f$bool$arg0$disj [0:0] ;
  wire[0:0] \f$bool$arg1  = 1'd0 ;
  wire \f$bool  = \f$bool$arg0  == \f$bool$arg1  ;
  wire[1:0] \f$true  = \i0$data  ;
  wire[0:0] \f$false$bool$arg0$disj  = \sel  ;
  wire[0:0] \f$false$bool$arg0  = \f$false$bool$arg0$disj [0:0] ;
  wire[0:0] \f$false$bool$arg1  = 1'd1 ;
  wire \f$false$bool  = \f$false$bool$arg0  == \f$false$bool$arg1  ;
  wire[1:0] \f$false$true  = \i1$data  ;
  wire[1:0] \f$false$false  = \i0$data  ;
  wire[1:0] \f$false  = ( \f$false$bool  ? \f$false$true  : \f$false$false  ) ;
  wire[1:0] \f  = ( \f$bool  ? \f$true  : \f$false  ) ;
  
  assign \o0  = \f  ;
endmodule

module \OFUN_0$DFIFO_2_Merge2 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , input [1:0] \i1$data 
    , input \sel 
    , output [1:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[0:0] \f$bool$arg0$disj  = \sel  ;
  wire[0:0] \f$bool$arg0  = \f$bool$arg0$disj [0:0] ;
  wire[0:0] \f$bool$arg1  = 1'd0 ;
  wire \f$bool  = \f$bool$arg0  == \f$bool$arg1  ;
  wire[1:0] \f$true  = \i0$data  ;
  wire[0:0] \f$false$bool$arg0$disj  = \sel  ;
  wire[0:0] \f$false$bool$arg0  = \f$false$bool$arg0$disj [0:0] ;
  wire[0:0] \f$false$bool$arg1  = 1'd1 ;
  wire \f$false$bool  = \f$false$bool$arg0  == \f$false$bool$arg1  ;
  wire[1:0] \f$false$true  = \i1$data  ;
  wire[1:0] \f$false$false  = \i0$data  ;
  wire[1:0] \f$false  = ( \f$false$bool  ? \f$false$true  : \f$false$false  ) ;
  wire[1:0] \f  = ( \f$bool  ? \f$true  : \f$false  ) ;
  
  assign \o0  = \f  ;
endmodule

module \OFUN_0$DFIFO_2_Merge3 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , input [1:0] \i1$data 
    , input \sel 
    , output [1:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[0:0] \f$bool$arg0$disj  = \sel  ;
  wire[0:0] \f$bool$arg0  = \f$bool$arg0$disj [0:0] ;
  wire[0:0] \f$bool$arg1  = 1'd0 ;
  wire \f$bool  = \f$bool$arg0  == \f$bool$arg1  ;
  wire[1:0] \f$true  = \i0$data  ;
  wire[0:0] \f$false$bool$arg0$disj  = \sel  ;
  wire[0:0] \f$false$bool$arg0  = \f$false$bool$arg0$disj [0:0] ;
  wire[0:0] \f$false$bool$arg1  = 1'd1 ;
  wire \f$false$bool  = \f$false$bool$arg0  == \f$false$bool$arg1  ;
  wire[1:0] \f$false$true  = \i1$data  ;
  wire[1:0] \f$false$false  = \i0$data  ;
  wire[1:0] \f$false  = ( \f$false$bool  ? \f$false$true  : \f$false$false  ) ;
  wire[1:0] \f  = ( \f$bool  ? \f$true  : \f$false  ) ;
  
  assign \o0  = \f  ;
endmodule

module \OFUN_0$DFIFO_2_Merge4 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , input [1:0] \i1$data 
    , input \sel 
    , output [1:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[0:0] \f$bool$arg0$disj  = \sel  ;
  wire[0:0] \f$bool$arg0  = \f$bool$arg0$disj [0:0] ;
  wire[0:0] \f$bool$arg1  = 1'd0 ;
  wire \f$bool  = \f$bool$arg0  == \f$bool$arg1  ;
  wire[1:0] \f$true  = \i0$data  ;
  wire[0:0] \f$false$bool$arg0$disj  = \sel  ;
  wire[0:0] \f$false$bool$arg0  = \f$false$bool$arg0$disj [0:0] ;
  wire[0:0] \f$false$bool$arg1  = 1'd1 ;
  wire \f$false$bool  = \f$false$bool$arg0  == \f$false$bool$arg1  ;
  wire[1:0] \f$false$true  = \i1$data  ;
  wire[1:0] \f$false$false  = \i0$data  ;
  wire[1:0] \f$false  = ( \f$false$bool  ? \f$false$true  : \f$false$false  ) ;
  wire[1:0] \f  = ( \f$bool  ? \f$true  : \f$false  ) ;
  
  assign \o0  = \f  ;
endmodule

module \DFIFO_2$type3 (
      input \clk , input \rst 
    , input \bus_ins1$irdy , input [1:0] \bus_ins1$data , output \bus_ins1$trdy 
    , input \bus_ins2$irdy , input [1:0] \bus_ins2$data , output \bus_ins2$trdy 
    , output \bus_outs1$irdy , output [1:0] \bus_outs1$data , input \bus_outs1$trdy 
    , output \bus_outs2$irdy , output [1:0] \bus_outs2$data , input \bus_outs2$trdy 
  );
  
  //
  // Channel declarations
  //
  wire \toQueueUp1$irdy  ;
  wire [1:0] \toQueueUp1$data  ;
  wire \toQueueUp1$trdy  ;
  wire \toQueueDown1$irdy  ;
  wire [1:0] \toQueueDown1$data  ;
  wire \toQueueDown1$trdy  ;
  wire \channel1$irdy  ;
  wire [1:0] \channel1$data  ;
  wire \channel1$trdy  ;
  wire \toQueueUp2$irdy  ;
  wire [1:0] \toQueueUp2$data  ;
  wire \toQueueUp2$trdy  ;
  wire \toQueueDown2$irdy  ;
  wire [1:0] \toQueueDown2$data  ;
  wire \toQueueDown2$trdy  ;
  wire \channel2$irdy  ;
  wire [1:0] \channel2$data  ;
  wire \channel2$trdy  ;
  wire \in0up$irdy  ;
  wire [1:0] \in0up$data  ;
  wire \in0up$trdy  ;
  wire \in0down$irdy  ;
  wire [1:0] \in0down$data  ;
  wire \in0down$trdy  ;
  wire \channel6$irdy  ;
  wire [1:0] \channel6$data  ;
  wire \channel6$trdy  ;
  wire \channel5$irdy  ;
  wire [1:0] \channel5$data  ;
  wire \channel5$trdy  ;
  wire \channel3$irdy  ;
  wire [1:0] \channel3$data  ;
  wire \channel3$trdy  ;
  wire \channel4$irdy  ;
  wire [1:0] \channel4$data  ;
  wire \channel4$trdy  ;
  wire \in1up$irdy  ;
  wire [1:0] \in1up$data  ;
  wire \in1up$trdy  ;
  wire \in1down$irdy  ;
  wire [1:0] \in1down$data  ;
  wire \in1down$trdy  ;
  wire \channel10$irdy  ;
  wire [1:0] \channel10$data  ;
  wire \channel10$trdy  ;
  wire \channel9$irdy  ;
  wire [1:0] \channel9$data  ;
  wire \channel9$trdy  ;
  wire \channel7$irdy  ;
  wire [1:0] \channel7$data  ;
  wire \channel7$trdy  ;
  wire \channel8$irdy  ;
  wire [1:0] \channel8$data  ;
  wire \channel8$trdy  ;
  wire \channel11$irdy  ;
  wire [1:0] \channel11$data  ;
  wire \channel11$trdy  ;
  wire \channel12$irdy  ;
  wire [1:0] \channel12$data  ;
  wire \channel12$trdy  ;
  wire \channel13$irdy  ;
  wire [1:0] \channel13$data  ;
  wire \channel13$trdy  ;
  wire \channel14$irdy  ;
  wire [1:0] \channel14$data  ;
  wire \channel14$trdy  ;
  
  //
  // Function Channels
  //
  wire [1:0] \ofunchan_0_Merge1$data  ;
  wire \sel_Merge1  ;
  wire [1:0] \ofunchan_0_Merge2$data  ;
  wire \sel_Merge2  ;
  wire [1:0] \ofunchan_0_Merge3$data  ;
  wire \sel_Merge3  ;
  wire [1:0] \ofunchan_0_Merge4$data  ;
  wire \sel_Merge4  ;
  
  //
  // Component and Macro instantiations
  //
  \LoadBalancer2  #(
    .DATASIZE(2)
  ) \LoadBalancer1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\channel1$irdy )
    , .\i0$data (\channel1$data )
    , .\i0$trdy (\channel1$trdy )
    , .\o0$irdy (\toQueueUp1$irdy )
    , .\o0$data (\toQueueUp1$data )
    , .\o0$trdy (\toQueueUp1$trdy )
    , .\o1$irdy (\toQueueDown1$irdy )
    , .\o1$data (\toQueueDown1$data )
    , .\o1$trdy (\toQueueDown1$trdy )
  );
  
  \LoadBalancer2  #(
    .DATASIZE(2)
  ) \LoadBalancer2  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\channel2$irdy )
    , .\i0$data (\channel2$data )
    , .\i0$trdy (\channel2$trdy )
    , .\o0$irdy (\toQueueUp2$irdy )
    , .\o0$data (\toQueueUp2$data )
    , .\o0$trdy (\toQueueUp2$trdy )
    , .\o1$irdy (\toQueueDown2$irdy )
    , .\o1$data (\toQueueDown2$data )
    , .\o1$trdy (\toQueueDown2$trdy )
  );
  
  \LoadBalancer2  #(
    .DATASIZE(2)
  ) \LoadBalancer3  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\channel6$irdy )
    , .\i0$data (\channel6$data )
    , .\i0$trdy (\channel6$trdy )
    , .\o0$irdy (\in0up$irdy )
    , .\o0$data (\in0up$data )
    , .\o0$trdy (\in0up$trdy )
    , .\o1$irdy (\in0down$irdy )
    , .\o1$data (\in0down$data )
    , .\o1$trdy (\in0down$trdy )
  );
  
  \Queue  #(
    .NUM_DATA(0),
    .DATASIZE(2),
    .LENGTH(2)
  ) \Queue1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\channel5$irdy )
    , .\i0$data (\channel5$data )
    , .\i0$trdy (\channel5$trdy )
    , .\o0$irdy (\channel6$irdy )
    , .\o0$data (\channel6$data )
    , .\o0$trdy (\channel6$trdy )
  );
  
  \Merge2  #(
    .INPUTSIZE1(2),
    .OUTPUTSIZE(2),
    .INPUTSIZE0(2)
  ) \Merge1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\channel3$irdy )
    , .\i0$data (\channel3$data )
    , .\i0$trdy (\channel3$trdy )
    , .\i1$irdy (\channel4$irdy )
    , .\i1$data (\channel4$data )
    , .\i1$trdy (\channel4$trdy )
    , .\o0$irdy (\channel5$irdy )
    , .\o0$data (\channel5$data )
    , .\o0$trdy (\channel5$trdy )
    , .\f$data (\ofunchan_0_Merge1$data )
    , .\sel (\sel_Merge1 )
  );
  
  \OFUN_0$DFIFO_2_Merge1  \ofun_0_Merge1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\channel3$data )
    , .\i1$data (\channel4$data )
    , .\sel (\sel_Merge1 )
    , .\o0 (\ofunchan_0_Merge1$data )
  );
  
  \LoadBalancer2  #(
    .DATASIZE(2)
  ) \LoadBalancer4  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\channel10$irdy )
    , .\i0$data (\channel10$data )
    , .\i0$trdy (\channel10$trdy )
    , .\o0$irdy (\in1up$irdy )
    , .\o0$data (\in1up$data )
    , .\o0$trdy (\in1up$trdy )
    , .\o1$irdy (\in1down$irdy )
    , .\o1$data (\in1down$data )
    , .\o1$trdy (\in1down$trdy )
  );
  
  \Queue  #(
    .NUM_DATA(0),
    .DATASIZE(2),
    .LENGTH(2)
  ) \Queue2  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\channel9$irdy )
    , .\i0$data (\channel9$data )
    , .\i0$trdy (\channel9$trdy )
    , .\o0$irdy (\channel10$irdy )
    , .\o0$data (\channel10$data )
    , .\o0$trdy (\channel10$trdy )
  );
  
  \Merge2  #(
    .INPUTSIZE1(2),
    .OUTPUTSIZE(2),
    .INPUTSIZE0(2)
  ) \Merge2  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\channel7$irdy )
    , .\i0$data (\channel7$data )
    , .\i0$trdy (\channel7$trdy )
    , .\i1$irdy (\channel8$irdy )
    , .\i1$data (\channel8$data )
    , .\i1$trdy (\channel8$trdy )
    , .\o0$irdy (\channel9$irdy )
    , .\o0$data (\channel9$data )
    , .\o0$trdy (\channel9$trdy )
    , .\f$data (\ofunchan_0_Merge2$data )
    , .\sel (\sel_Merge2 )
  );
  
  \OFUN_0$DFIFO_2_Merge2  \ofun_0_Merge2  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\channel7$data )
    , .\i1$data (\channel8$data )
    , .\sel (\sel_Merge2 )
    , .\o0 (\ofunchan_0_Merge2$data )
  );
  
  \Merge2  #(
    .INPUTSIZE1(2),
    .OUTPUTSIZE(2),
    .INPUTSIZE0(2)
  ) \Merge3  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\channel11$irdy )
    , .\i0$data (\channel11$data )
    , .\i0$trdy (\channel11$trdy )
    , .\i1$irdy (\channel12$irdy )
    , .\i1$data (\channel12$data )
    , .\i1$trdy (\channel12$trdy )
    , .\o0$irdy (\bus_outs1$irdy )
    , .\o0$data (\bus_outs1$data )
    , .\o0$trdy (\bus_outs1$trdy )
    , .\f$data (\ofunchan_0_Merge3$data )
    , .\sel (\sel_Merge3 )
  );
  
  \OFUN_0$DFIFO_2_Merge3  \ofun_0_Merge3  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\channel11$data )
    , .\i1$data (\channel12$data )
    , .\sel (\sel_Merge3 )
    , .\o0 (\ofunchan_0_Merge3$data )
  );
  
  \Merge2  #(
    .INPUTSIZE1(2),
    .OUTPUTSIZE(2),
    .INPUTSIZE0(2)
  ) \Merge4  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\channel13$irdy )
    , .\i0$data (\channel13$data )
    , .\i0$trdy (\channel13$trdy )
    , .\i1$irdy (\channel14$irdy )
    , .\i1$data (\channel14$data )
    , .\i1$trdy (\channel14$trdy )
    , .\o0$irdy (\bus_outs2$irdy )
    , .\o0$data (\bus_outs2$data )
    , .\o0$trdy (\bus_outs2$trdy )
    , .\f$data (\ofunchan_0_Merge4$data )
    , .\sel (\sel_Merge4 )
  );
  
  \OFUN_0$DFIFO_2_Merge4  \ofun_0_Merge4  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\channel13$data )
    , .\i1$data (\channel14$data )
    , .\sel (\sel_Merge4 )
    , .\o0 (\ofunchan_0_Merge4$data )
  );
  
  \Latch$type7  \Latch1  (
      .\clk (\clk ), .\rst (\rst )
    , .\input$irdy (\bus_ins1$irdy )
    , .\input$data (\bus_ins1$data )
    , .\input$trdy (\bus_ins1$trdy )
    , .\output$irdy (\channel1$irdy )
    , .\output$data (\channel1$data )
    , .\output$trdy (\channel1$trdy )
  );
  
  \Latch$type4  \Latch2  (
      .\clk (\clk ), .\rst (\rst )
    , .\input$irdy (\bus_ins2$irdy )
    , .\input$data (\bus_ins2$data )
    , .\input$trdy (\bus_ins2$trdy )
    , .\output$irdy (\channel2$irdy )
    , .\output$data (\channel2$data )
    , .\output$trdy (\channel2$trdy )
  );
  
  \Latch$type7  \Latch3  (
      .\clk (\clk ), .\rst (\rst )
    , .\input$irdy (\toQueueUp1$irdy )
    , .\input$data (\toQueueUp1$data )
    , .\input$trdy (\toQueueUp1$trdy )
    , .\output$irdy (\channel3$irdy )
    , .\output$data (\channel3$data )
    , .\output$trdy (\channel3$trdy )
  );
  
  \Latch$type4  \Latch4  (
      .\clk (\clk ), .\rst (\rst )
    , .\input$irdy (\toQueueUp2$irdy )
    , .\input$data (\toQueueUp2$data )
    , .\input$trdy (\toQueueUp2$trdy )
    , .\output$irdy (\channel4$irdy )
    , .\output$data (\channel4$data )
    , .\output$trdy (\channel4$trdy )
  );
  
  \Latch$type7  \Latch5  (
      .\clk (\clk ), .\rst (\rst )
    , .\input$irdy (\toQueueDown1$irdy )
    , .\input$data (\toQueueDown1$data )
    , .\input$trdy (\toQueueDown1$trdy )
    , .\output$irdy (\channel7$irdy )
    , .\output$data (\channel7$data )
    , .\output$trdy (\channel7$trdy )
  );
  
  \Latch$type4  \Latch6  (
      .\clk (\clk ), .\rst (\rst )
    , .\input$irdy (\toQueueDown2$irdy )
    , .\input$data (\toQueueDown2$data )
    , .\input$trdy (\toQueueDown2$trdy )
    , .\output$irdy (\channel8$irdy )
    , .\output$data (\channel8$data )
    , .\output$trdy (\channel8$trdy )
  );
  
  \Latch$type4  \Latch7  (
      .\clk (\clk ), .\rst (\rst )
    , .\input$irdy (\in0up$irdy )
    , .\input$data (\in0up$data )
    , .\input$trdy (\in0up$trdy )
    , .\output$irdy (\channel11$irdy )
    , .\output$data (\channel11$data )
    , .\output$trdy (\channel11$trdy )
  );
  
  \Latch$type4  \Latch8  (
      .\clk (\clk ), .\rst (\rst )
    , .\input$irdy (\in1up$irdy )
    , .\input$data (\in1up$data )
    , .\input$trdy (\in1up$trdy )
    , .\output$irdy (\channel12$irdy )
    , .\output$data (\channel12$data )
    , .\output$trdy (\channel12$trdy )
  );
  
  \Latch$type4  \Latch9  (
      .\clk (\clk ), .\rst (\rst )
    , .\input$irdy (\in0down$irdy )
    , .\input$data (\in0down$data )
    , .\input$trdy (\in0down$trdy )
    , .\output$irdy (\channel13$irdy )
    , .\output$data (\channel13$data )
    , .\output$trdy (\channel13$trdy )
  );
  
  \Latch$type4  \Latch10  (
      .\clk (\clk ), .\rst (\rst )
    , .\input$irdy (\in1down$irdy )
    , .\input$data (\in1down$data )
    , .\input$trdy (\in1down$trdy )
    , .\output$irdy (\channel14$irdy )
    , .\output$data (\channel14$data )
    , .\output$trdy (\channel14$trdy )
  );
  
endmodule


//
// DFIFO_2 switch functions
//
module \OFUN_0$DFIFO_2_Merge1 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , input [1:0] \i1$data 
    , input \sel 
    , output [1:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[0:0] \f$bool$arg0$disj  = \sel  ;
  wire[0:0] \f$bool$arg0  = \f$bool$arg0$disj [0:0] ;
  wire[0:0] \f$bool$arg1  = 1'd0 ;
  wire \f$bool  = \f$bool$arg0  == \f$bool$arg1  ;
  wire[1:0] \f$true  = \i0$data  ;
  wire[0:0] \f$false$bool$arg0$disj  = \sel  ;
  wire[0:0] \f$false$bool$arg0  = \f$false$bool$arg0$disj [0:0] ;
  wire[0:0] \f$false$bool$arg1  = 1'd1 ;
  wire \f$false$bool  = \f$false$bool$arg0  == \f$false$bool$arg1  ;
  wire[1:0] \f$false$true  = \i1$data  ;
  wire[1:0] \f$false$false  = \i0$data  ;
  wire[1:0] \f$false  = ( \f$false$bool  ? \f$false$true  : \f$false$false  ) ;
  wire[1:0] \f  = ( \f$bool  ? \f$true  : \f$false  ) ;
  
  assign \o0  = \f  ;
endmodule

module \OFUN_0$DFIFO_2_Merge2 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , input [1:0] \i1$data 
    , input \sel 
    , output [1:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[0:0] \f$bool$arg0$disj  = \sel  ;
  wire[0:0] \f$bool$arg0  = \f$bool$arg0$disj [0:0] ;
  wire[0:0] \f$bool$arg1  = 1'd0 ;
  wire \f$bool  = \f$bool$arg0  == \f$bool$arg1  ;
  wire[1:0] \f$true  = \i0$data  ;
  wire[0:0] \f$false$bool$arg0$disj  = \sel  ;
  wire[0:0] \f$false$bool$arg0  = \f$false$bool$arg0$disj [0:0] ;
  wire[0:0] \f$false$bool$arg1  = 1'd1 ;
  wire \f$false$bool  = \f$false$bool$arg0  == \f$false$bool$arg1  ;
  wire[1:0] \f$false$true  = \i1$data  ;
  wire[1:0] \f$false$false  = \i0$data  ;
  wire[1:0] \f$false  = ( \f$false$bool  ? \f$false$true  : \f$false$false  ) ;
  wire[1:0] \f  = ( \f$bool  ? \f$true  : \f$false  ) ;
  
  assign \o0  = \f  ;
endmodule

module \OFUN_0$DFIFO_2_Merge3 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , input [1:0] \i1$data 
    , input \sel 
    , output [1:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[0:0] \f$bool$arg0$disj  = \sel  ;
  wire[0:0] \f$bool$arg0  = \f$bool$arg0$disj [0:0] ;
  wire[0:0] \f$bool$arg1  = 1'd0 ;
  wire \f$bool  = \f$bool$arg0  == \f$bool$arg1  ;
  wire[1:0] \f$true  = \i0$data  ;
  wire[0:0] \f$false$bool$arg0$disj  = \sel  ;
  wire[0:0] \f$false$bool$arg0  = \f$false$bool$arg0$disj [0:0] ;
  wire[0:0] \f$false$bool$arg1  = 1'd1 ;
  wire \f$false$bool  = \f$false$bool$arg0  == \f$false$bool$arg1  ;
  wire[1:0] \f$false$true  = \i1$data  ;
  wire[1:0] \f$false$false  = \i0$data  ;
  wire[1:0] \f$false  = ( \f$false$bool  ? \f$false$true  : \f$false$false  ) ;
  wire[1:0] \f  = ( \f$bool  ? \f$true  : \f$false  ) ;
  
  assign \o0  = \f  ;
endmodule

module \OFUN_0$DFIFO_2_Merge4 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , input [1:0] \i1$data 
    , input \sel 
    , output [1:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[0:0] \f$bool$arg0$disj  = \sel  ;
  wire[0:0] \f$bool$arg0  = \f$bool$arg0$disj [0:0] ;
  wire[0:0] \f$bool$arg1  = 1'd0 ;
  wire \f$bool  = \f$bool$arg0  == \f$bool$arg1  ;
  wire[1:0] \f$true  = \i0$data  ;
  wire[0:0] \f$false$bool$arg0$disj  = \sel  ;
  wire[0:0] \f$false$bool$arg0  = \f$false$bool$arg0$disj [0:0] ;
  wire[0:0] \f$false$bool$arg1  = 1'd1 ;
  wire \f$false$bool  = \f$false$bool$arg0  == \f$false$bool$arg1  ;
  wire[1:0] \f$false$true  = \i1$data  ;
  wire[1:0] \f$false$false  = \i0$data  ;
  wire[1:0] \f$false  = ( \f$false$bool  ? \f$false$true  : \f$false$false  ) ;
  wire[1:0] \f  = ( \f$bool  ? \f$true  : \f$false  ) ;
  
  assign \o0  = \f  ;
endmodule

module \RECEPTION_1_1_3_2 (
      input \clk , input \rst , input [63:0] \t 
    , input \input$irdy , input [1:0] \input$data , output \input$trdy 
    , output \bus_outs1$irdy , output [1:0] \bus_outs1$data , input \bus_outs1$trdy 
    , output \bus_outs2$irdy , output [1:0] \bus_outs2$data , input \bus_outs2$trdy 
    , output \bus_outs3$irdy , output [1:0] \bus_outs3$data , input \bus_outs3$trdy 
    , output \bus_outs4$irdy , output [0:0] \bus_outs4$data , input \bus_outs4$trdy 
    , input \CreditCounter1$PatientSource1$unbound_irdy 
    , input [0:0] \CreditCounter1$PatientSource1$unbound_data 
    , output \CreditCounter1$PatientSource1$trdy 
    , input \CreditCounter1$Sink1$unbound_trdy 
    , output \CreditCounter1$Sink1$irdy 
    , output [0:0] \CreditCounter1$Sink1$data 
  );
  
  //
  // Channel declarations
  //
  wire \noCONS$irdy  ;
  wire [1:0] \noCONS$data  ;
  wire \noCONS$trdy  ;
  wire \toRCP$irdy  ;
  wire [1:0] \toRCP$data  ;
  wire \toRCP$trdy  ;
  wire \creditBack$irdy  ;
  wire [1:0] \creditBack$data  ;
  wire \creditBack$trdy  ;
  wire \channel1$irdy  ;
  wire [1:0] \channel1$data  ;
  wire \channel1$trdy  ;
  
  //
  // Function Channels
  //
  wire \sfunchan_0_Switch1$data  ;
  wire [1:0] \ofunchan_1_Switch1$data  ;
  wire [1:0] \ofunchan_2_Switch1$data  ;
  wire \sfunchan_0_Switch2$data  ;
  wire [1:0] \ofunchan_1_Switch2$data  ;
  wire [1:0] \ofunchan_2_Switch2$data  ;
  
  //
  // Component and Macro instantiations
  //
  \Fork2  #(
    .DATASIZE(2)
  ) \Fork1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\channel1$irdy )
    , .\i0$data (\channel1$data )
    , .\i0$trdy (\channel1$trdy )
    , .\o0$irdy (\toRCP$irdy )
    , .\o0$data (\toRCP$data )
    , .\o0$trdy (\toRCP$trdy )
    , .\o1$irdy (\creditBack$irdy )
    , .\o1$data (\creditBack$data )
    , .\o1$trdy (\creditBack$trdy )
  );
  
  \Queue  #(
    .NUM_DATA(0),
    .DATASIZE(2),
    .LENGTH(2)
  ) \Queue1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\input$irdy )
    , .\i0$data (\input$data )
    , .\i0$trdy (\input$trdy )
    , .\o0$irdy (\channel1$irdy )
    , .\o0$data (\channel1$data )
    , .\o0$trdy (\channel1$trdy )
  );
  
  \Switch2  #(
    .OUTPUTSIZE0(2),
    .OUTPUTSIZE1(2),
    .INPUTSIZE(2)
  ) \Switch1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\toRCP$irdy )
    , .\i0$data (\toRCP$data )
    , .\i0$trdy (\toRCP$trdy )
    , .\o0$irdy (\bus_outs1$irdy )
    , .\o0$data (\bus_outs1$data )
    , .\o0$trdy (\bus_outs1$trdy )
    , .\o1$irdy (\noCONS$irdy )
    , .\o1$data (\noCONS$data )
    , .\o1$trdy (\noCONS$trdy )
    , .\sel$data (\sfunchan_0_Switch1$data )
    , .\f0$data (\ofunchan_1_Switch1$data )
    , .\f1$data (\ofunchan_2_Switch1$data )
  );
  
  \SFUN_0$RECEPTION_1_1_3_2_Switch1  \sfun_0_Switch1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\toRCP$data )
    , .\o0 (\sfunchan_0_Switch1$data )
  );
  
  \OFUN_1$RECEPTION_1_1_3_2_Switch1  \ofun_1_Switch1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\toRCP$data )
    , .\o0 (\ofunchan_1_Switch1$data )
  );
  
  \OFUN_2$RECEPTION_1_1_3_2_Switch1  \ofun_2_Switch1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\toRCP$data )
    , .\o0 (\ofunchan_2_Switch1$data )
  );
  
  \Switch2  #(
    .OUTPUTSIZE0(2),
    .OUTPUTSIZE1(2),
    .INPUTSIZE(2)
  ) \Switch2  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\noCONS$irdy )
    , .\i0$data (\noCONS$data )
    , .\i0$trdy (\noCONS$trdy )
    , .\o0$irdy (\bus_outs2$irdy )
    , .\o0$data (\bus_outs2$data )
    , .\o0$trdy (\bus_outs2$trdy )
    , .\o1$irdy (\bus_outs3$irdy )
    , .\o1$data (\bus_outs3$data )
    , .\o1$trdy (\bus_outs3$trdy )
    , .\sel$data (\sfunchan_0_Switch2$data )
    , .\f0$data (\ofunchan_1_Switch2$data )
    , .\f1$data (\ofunchan_2_Switch2$data )
  );
  
  \SFUN_0$RECEPTION_1_1_3_2_Switch2  \sfun_0_Switch2  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\noCONS$data )
    , .\o0 (\sfunchan_0_Switch2$data )
  );
  
  \OFUN_1$RECEPTION_1_1_3_2_Switch2  \ofun_1_Switch2  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\noCONS$data )
    , .\o0 (\ofunchan_1_Switch2$data )
  );
  
  \OFUN_2$RECEPTION_1_1_3_2_Switch2  \ofun_2_Switch2  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\noCONS$data )
    , .\o0 (\ofunchan_2_Switch2$data )
  );
  
  \CreditCounter_2  \CreditCounter1  (
      .\clk (\clk ), .\rst (\rst ), .\t (\t )
    , .\i$irdy (\creditBack$irdy )
    , .\i$data (\creditBack$data )
    , .\i$trdy (\creditBack$trdy )
    , .\o$irdy (\bus_outs4$irdy )
    , .\o$data (\bus_outs4$data )
    , .\o$trdy (\bus_outs4$trdy )
    , .\PatientSource1$unbound_irdy (\CreditCounter1$PatientSource1$unbound_irdy )
    , .\PatientSource1$unbound_data (\CreditCounter1$PatientSource1$unbound_data )
    , .\PatientSource1$trdy (\CreditCounter1$PatientSource1$trdy )
    , .\Sink1$unbound_trdy (\CreditCounter1$Sink1$unbound_trdy )
    , .\Sink1$irdy (\CreditCounter1$Sink1$irdy )
    , .\Sink1$data (\CreditCounter1$Sink1$data )
  );
  
endmodule


//
// RECEPTION_1_1_3_2 switch functions
//
module \SFUN_0$RECEPTION_1_1_3_2_Switch1 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , output [0:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[1:0] \f$bool$g0  = \i0$data  ;
  wire[1:0] \f$bool$f$arg0$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$arg0$arg0$conj  = \f$bool$f$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$arg0$arg0  = \f$bool$f$arg0$arg0$conj [1:1] ;
  wire[0:0] \f$bool$f$arg0$arg1  = 1'd1 ;
  wire \f$bool$f$arg0  = \f$bool$f$arg0$arg0  == \f$bool$f$arg0$arg1  ;
  wire[1:0] \f$bool$f$arg1$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$arg1$arg0$conj  = \f$bool$f$arg1$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$arg1$arg0  = \f$bool$f$arg1$arg0$conj [0:0] ;
  wire[0:0] \f$bool$f$arg1$arg1  = 1'd1 ;
  wire \f$bool$f$arg1  = \f$bool$f$arg1$arg0  == \f$bool$f$arg1$arg1  ;
  wire \f$bool$f  = \f$bool$f$arg0  && \f$bool$f$arg1  ;
  wire \f$bool  = \f$bool$f  ;
  wire[0:0] \f$true$content  = 1'd0 ;
  wire[0:0] \f$true  = \f$true$content  ;
  wire[1:0] \f$false$bool$g0  = \i0$data  ;
  wire[1:0] \f$false$bool$f$arg0$arg0$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$arg0$arg0$conj  = \f$false$bool$f$arg0$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$arg0$arg0  = \f$false$bool$f$arg0$arg0$arg0$conj [1:1] ;
  wire[0:0] \f$false$bool$f$arg0$arg0$arg1  = 1'd1 ;
  wire \f$false$bool$f$arg0$arg0  = \f$false$bool$f$arg0$arg0$arg0  == \f$false$bool$f$arg0$arg0$arg1  ;
  wire[1:0] \f$false$bool$f$arg0$arg1$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$arg1$arg0$conj  = \f$false$bool$f$arg0$arg1$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$arg1$arg0  = \f$false$bool$f$arg0$arg1$arg0$conj [0:0] ;
  wire[0:0] \f$false$bool$f$arg0$arg1$arg1  = 1'd1 ;
  wire \f$false$bool$f$arg0$arg1  = \f$false$bool$f$arg0$arg1$arg0  == \f$false$bool$f$arg0$arg1$arg1  ;
  wire \f$false$bool$f$arg0  = \f$false$bool$f$arg0$arg0  && \f$false$bool$f$arg0$arg1  ;
  wire \f$false$bool$f  = !\f$false$bool$f$arg0  ;
  wire \f$false$bool  = \f$false$bool$f  ;
  wire[0:0] \f$false$true$content  = 1'd1 ;
  wire[0:0] \f$false$true  = \f$false$true$content  ;
  wire[0:0] \f$false$false$content  = 1'd0 ;
  wire[0:0] \f$false$false  = \f$false$false$content  ;
  wire[0:0] \f$false  = ( \f$false$bool  ? \f$false$true  : \f$false$false  ) ;
  wire[0:0] \f  = ( \f$bool  ? \f$true  : \f$false  ) ;
  
  assign \o0  = \f  ;
endmodule

module \OFUN_1$RECEPTION_1_1_3_2_Switch1 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , output [1:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[1:0] \f  = \i0$data  ;
  
  assign \o0  = \f  ;
endmodule

module \OFUN_2$RECEPTION_1_1_3_2_Switch1 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , output [1:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[1:0] \f  = \i0$data  ;
  
  assign \o0  = \f  ;
endmodule

module \SFUN_0$RECEPTION_1_1_3_2_Switch2 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , output [0:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[1:0] \f$bool$g0  = \i0$data  ;
  wire \f$bool$f$bool  = 1'd0 ;
  wire[1:0] \f$bool$f$true$arg0$arg0$arg0$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$true$arg0$arg0$arg0$arg0$conj  = \f$bool$f$true$arg0$arg0$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$true$arg0$arg0$arg0$arg0  = \f$bool$f$true$arg0$arg0$arg0$arg0$conj [1:1] ;
  wire[0:0] \f$bool$f$true$arg0$arg0$arg0$arg1  = 1'd1 ;
  wire \f$bool$f$true$arg0$arg0$arg0  = \f$bool$f$true$arg0$arg0$arg0$arg0  == \f$bool$f$true$arg0$arg0$arg0$arg1  ;
  wire \f$bool$f$true$arg0$arg0  = !\f$bool$f$true$arg0$arg0$arg0  ;
  wire[1:0] \f$bool$f$true$arg0$arg1$arg0$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$true$arg0$arg1$arg0$arg0$conj  = \f$bool$f$true$arg0$arg1$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$true$arg0$arg1$arg0$arg0  = \f$bool$f$true$arg0$arg1$arg0$arg0$conj [1:1] ;
  wire[0:0] \f$bool$f$true$arg0$arg1$arg0$arg1  = 1'd1 ;
  wire \f$bool$f$true$arg0$arg1$arg0  = \f$bool$f$true$arg0$arg1$arg0$arg0  > \f$bool$f$true$arg0$arg1$arg0$arg1  ;
  wire \f$bool$f$true$arg0$arg1  = !\f$bool$f$true$arg0$arg1$arg0  ;
  wire \f$bool$f$true$arg0  = \f$bool$f$true$arg0$arg0  && \f$bool$f$true$arg0$arg1  ;
  wire \f$bool$f$true$arg1  = 1'd0 ;
  wire \f$bool$f$true  = \f$bool$f$true$arg0  || \f$bool$f$true$arg1  ;
  wire \f$bool$f$false$bool  = 1'd0 ;
  wire[1:0] \f$bool$f$false$true$arg0$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$false$true$arg0$arg0$conj  = \f$bool$f$false$true$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$false$true$arg0$arg0  = \f$bool$f$false$true$arg0$arg0$conj [1:1] ;
  wire[0:0] \f$bool$f$false$true$arg0$arg1  = 1'd1 ;
  wire \f$bool$f$false$true$arg0  = \f$bool$f$false$true$arg0$arg0  > \f$bool$f$false$true$arg0$arg1  ;
  wire \f$bool$f$false$true$arg1$arg0  = 1'd1 ;
  wire[1:0] \f$bool$f$false$true$arg1$arg1$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$false$true$arg1$arg1$arg0$conj  = \f$bool$f$false$true$arg1$arg1$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$false$true$arg1$arg1$arg0  = \f$bool$f$false$true$arg1$arg1$arg0$conj [1:1] ;
  wire[0:0] \f$bool$f$false$true$arg1$arg1$arg1  = 1'd0 ;
  wire \f$bool$f$false$true$arg1$arg1  = \f$bool$f$false$true$arg1$arg1$arg0  == \f$bool$f$false$true$arg1$arg1$arg1  ;
  wire \f$bool$f$false$true$arg1  = \f$bool$f$false$true$arg1$arg0  && \f$bool$f$false$true$arg1$arg1  ;
  wire \f$bool$f$false$true  = \f$bool$f$false$true$arg0  || \f$bool$f$false$true$arg1  ;
  wire \f$bool$f$false$false$bool  = 1'd0 ;
  wire[1:0] \f$bool$f$false$false$true$arg0$arg0$arg0$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$false$false$true$arg0$arg0$arg0$arg0$conj  = \f$bool$f$false$false$true$arg0$arg0$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$false$false$true$arg0$arg0$arg0$arg0  = \f$bool$f$false$false$true$arg0$arg0$arg0$arg0$conj [0:0] ;
  wire[0:0] \f$bool$f$false$false$true$arg0$arg0$arg0$arg1  = 1'd1 ;
  wire \f$bool$f$false$false$true$arg0$arg0$arg0  = \f$bool$f$false$false$true$arg0$arg0$arg0$arg0  == \f$bool$f$false$false$true$arg0$arg0$arg0$arg1  ;
  wire \f$bool$f$false$false$true$arg0$arg0  = !\f$bool$f$false$false$true$arg0$arg0$arg0  ;
  wire[1:0] \f$bool$f$false$false$true$arg0$arg1$arg0$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$false$false$true$arg0$arg1$arg0$arg0$conj  = \f$bool$f$false$false$true$arg0$arg1$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$false$false$true$arg0$arg1$arg0$arg0  = \f$bool$f$false$false$true$arg0$arg1$arg0$arg0$conj [0:0] ;
  wire[0:0] \f$bool$f$false$false$true$arg0$arg1$arg0$arg1  = 1'd1 ;
  wire \f$bool$f$false$false$true$arg0$arg1$arg0  = \f$bool$f$false$false$true$arg0$arg1$arg0$arg0  > \f$bool$f$false$false$true$arg0$arg1$arg0$arg1  ;
  wire \f$bool$f$false$false$true$arg0$arg1  = !\f$bool$f$false$false$true$arg0$arg1$arg0  ;
  wire \f$bool$f$false$false$true$arg0  = \f$bool$f$false$false$true$arg0$arg0  && \f$bool$f$false$false$true$arg0$arg1  ;
  wire \f$bool$f$false$false$true$arg1  = 1'd0 ;
  wire \f$bool$f$false$false$true  = \f$bool$f$false$false$true$arg0  || \f$bool$f$false$false$true$arg1  ;
  wire[1:0] \f$bool$f$false$false$false$arg0$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$false$false$false$arg0$arg0$conj  = \f$bool$f$false$false$false$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$false$false$false$arg0$arg0  = \f$bool$f$false$false$false$arg0$arg0$conj [0:0] ;
  wire[0:0] \f$bool$f$false$false$false$arg0$arg1  = 1'd1 ;
  wire \f$bool$f$false$false$false$arg0  = \f$bool$f$false$false$false$arg0$arg0  > \f$bool$f$false$false$false$arg0$arg1  ;
  wire \f$bool$f$false$false$false$arg1$arg0  = 1'd1 ;
  wire[1:0] \f$bool$f$false$false$false$arg1$arg1$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$false$false$false$arg1$arg1$arg0$conj  = \f$bool$f$false$false$false$arg1$arg1$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$false$false$false$arg1$arg1$arg0  = \f$bool$f$false$false$false$arg1$arg1$arg0$conj [0:0] ;
  wire[0:0] \f$bool$f$false$false$false$arg1$arg1$arg1  = 1'd0 ;
  wire \f$bool$f$false$false$false$arg1$arg1  = \f$bool$f$false$false$false$arg1$arg1$arg0  == \f$bool$f$false$false$false$arg1$arg1$arg1  ;
  wire \f$bool$f$false$false$false$arg1  = \f$bool$f$false$false$false$arg1$arg0  && \f$bool$f$false$false$false$arg1$arg1  ;
  wire \f$bool$f$false$false$false  = \f$bool$f$false$false$false$arg0  || \f$bool$f$false$false$false$arg1  ;
  wire \f$bool$f$false$false  = ( \f$bool$f$false$false$bool  ? \f$bool$f$false$false$true  : \f$bool$f$false$false$false  ) ;
  wire \f$bool$f$false  = ( \f$bool$f$false$bool  ? \f$bool$f$false$true  : \f$bool$f$false$false  ) ;
  wire \f$bool$f  = ( \f$bool$f$bool  ? \f$bool$f$true  : \f$bool$f$false  ) ;
  wire \f$bool  = \f$bool$f  ;
  wire[0:0] \f$true$content  = 1'd0 ;
  wire[0:0] \f$true  = \f$true$content  ;
  wire[1:0] \f$false$bool$g0  = \i0$data  ;
  wire \f$false$bool$f$arg0$bool  = 1'd0 ;
  wire[1:0] \f$false$bool$f$arg0$true$arg0$arg0$arg0$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$true$arg0$arg0$arg0$arg0$conj  = \f$false$bool$f$arg0$true$arg0$arg0$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$true$arg0$arg0$arg0$arg0  = \f$false$bool$f$arg0$true$arg0$arg0$arg0$arg0$conj [1:1] ;
  wire[0:0] \f$false$bool$f$arg0$true$arg0$arg0$arg0$arg1  = 1'd1 ;
  wire \f$false$bool$f$arg0$true$arg0$arg0$arg0  = \f$false$bool$f$arg0$true$arg0$arg0$arg0$arg0  == \f$false$bool$f$arg0$true$arg0$arg0$arg0$arg1  ;
  wire \f$false$bool$f$arg0$true$arg0$arg0  = !\f$false$bool$f$arg0$true$arg0$arg0$arg0  ;
  wire[1:0] \f$false$bool$f$arg0$true$arg0$arg1$arg0$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$true$arg0$arg1$arg0$arg0$conj  = \f$false$bool$f$arg0$true$arg0$arg1$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$true$arg0$arg1$arg0$arg0  = \f$false$bool$f$arg0$true$arg0$arg1$arg0$arg0$conj [1:1] ;
  wire[0:0] \f$false$bool$f$arg0$true$arg0$arg1$arg0$arg1  = 1'd1 ;
  wire \f$false$bool$f$arg0$true$arg0$arg1$arg0  = \f$false$bool$f$arg0$true$arg0$arg1$arg0$arg0  > \f$false$bool$f$arg0$true$arg0$arg1$arg0$arg1  ;
  wire \f$false$bool$f$arg0$true$arg0$arg1  = !\f$false$bool$f$arg0$true$arg0$arg1$arg0  ;
  wire \f$false$bool$f$arg0$true$arg0  = \f$false$bool$f$arg0$true$arg0$arg0  && \f$false$bool$f$arg0$true$arg0$arg1  ;
  wire \f$false$bool$f$arg0$true$arg1  = 1'd0 ;
  wire \f$false$bool$f$arg0$true  = \f$false$bool$f$arg0$true$arg0  || \f$false$bool$f$arg0$true$arg1  ;
  wire \f$false$bool$f$arg0$false$bool  = 1'd0 ;
  wire[1:0] \f$false$bool$f$arg0$false$true$arg0$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$false$true$arg0$arg0$conj  = \f$false$bool$f$arg0$false$true$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$false$true$arg0$arg0  = \f$false$bool$f$arg0$false$true$arg0$arg0$conj [1:1] ;
  wire[0:0] \f$false$bool$f$arg0$false$true$arg0$arg1  = 1'd1 ;
  wire \f$false$bool$f$arg0$false$true$arg0  = \f$false$bool$f$arg0$false$true$arg0$arg0  > \f$false$bool$f$arg0$false$true$arg0$arg1  ;
  wire \f$false$bool$f$arg0$false$true$arg1$arg0  = 1'd1 ;
  wire[1:0] \f$false$bool$f$arg0$false$true$arg1$arg1$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$false$true$arg1$arg1$arg0$conj  = \f$false$bool$f$arg0$false$true$arg1$arg1$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$false$true$arg1$arg1$arg0  = \f$false$bool$f$arg0$false$true$arg1$arg1$arg0$conj [1:1] ;
  wire[0:0] \f$false$bool$f$arg0$false$true$arg1$arg1$arg1  = 1'd0 ;
  wire \f$false$bool$f$arg0$false$true$arg1$arg1  = \f$false$bool$f$arg0$false$true$arg1$arg1$arg0  == \f$false$bool$f$arg0$false$true$arg1$arg1$arg1  ;
  wire \f$false$bool$f$arg0$false$true$arg1  = \f$false$bool$f$arg0$false$true$arg1$arg0  && \f$false$bool$f$arg0$false$true$arg1$arg1  ;
  wire \f$false$bool$f$arg0$false$true  = \f$false$bool$f$arg0$false$true$arg0  || \f$false$bool$f$arg0$false$true$arg1  ;
  wire \f$false$bool$f$arg0$false$false$bool  = 1'd0 ;
  wire[1:0] \f$false$bool$f$arg0$false$false$true$arg0$arg0$arg0$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$false$false$true$arg0$arg0$arg0$arg0$conj  = \f$false$bool$f$arg0$false$false$true$arg0$arg0$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$false$false$true$arg0$arg0$arg0$arg0  = \f$false$bool$f$arg0$false$false$true$arg0$arg0$arg0$arg0$conj [0:0] ;
  wire[0:0] \f$false$bool$f$arg0$false$false$true$arg0$arg0$arg0$arg1  = 1'd1 ;
  wire \f$false$bool$f$arg0$false$false$true$arg0$arg0$arg0  = \f$false$bool$f$arg0$false$false$true$arg0$arg0$arg0$arg0  == \f$false$bool$f$arg0$false$false$true$arg0$arg0$arg0$arg1  ;
  wire \f$false$bool$f$arg0$false$false$true$arg0$arg0  = !\f$false$bool$f$arg0$false$false$true$arg0$arg0$arg0  ;
  wire[1:0] \f$false$bool$f$arg0$false$false$true$arg0$arg1$arg0$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$false$false$true$arg0$arg1$arg0$arg0$conj  = \f$false$bool$f$arg0$false$false$true$arg0$arg1$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$false$false$true$arg0$arg1$arg0$arg0  = \f$false$bool$f$arg0$false$false$true$arg0$arg1$arg0$arg0$conj [0:0] ;
  wire[0:0] \f$false$bool$f$arg0$false$false$true$arg0$arg1$arg0$arg1  = 1'd1 ;
  wire \f$false$bool$f$arg0$false$false$true$arg0$arg1$arg0  = \f$false$bool$f$arg0$false$false$true$arg0$arg1$arg0$arg0  > \f$false$bool$f$arg0$false$false$true$arg0$arg1$arg0$arg1  ;
  wire \f$false$bool$f$arg0$false$false$true$arg0$arg1  = !\f$false$bool$f$arg0$false$false$true$arg0$arg1$arg0  ;
  wire \f$false$bool$f$arg0$false$false$true$arg0  = \f$false$bool$f$arg0$false$false$true$arg0$arg0  && \f$false$bool$f$arg0$false$false$true$arg0$arg1  ;
  wire \f$false$bool$f$arg0$false$false$true$arg1  = 1'd0 ;
  wire \f$false$bool$f$arg0$false$false$true  = \f$false$bool$f$arg0$false$false$true$arg0  || \f$false$bool$f$arg0$false$false$true$arg1  ;
  wire[1:0] \f$false$bool$f$arg0$false$false$false$arg0$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$false$false$false$arg0$arg0$conj  = \f$false$bool$f$arg0$false$false$false$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$false$false$false$arg0$arg0  = \f$false$bool$f$arg0$false$false$false$arg0$arg0$conj [0:0] ;
  wire[0:0] \f$false$bool$f$arg0$false$false$false$arg0$arg1  = 1'd1 ;
  wire \f$false$bool$f$arg0$false$false$false$arg0  = \f$false$bool$f$arg0$false$false$false$arg0$arg0  > \f$false$bool$f$arg0$false$false$false$arg0$arg1  ;
  wire \f$false$bool$f$arg0$false$false$false$arg1$arg0  = 1'd1 ;
  wire[1:0] \f$false$bool$f$arg0$false$false$false$arg1$arg1$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$false$false$false$arg1$arg1$arg0$conj  = \f$false$bool$f$arg0$false$false$false$arg1$arg1$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$false$false$false$arg1$arg1$arg0  = \f$false$bool$f$arg0$false$false$false$arg1$arg1$arg0$conj [0:0] ;
  wire[0:0] \f$false$bool$f$arg0$false$false$false$arg1$arg1$arg1  = 1'd0 ;
  wire \f$false$bool$f$arg0$false$false$false$arg1$arg1  = \f$false$bool$f$arg0$false$false$false$arg1$arg1$arg0  == \f$false$bool$f$arg0$false$false$false$arg1$arg1$arg1  ;
  wire \f$false$bool$f$arg0$false$false$false$arg1  = \f$false$bool$f$arg0$false$false$false$arg1$arg0  && \f$false$bool$f$arg0$false$false$false$arg1$arg1  ;
  wire \f$false$bool$f$arg0$false$false$false  = \f$false$bool$f$arg0$false$false$false$arg0  || \f$false$bool$f$arg0$false$false$false$arg1  ;
  wire \f$false$bool$f$arg0$false$false  = ( \f$false$bool$f$arg0$false$false$bool  ? \f$false$bool$f$arg0$false$false$true  : \f$false$bool$f$arg0$false$false$false  ) ;
  wire \f$false$bool$f$arg0$false  = ( \f$false$bool$f$arg0$false$bool  ? \f$false$bool$f$arg0$false$true  : \f$false$bool$f$arg0$false$false  ) ;
  wire \f$false$bool$f$arg0  = ( \f$false$bool$f$arg0$bool  ? \f$false$bool$f$arg0$true  : \f$false$bool$f$arg0$false  ) ;
  wire \f$false$bool$f  = !\f$false$bool$f$arg0  ;
  wire \f$false$bool  = \f$false$bool$f  ;
  wire[0:0] \f$false$true$content  = 1'd1 ;
  wire[0:0] \f$false$true  = \f$false$true$content  ;
  wire[0:0] \f$false$false$content  = 1'd0 ;
  wire[0:0] \f$false$false  = \f$false$false$content  ;
  wire[0:0] \f$false  = ( \f$false$bool  ? \f$false$true  : \f$false$false  ) ;
  wire[0:0] \f  = ( \f$bool  ? \f$true  : \f$false  ) ;
  
  assign \o0  = \f  ;
endmodule

module \OFUN_1$RECEPTION_1_1_3_2_Switch2 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , output [1:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[1:0] \f  = \i0$data  ;
  
  assign \o0  = \f  ;
endmodule

module \OFUN_2$RECEPTION_1_1_3_2_Switch2 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , output [1:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[1:0] \f  = \i0$data  ;
  
  assign \o0  = \f  ;
endmodule

module \RECEPTION_1_1_2_2 (
      input \clk , input \rst , input [63:0] \t 
    , input \input$irdy , input [1:0] \input$data , output \input$trdy 
    , output \bus_outs1$irdy , output [1:0] \bus_outs1$data , input \bus_outs1$trdy 
    , output \bus_outs2$irdy , output [1:0] \bus_outs2$data , input \bus_outs2$trdy 
    , output \bus_outs3$irdy , output [1:0] \bus_outs3$data , input \bus_outs3$trdy 
    , output \bus_outs4$irdy , output [0:0] \bus_outs4$data , input \bus_outs4$trdy 
    , input \CreditCounter1$PatientSource1$unbound_irdy 
    , input [0:0] \CreditCounter1$PatientSource1$unbound_data 
    , output \CreditCounter1$PatientSource1$trdy 
    , input \CreditCounter1$Sink1$unbound_trdy 
    , output \CreditCounter1$Sink1$irdy 
    , output [0:0] \CreditCounter1$Sink1$data 
  );
  
  //
  // Channel declarations
  //
  wire \noCONS$irdy  ;
  wire [1:0] \noCONS$data  ;
  wire \noCONS$trdy  ;
  wire \toRCP$irdy  ;
  wire [1:0] \toRCP$data  ;
  wire \toRCP$trdy  ;
  wire \creditBack$irdy  ;
  wire [1:0] \creditBack$data  ;
  wire \creditBack$trdy  ;
  wire \channel1$irdy  ;
  wire [1:0] \channel1$data  ;
  wire \channel1$trdy  ;
  
  //
  // Function Channels
  //
  wire \sfunchan_0_Switch1$data  ;
  wire [1:0] \ofunchan_1_Switch1$data  ;
  wire [1:0] \ofunchan_2_Switch1$data  ;
  wire \sfunchan_0_Switch2$data  ;
  wire [1:0] \ofunchan_1_Switch2$data  ;
  wire [1:0] \ofunchan_2_Switch2$data  ;
  
  //
  // Component and Macro instantiations
  //
  \Fork2  #(
    .DATASIZE(2)
  ) \Fork1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\channel1$irdy )
    , .\i0$data (\channel1$data )
    , .\i0$trdy (\channel1$trdy )
    , .\o0$irdy (\toRCP$irdy )
    , .\o0$data (\toRCP$data )
    , .\o0$trdy (\toRCP$trdy )
    , .\o1$irdy (\creditBack$irdy )
    , .\o1$data (\creditBack$data )
    , .\o1$trdy (\creditBack$trdy )
  );
  
  \Queue  #(
    .NUM_DATA(0),
    .DATASIZE(2),
    .LENGTH(2)
  ) \Queue1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\input$irdy )
    , .\i0$data (\input$data )
    , .\i0$trdy (\input$trdy )
    , .\o0$irdy (\channel1$irdy )
    , .\o0$data (\channel1$data )
    , .\o0$trdy (\channel1$trdy )
  );
  
  \Switch2  #(
    .OUTPUTSIZE0(2),
    .OUTPUTSIZE1(2),
    .INPUTSIZE(2)
  ) \Switch1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\toRCP$irdy )
    , .\i0$data (\toRCP$data )
    , .\i0$trdy (\toRCP$trdy )
    , .\o0$irdy (\bus_outs1$irdy )
    , .\o0$data (\bus_outs1$data )
    , .\o0$trdy (\bus_outs1$trdy )
    , .\o1$irdy (\noCONS$irdy )
    , .\o1$data (\noCONS$data )
    , .\o1$trdy (\noCONS$trdy )
    , .\sel$data (\sfunchan_0_Switch1$data )
    , .\f0$data (\ofunchan_1_Switch1$data )
    , .\f1$data (\ofunchan_2_Switch1$data )
  );
  
  \SFUN_0$RECEPTION_1_1_2_2_Switch1  \sfun_0_Switch1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\toRCP$data )
    , .\o0 (\sfunchan_0_Switch1$data )
  );
  
  \OFUN_1$RECEPTION_1_1_2_2_Switch1  \ofun_1_Switch1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\toRCP$data )
    , .\o0 (\ofunchan_1_Switch1$data )
  );
  
  \OFUN_2$RECEPTION_1_1_2_2_Switch1  \ofun_2_Switch1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\toRCP$data )
    , .\o0 (\ofunchan_2_Switch1$data )
  );
  
  \Switch2  #(
    .OUTPUTSIZE0(2),
    .OUTPUTSIZE1(2),
    .INPUTSIZE(2)
  ) \Switch2  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\noCONS$irdy )
    , .\i0$data (\noCONS$data )
    , .\i0$trdy (\noCONS$trdy )
    , .\o0$irdy (\bus_outs2$irdy )
    , .\o0$data (\bus_outs2$data )
    , .\o0$trdy (\bus_outs2$trdy )
    , .\o1$irdy (\bus_outs3$irdy )
    , .\o1$data (\bus_outs3$data )
    , .\o1$trdy (\bus_outs3$trdy )
    , .\sel$data (\sfunchan_0_Switch2$data )
    , .\f0$data (\ofunchan_1_Switch2$data )
    , .\f1$data (\ofunchan_2_Switch2$data )
  );
  
  \SFUN_0$RECEPTION_1_1_2_2_Switch2  \sfun_0_Switch2  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\noCONS$data )
    , .\o0 (\sfunchan_0_Switch2$data )
  );
  
  \OFUN_1$RECEPTION_1_1_2_2_Switch2  \ofun_1_Switch2  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\noCONS$data )
    , .\o0 (\ofunchan_1_Switch2$data )
  );
  
  \OFUN_2$RECEPTION_1_1_2_2_Switch2  \ofun_2_Switch2  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\noCONS$data )
    , .\o0 (\ofunchan_2_Switch2$data )
  );
  
  \CreditCounter_2  \CreditCounter1  (
      .\clk (\clk ), .\rst (\rst ), .\t (\t )
    , .\i$irdy (\creditBack$irdy )
    , .\i$data (\creditBack$data )
    , .\i$trdy (\creditBack$trdy )
    , .\o$irdy (\bus_outs4$irdy )
    , .\o$data (\bus_outs4$data )
    , .\o$trdy (\bus_outs4$trdy )
    , .\PatientSource1$unbound_irdy (\CreditCounter1$PatientSource1$unbound_irdy )
    , .\PatientSource1$unbound_data (\CreditCounter1$PatientSource1$unbound_data )
    , .\PatientSource1$trdy (\CreditCounter1$PatientSource1$trdy )
    , .\Sink1$unbound_trdy (\CreditCounter1$Sink1$unbound_trdy )
    , .\Sink1$irdy (\CreditCounter1$Sink1$irdy )
    , .\Sink1$data (\CreditCounter1$Sink1$data )
  );
  
endmodule


//
// RECEPTION_1_1_2_2 switch functions
//
module \SFUN_0$RECEPTION_1_1_2_2_Switch1 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , output [0:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[1:0] \f$bool$g0  = \i0$data  ;
  wire[1:0] \f$bool$f$arg0$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$arg0$arg0$conj  = \f$bool$f$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$arg0$arg0  = \f$bool$f$arg0$arg0$conj [1:1] ;
  wire[0:0] \f$bool$f$arg0$arg1  = 1'd1 ;
  wire \f$bool$f$arg0  = \f$bool$f$arg0$arg0  == \f$bool$f$arg0$arg1  ;
  wire[1:0] \f$bool$f$arg1$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$arg1$arg0$conj  = \f$bool$f$arg1$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$arg1$arg0  = \f$bool$f$arg1$arg0$conj [0:0] ;
  wire[0:0] \f$bool$f$arg1$arg1  = 1'd1 ;
  wire \f$bool$f$arg1  = \f$bool$f$arg1$arg0  == \f$bool$f$arg1$arg1  ;
  wire \f$bool$f  = \f$bool$f$arg0  && \f$bool$f$arg1  ;
  wire \f$bool  = \f$bool$f  ;
  wire[0:0] \f$true$content  = 1'd0 ;
  wire[0:0] \f$true  = \f$true$content  ;
  wire[1:0] \f$false$bool$g0  = \i0$data  ;
  wire[1:0] \f$false$bool$f$arg0$arg0$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$arg0$arg0$conj  = \f$false$bool$f$arg0$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$arg0$arg0  = \f$false$bool$f$arg0$arg0$arg0$conj [1:1] ;
  wire[0:0] \f$false$bool$f$arg0$arg0$arg1  = 1'd1 ;
  wire \f$false$bool$f$arg0$arg0  = \f$false$bool$f$arg0$arg0$arg0  == \f$false$bool$f$arg0$arg0$arg1  ;
  wire[1:0] \f$false$bool$f$arg0$arg1$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$arg1$arg0$conj  = \f$false$bool$f$arg0$arg1$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$arg1$arg0  = \f$false$bool$f$arg0$arg1$arg0$conj [0:0] ;
  wire[0:0] \f$false$bool$f$arg0$arg1$arg1  = 1'd1 ;
  wire \f$false$bool$f$arg0$arg1  = \f$false$bool$f$arg0$arg1$arg0  == \f$false$bool$f$arg0$arg1$arg1  ;
  wire \f$false$bool$f$arg0  = \f$false$bool$f$arg0$arg0  && \f$false$bool$f$arg0$arg1  ;
  wire \f$false$bool$f  = !\f$false$bool$f$arg0  ;
  wire \f$false$bool  = \f$false$bool$f  ;
  wire[0:0] \f$false$true$content  = 1'd1 ;
  wire[0:0] \f$false$true  = \f$false$true$content  ;
  wire[0:0] \f$false$false$content  = 1'd0 ;
  wire[0:0] \f$false$false  = \f$false$false$content  ;
  wire[0:0] \f$false  = ( \f$false$bool  ? \f$false$true  : \f$false$false  ) ;
  wire[0:0] \f  = ( \f$bool  ? \f$true  : \f$false  ) ;
  
  assign \o0  = \f  ;
endmodule

module \OFUN_1$RECEPTION_1_1_2_2_Switch1 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , output [1:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[1:0] \f  = \i0$data  ;
  
  assign \o0  = \f  ;
endmodule

module \OFUN_2$RECEPTION_1_1_2_2_Switch1 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , output [1:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[1:0] \f  = \i0$data  ;
  
  assign \o0  = \f  ;
endmodule

module \SFUN_0$RECEPTION_1_1_2_2_Switch2 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , output [0:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[1:0] \f$bool$g0  = \i0$data  ;
  wire \f$bool$f$bool  = 1'd0 ;
  wire[1:0] \f$bool$f$true$arg0$arg0$arg0$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$true$arg0$arg0$arg0$arg0$conj  = \f$bool$f$true$arg0$arg0$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$true$arg0$arg0$arg0$arg0  = \f$bool$f$true$arg0$arg0$arg0$arg0$conj [1:1] ;
  wire[0:0] \f$bool$f$true$arg0$arg0$arg0$arg1  = 1'd1 ;
  wire \f$bool$f$true$arg0$arg0$arg0  = \f$bool$f$true$arg0$arg0$arg0$arg0  == \f$bool$f$true$arg0$arg0$arg0$arg1  ;
  wire \f$bool$f$true$arg0$arg0  = !\f$bool$f$true$arg0$arg0$arg0  ;
  wire[1:0] \f$bool$f$true$arg0$arg1$arg0$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$true$arg0$arg1$arg0$arg0$conj  = \f$bool$f$true$arg0$arg1$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$true$arg0$arg1$arg0$arg0  = \f$bool$f$true$arg0$arg1$arg0$arg0$conj [1:1] ;
  wire[0:0] \f$bool$f$true$arg0$arg1$arg0$arg1  = 1'd1 ;
  wire \f$bool$f$true$arg0$arg1$arg0  = \f$bool$f$true$arg0$arg1$arg0$arg0  > \f$bool$f$true$arg0$arg1$arg0$arg1  ;
  wire \f$bool$f$true$arg0$arg1  = !\f$bool$f$true$arg0$arg1$arg0  ;
  wire \f$bool$f$true$arg0  = \f$bool$f$true$arg0$arg0  && \f$bool$f$true$arg0$arg1  ;
  wire \f$bool$f$true$arg1  = 1'd0 ;
  wire \f$bool$f$true  = \f$bool$f$true$arg0  || \f$bool$f$true$arg1  ;
  wire \f$bool$f$false$bool  = 1'd0 ;
  wire[1:0] \f$bool$f$false$true$arg0$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$false$true$arg0$arg0$conj  = \f$bool$f$false$true$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$false$true$arg0$arg0  = \f$bool$f$false$true$arg0$arg0$conj [1:1] ;
  wire[0:0] \f$bool$f$false$true$arg0$arg1  = 1'd1 ;
  wire \f$bool$f$false$true$arg0  = \f$bool$f$false$true$arg0$arg0  > \f$bool$f$false$true$arg0$arg1  ;
  wire \f$bool$f$false$true$arg1$arg0  = 1'd1 ;
  wire[1:0] \f$bool$f$false$true$arg1$arg1$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$false$true$arg1$arg1$arg0$conj  = \f$bool$f$false$true$arg1$arg1$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$false$true$arg1$arg1$arg0  = \f$bool$f$false$true$arg1$arg1$arg0$conj [1:1] ;
  wire[0:0] \f$bool$f$false$true$arg1$arg1$arg1  = 1'd0 ;
  wire \f$bool$f$false$true$arg1$arg1  = \f$bool$f$false$true$arg1$arg1$arg0  == \f$bool$f$false$true$arg1$arg1$arg1  ;
  wire \f$bool$f$false$true$arg1  = \f$bool$f$false$true$arg1$arg0  && \f$bool$f$false$true$arg1$arg1  ;
  wire \f$bool$f$false$true  = \f$bool$f$false$true$arg0  || \f$bool$f$false$true$arg1  ;
  wire \f$bool$f$false$false$bool  = 1'd1 ;
  wire[1:0] \f$bool$f$false$false$true$arg0$arg0$arg0$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$false$false$true$arg0$arg0$arg0$arg0$conj  = \f$bool$f$false$false$true$arg0$arg0$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$false$false$true$arg0$arg0$arg0$arg0  = \f$bool$f$false$false$true$arg0$arg0$arg0$arg0$conj [0:0] ;
  wire[0:0] \f$bool$f$false$false$true$arg0$arg0$arg0$arg1  = 1'd1 ;
  wire \f$bool$f$false$false$true$arg0$arg0$arg0  = \f$bool$f$false$false$true$arg0$arg0$arg0$arg0  == \f$bool$f$false$false$true$arg0$arg0$arg0$arg1  ;
  wire \f$bool$f$false$false$true$arg0$arg0  = !\f$bool$f$false$false$true$arg0$arg0$arg0  ;
  wire[1:0] \f$bool$f$false$false$true$arg0$arg1$arg0$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$false$false$true$arg0$arg1$arg0$arg0$conj  = \f$bool$f$false$false$true$arg0$arg1$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$false$false$true$arg0$arg1$arg0$arg0  = \f$bool$f$false$false$true$arg0$arg1$arg0$arg0$conj [0:0] ;
  wire[0:0] \f$bool$f$false$false$true$arg0$arg1$arg0$arg1  = 1'd1 ;
  wire \f$bool$f$false$false$true$arg0$arg1$arg0  = \f$bool$f$false$false$true$arg0$arg1$arg0$arg0  > \f$bool$f$false$false$true$arg0$arg1$arg0$arg1  ;
  wire \f$bool$f$false$false$true$arg0$arg1  = !\f$bool$f$false$false$true$arg0$arg1$arg0  ;
  wire \f$bool$f$false$false$true$arg0  = \f$bool$f$false$false$true$arg0$arg0  && \f$bool$f$false$false$true$arg0$arg1  ;
  wire \f$bool$f$false$false$true$arg1  = 1'd0 ;
  wire \f$bool$f$false$false$true  = \f$bool$f$false$false$true$arg0  || \f$bool$f$false$false$true$arg1  ;
  wire[1:0] \f$bool$f$false$false$false$arg0$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$false$false$false$arg0$arg0$conj  = \f$bool$f$false$false$false$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$false$false$false$arg0$arg0  = \f$bool$f$false$false$false$arg0$arg0$conj [0:0] ;
  wire[0:0] \f$bool$f$false$false$false$arg0$arg1  = 1'd1 ;
  wire \f$bool$f$false$false$false$arg0  = \f$bool$f$false$false$false$arg0$arg0  > \f$bool$f$false$false$false$arg0$arg1  ;
  wire \f$bool$f$false$false$false$arg1$arg0  = 1'd1 ;
  wire[1:0] \f$bool$f$false$false$false$arg1$arg1$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$false$false$false$arg1$arg1$arg0$conj  = \f$bool$f$false$false$false$arg1$arg1$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$false$false$false$arg1$arg1$arg0  = \f$bool$f$false$false$false$arg1$arg1$arg0$conj [0:0] ;
  wire[0:0] \f$bool$f$false$false$false$arg1$arg1$arg1  = 1'd0 ;
  wire \f$bool$f$false$false$false$arg1$arg1  = \f$bool$f$false$false$false$arg1$arg1$arg0  == \f$bool$f$false$false$false$arg1$arg1$arg1  ;
  wire \f$bool$f$false$false$false$arg1  = \f$bool$f$false$false$false$arg1$arg0  && \f$bool$f$false$false$false$arg1$arg1  ;
  wire \f$bool$f$false$false$false  = \f$bool$f$false$false$false$arg0  || \f$bool$f$false$false$false$arg1  ;
  wire \f$bool$f$false$false  = ( \f$bool$f$false$false$bool  ? \f$bool$f$false$false$true  : \f$bool$f$false$false$false  ) ;
  wire \f$bool$f$false  = ( \f$bool$f$false$bool  ? \f$bool$f$false$true  : \f$bool$f$false$false  ) ;
  wire \f$bool$f  = ( \f$bool$f$bool  ? \f$bool$f$true  : \f$bool$f$false  ) ;
  wire \f$bool  = \f$bool$f  ;
  wire[0:0] \f$true$content  = 1'd0 ;
  wire[0:0] \f$true  = \f$true$content  ;
  wire[1:0] \f$false$bool$g0  = \i0$data  ;
  wire \f$false$bool$f$arg0$bool  = 1'd0 ;
  wire[1:0] \f$false$bool$f$arg0$true$arg0$arg0$arg0$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$true$arg0$arg0$arg0$arg0$conj  = \f$false$bool$f$arg0$true$arg0$arg0$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$true$arg0$arg0$arg0$arg0  = \f$false$bool$f$arg0$true$arg0$arg0$arg0$arg0$conj [1:1] ;
  wire[0:0] \f$false$bool$f$arg0$true$arg0$arg0$arg0$arg1  = 1'd1 ;
  wire \f$false$bool$f$arg0$true$arg0$arg0$arg0  = \f$false$bool$f$arg0$true$arg0$arg0$arg0$arg0  == \f$false$bool$f$arg0$true$arg0$arg0$arg0$arg1  ;
  wire \f$false$bool$f$arg0$true$arg0$arg0  = !\f$false$bool$f$arg0$true$arg0$arg0$arg0  ;
  wire[1:0] \f$false$bool$f$arg0$true$arg0$arg1$arg0$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$true$arg0$arg1$arg0$arg0$conj  = \f$false$bool$f$arg0$true$arg0$arg1$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$true$arg0$arg1$arg0$arg0  = \f$false$bool$f$arg0$true$arg0$arg1$arg0$arg0$conj [1:1] ;
  wire[0:0] \f$false$bool$f$arg0$true$arg0$arg1$arg0$arg1  = 1'd1 ;
  wire \f$false$bool$f$arg0$true$arg0$arg1$arg0  = \f$false$bool$f$arg0$true$arg0$arg1$arg0$arg0  > \f$false$bool$f$arg0$true$arg0$arg1$arg0$arg1  ;
  wire \f$false$bool$f$arg0$true$arg0$arg1  = !\f$false$bool$f$arg0$true$arg0$arg1$arg0  ;
  wire \f$false$bool$f$arg0$true$arg0  = \f$false$bool$f$arg0$true$arg0$arg0  && \f$false$bool$f$arg0$true$arg0$arg1  ;
  wire \f$false$bool$f$arg0$true$arg1  = 1'd0 ;
  wire \f$false$bool$f$arg0$true  = \f$false$bool$f$arg0$true$arg0  || \f$false$bool$f$arg0$true$arg1  ;
  wire \f$false$bool$f$arg0$false$bool  = 1'd0 ;
  wire[1:0] \f$false$bool$f$arg0$false$true$arg0$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$false$true$arg0$arg0$conj  = \f$false$bool$f$arg0$false$true$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$false$true$arg0$arg0  = \f$false$bool$f$arg0$false$true$arg0$arg0$conj [1:1] ;
  wire[0:0] \f$false$bool$f$arg0$false$true$arg0$arg1  = 1'd1 ;
  wire \f$false$bool$f$arg0$false$true$arg0  = \f$false$bool$f$arg0$false$true$arg0$arg0  > \f$false$bool$f$arg0$false$true$arg0$arg1  ;
  wire \f$false$bool$f$arg0$false$true$arg1$arg0  = 1'd1 ;
  wire[1:0] \f$false$bool$f$arg0$false$true$arg1$arg1$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$false$true$arg1$arg1$arg0$conj  = \f$false$bool$f$arg0$false$true$arg1$arg1$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$false$true$arg1$arg1$arg0  = \f$false$bool$f$arg0$false$true$arg1$arg1$arg0$conj [1:1] ;
  wire[0:0] \f$false$bool$f$arg0$false$true$arg1$arg1$arg1  = 1'd0 ;
  wire \f$false$bool$f$arg0$false$true$arg1$arg1  = \f$false$bool$f$arg0$false$true$arg1$arg1$arg0  == \f$false$bool$f$arg0$false$true$arg1$arg1$arg1  ;
  wire \f$false$bool$f$arg0$false$true$arg1  = \f$false$bool$f$arg0$false$true$arg1$arg0  && \f$false$bool$f$arg0$false$true$arg1$arg1  ;
  wire \f$false$bool$f$arg0$false$true  = \f$false$bool$f$arg0$false$true$arg0  || \f$false$bool$f$arg0$false$true$arg1  ;
  wire \f$false$bool$f$arg0$false$false$bool  = 1'd1 ;
  wire[1:0] \f$false$bool$f$arg0$false$false$true$arg0$arg0$arg0$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$false$false$true$arg0$arg0$arg0$arg0$conj  = \f$false$bool$f$arg0$false$false$true$arg0$arg0$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$false$false$true$arg0$arg0$arg0$arg0  = \f$false$bool$f$arg0$false$false$true$arg0$arg0$arg0$arg0$conj [0:0] ;
  wire[0:0] \f$false$bool$f$arg0$false$false$true$arg0$arg0$arg0$arg1  = 1'd1 ;
  wire \f$false$bool$f$arg0$false$false$true$arg0$arg0$arg0  = \f$false$bool$f$arg0$false$false$true$arg0$arg0$arg0$arg0  == \f$false$bool$f$arg0$false$false$true$arg0$arg0$arg0$arg1  ;
  wire \f$false$bool$f$arg0$false$false$true$arg0$arg0  = !\f$false$bool$f$arg0$false$false$true$arg0$arg0$arg0  ;
  wire[1:0] \f$false$bool$f$arg0$false$false$true$arg0$arg1$arg0$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$false$false$true$arg0$arg1$arg0$arg0$conj  = \f$false$bool$f$arg0$false$false$true$arg0$arg1$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$false$false$true$arg0$arg1$arg0$arg0  = \f$false$bool$f$arg0$false$false$true$arg0$arg1$arg0$arg0$conj [0:0] ;
  wire[0:0] \f$false$bool$f$arg0$false$false$true$arg0$arg1$arg0$arg1  = 1'd1 ;
  wire \f$false$bool$f$arg0$false$false$true$arg0$arg1$arg0  = \f$false$bool$f$arg0$false$false$true$arg0$arg1$arg0$arg0  > \f$false$bool$f$arg0$false$false$true$arg0$arg1$arg0$arg1  ;
  wire \f$false$bool$f$arg0$false$false$true$arg0$arg1  = !\f$false$bool$f$arg0$false$false$true$arg0$arg1$arg0  ;
  wire \f$false$bool$f$arg0$false$false$true$arg0  = \f$false$bool$f$arg0$false$false$true$arg0$arg0  && \f$false$bool$f$arg0$false$false$true$arg0$arg1  ;
  wire \f$false$bool$f$arg0$false$false$true$arg1  = 1'd0 ;
  wire \f$false$bool$f$arg0$false$false$true  = \f$false$bool$f$arg0$false$false$true$arg0  || \f$false$bool$f$arg0$false$false$true$arg1  ;
  wire[1:0] \f$false$bool$f$arg0$false$false$false$arg0$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$false$false$false$arg0$arg0$conj  = \f$false$bool$f$arg0$false$false$false$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$false$false$false$arg0$arg0  = \f$false$bool$f$arg0$false$false$false$arg0$arg0$conj [0:0] ;
  wire[0:0] \f$false$bool$f$arg0$false$false$false$arg0$arg1  = 1'd1 ;
  wire \f$false$bool$f$arg0$false$false$false$arg0  = \f$false$bool$f$arg0$false$false$false$arg0$arg0  > \f$false$bool$f$arg0$false$false$false$arg0$arg1  ;
  wire \f$false$bool$f$arg0$false$false$false$arg1$arg0  = 1'd1 ;
  wire[1:0] \f$false$bool$f$arg0$false$false$false$arg1$arg1$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$false$false$false$arg1$arg1$arg0$conj  = \f$false$bool$f$arg0$false$false$false$arg1$arg1$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$false$false$false$arg1$arg1$arg0  = \f$false$bool$f$arg0$false$false$false$arg1$arg1$arg0$conj [0:0] ;
  wire[0:0] \f$false$bool$f$arg0$false$false$false$arg1$arg1$arg1  = 1'd0 ;
  wire \f$false$bool$f$arg0$false$false$false$arg1$arg1  = \f$false$bool$f$arg0$false$false$false$arg1$arg1$arg0  == \f$false$bool$f$arg0$false$false$false$arg1$arg1$arg1  ;
  wire \f$false$bool$f$arg0$false$false$false$arg1  = \f$false$bool$f$arg0$false$false$false$arg1$arg0  && \f$false$bool$f$arg0$false$false$false$arg1$arg1  ;
  wire \f$false$bool$f$arg0$false$false$false  = \f$false$bool$f$arg0$false$false$false$arg0  || \f$false$bool$f$arg0$false$false$false$arg1  ;
  wire \f$false$bool$f$arg0$false$false  = ( \f$false$bool$f$arg0$false$false$bool  ? \f$false$bool$f$arg0$false$false$true  : \f$false$bool$f$arg0$false$false$false  ) ;
  wire \f$false$bool$f$arg0$false  = ( \f$false$bool$f$arg0$false$bool  ? \f$false$bool$f$arg0$false$true  : \f$false$bool$f$arg0$false$false  ) ;
  wire \f$false$bool$f$arg0  = ( \f$false$bool$f$arg0$bool  ? \f$false$bool$f$arg0$true  : \f$false$bool$f$arg0$false  ) ;
  wire \f$false$bool$f  = !\f$false$bool$f$arg0  ;
  wire \f$false$bool  = \f$false$bool$f  ;
  wire[0:0] \f$false$true$content  = 1'd1 ;
  wire[0:0] \f$false$true  = \f$false$true$content  ;
  wire[0:0] \f$false$false$content  = 1'd0 ;
  wire[0:0] \f$false$false  = \f$false$false$content  ;
  wire[0:0] \f$false  = ( \f$false$bool  ? \f$false$true  : \f$false$false  ) ;
  wire[0:0] \f  = ( \f$bool  ? \f$true  : \f$false  ) ;
  
  assign \o0  = \f  ;
endmodule

module \OFUN_1$RECEPTION_1_1_2_2_Switch2 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , output [1:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[1:0] \f  = \i0$data  ;
  
  assign \o0  = \f  ;
endmodule

module \OFUN_2$RECEPTION_1_1_2_2_Switch2 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , output [1:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[1:0] \f  = \i0$data  ;
  
  assign \o0  = \f  ;
endmodule

module \RECEPTION_0_0_2_2 (
      input \clk , input \rst , input [63:0] \t 
    , input \input$irdy , input [1:0] \input$data , output \input$trdy 
    , output \bus_outs1$irdy , output [1:0] \bus_outs1$data , input \bus_outs1$trdy 
    , output \bus_outs2$irdy , output [1:0] \bus_outs2$data , input \bus_outs2$trdy 
    , output \bus_outs3$irdy , output [1:0] \bus_outs3$data , input \bus_outs3$trdy 
    , output \bus_outs4$irdy , output [0:0] \bus_outs4$data , input \bus_outs4$trdy 
    , input \CreditCounter1$PatientSource1$unbound_irdy 
    , input [0:0] \CreditCounter1$PatientSource1$unbound_data 
    , output \CreditCounter1$PatientSource1$trdy 
    , input \CreditCounter1$Sink1$unbound_trdy 
    , output \CreditCounter1$Sink1$irdy 
    , output [0:0] \CreditCounter1$Sink1$data 
  );
  
  //
  // Channel declarations
  //
  wire \noCONS$irdy  ;
  wire [1:0] \noCONS$data  ;
  wire \noCONS$trdy  ;
  wire \toRCP$irdy  ;
  wire [1:0] \toRCP$data  ;
  wire \toRCP$trdy  ;
  wire \creditBack$irdy  ;
  wire [1:0] \creditBack$data  ;
  wire \creditBack$trdy  ;
  wire \channel1$irdy  ;
  wire [1:0] \channel1$data  ;
  wire \channel1$trdy  ;
  
  //
  // Function Channels
  //
  wire \sfunchan_0_Switch1$data  ;
  wire [1:0] \ofunchan_1_Switch1$data  ;
  wire [1:0] \ofunchan_2_Switch1$data  ;
  wire \sfunchan_0_Switch2$data  ;
  wire [1:0] \ofunchan_1_Switch2$data  ;
  wire [1:0] \ofunchan_2_Switch2$data  ;
  
  //
  // Component and Macro instantiations
  //
  \Fork2  #(
    .DATASIZE(2)
  ) \Fork1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\channel1$irdy )
    , .\i0$data (\channel1$data )
    , .\i0$trdy (\channel1$trdy )
    , .\o0$irdy (\toRCP$irdy )
    , .\o0$data (\toRCP$data )
    , .\o0$trdy (\toRCP$trdy )
    , .\o1$irdy (\creditBack$irdy )
    , .\o1$data (\creditBack$data )
    , .\o1$trdy (\creditBack$trdy )
  );
  
  \Queue  #(
    .NUM_DATA(0),
    .DATASIZE(2),
    .LENGTH(2)
  ) \Queue1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\input$irdy )
    , .\i0$data (\input$data )
    , .\i0$trdy (\input$trdy )
    , .\o0$irdy (\channel1$irdy )
    , .\o0$data (\channel1$data )
    , .\o0$trdy (\channel1$trdy )
  );
  
  \Switch2  #(
    .OUTPUTSIZE0(2),
    .OUTPUTSIZE1(2),
    .INPUTSIZE(2)
  ) \Switch1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\toRCP$irdy )
    , .\i0$data (\toRCP$data )
    , .\i0$trdy (\toRCP$trdy )
    , .\o0$irdy (\bus_outs1$irdy )
    , .\o0$data (\bus_outs1$data )
    , .\o0$trdy (\bus_outs1$trdy )
    , .\o1$irdy (\noCONS$irdy )
    , .\o1$data (\noCONS$data )
    , .\o1$trdy (\noCONS$trdy )
    , .\sel$data (\sfunchan_0_Switch1$data )
    , .\f0$data (\ofunchan_1_Switch1$data )
    , .\f1$data (\ofunchan_2_Switch1$data )
  );
  
  \SFUN_0$RECEPTION_0_0_2_2_Switch1  \sfun_0_Switch1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\toRCP$data )
    , .\o0 (\sfunchan_0_Switch1$data )
  );
  
  \OFUN_1$RECEPTION_0_0_2_2_Switch1  \ofun_1_Switch1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\toRCP$data )
    , .\o0 (\ofunchan_1_Switch1$data )
  );
  
  \OFUN_2$RECEPTION_0_0_2_2_Switch1  \ofun_2_Switch1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\toRCP$data )
    , .\o0 (\ofunchan_2_Switch1$data )
  );
  
  \Switch2  #(
    .OUTPUTSIZE0(2),
    .OUTPUTSIZE1(2),
    .INPUTSIZE(2)
  ) \Switch2  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\noCONS$irdy )
    , .\i0$data (\noCONS$data )
    , .\i0$trdy (\noCONS$trdy )
    , .\o0$irdy (\bus_outs2$irdy )
    , .\o0$data (\bus_outs2$data )
    , .\o0$trdy (\bus_outs2$trdy )
    , .\o1$irdy (\bus_outs3$irdy )
    , .\o1$data (\bus_outs3$data )
    , .\o1$trdy (\bus_outs3$trdy )
    , .\sel$data (\sfunchan_0_Switch2$data )
    , .\f0$data (\ofunchan_1_Switch2$data )
    , .\f1$data (\ofunchan_2_Switch2$data )
  );
  
  \SFUN_0$RECEPTION_0_0_2_2_Switch2  \sfun_0_Switch2  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\noCONS$data )
    , .\o0 (\sfunchan_0_Switch2$data )
  );
  
  \OFUN_1$RECEPTION_0_0_2_2_Switch2  \ofun_1_Switch2  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\noCONS$data )
    , .\o0 (\ofunchan_1_Switch2$data )
  );
  
  \OFUN_2$RECEPTION_0_0_2_2_Switch2  \ofun_2_Switch2  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\noCONS$data )
    , .\o0 (\ofunchan_2_Switch2$data )
  );
  
  \CreditCounter_2  \CreditCounter1  (
      .\clk (\clk ), .\rst (\rst ), .\t (\t )
    , .\i$irdy (\creditBack$irdy )
    , .\i$data (\creditBack$data )
    , .\i$trdy (\creditBack$trdy )
    , .\o$irdy (\bus_outs4$irdy )
    , .\o$data (\bus_outs4$data )
    , .\o$trdy (\bus_outs4$trdy )
    , .\PatientSource1$unbound_irdy (\CreditCounter1$PatientSource1$unbound_irdy )
    , .\PatientSource1$unbound_data (\CreditCounter1$PatientSource1$unbound_data )
    , .\PatientSource1$trdy (\CreditCounter1$PatientSource1$trdy )
    , .\Sink1$unbound_trdy (\CreditCounter1$Sink1$unbound_trdy )
    , .\Sink1$irdy (\CreditCounter1$Sink1$irdy )
    , .\Sink1$data (\CreditCounter1$Sink1$data )
  );
  
endmodule


//
// RECEPTION_0_0_2_2 switch functions
//
module \SFUN_0$RECEPTION_0_0_2_2_Switch1 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , output [0:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[1:0] \f$bool$g0  = \i0$data  ;
  wire[1:0] \f$bool$f$arg0$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$arg0$arg0$conj  = \f$bool$f$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$arg0$arg0  = \f$bool$f$arg0$arg0$conj [1:1] ;
  wire[0:0] \f$bool$f$arg0$arg1  = 1'd0 ;
  wire \f$bool$f$arg0  = \f$bool$f$arg0$arg0  == \f$bool$f$arg0$arg1  ;
  wire[1:0] \f$bool$f$arg1$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$arg1$arg0$conj  = \f$bool$f$arg1$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$arg1$arg0  = \f$bool$f$arg1$arg0$conj [0:0] ;
  wire[0:0] \f$bool$f$arg1$arg1  = 1'd0 ;
  wire \f$bool$f$arg1  = \f$bool$f$arg1$arg0  == \f$bool$f$arg1$arg1  ;
  wire \f$bool$f  = \f$bool$f$arg0  && \f$bool$f$arg1  ;
  wire \f$bool  = \f$bool$f  ;
  wire[0:0] \f$true$content  = 1'd0 ;
  wire[0:0] \f$true  = \f$true$content  ;
  wire[1:0] \f$false$bool$g0  = \i0$data  ;
  wire[1:0] \f$false$bool$f$arg0$arg0$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$arg0$arg0$conj  = \f$false$bool$f$arg0$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$arg0$arg0  = \f$false$bool$f$arg0$arg0$arg0$conj [1:1] ;
  wire[0:0] \f$false$bool$f$arg0$arg0$arg1  = 1'd0 ;
  wire \f$false$bool$f$arg0$arg0  = \f$false$bool$f$arg0$arg0$arg0  == \f$false$bool$f$arg0$arg0$arg1  ;
  wire[1:0] \f$false$bool$f$arg0$arg1$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$arg1$arg0$conj  = \f$false$bool$f$arg0$arg1$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$arg1$arg0  = \f$false$bool$f$arg0$arg1$arg0$conj [0:0] ;
  wire[0:0] \f$false$bool$f$arg0$arg1$arg1  = 1'd0 ;
  wire \f$false$bool$f$arg0$arg1  = \f$false$bool$f$arg0$arg1$arg0  == \f$false$bool$f$arg0$arg1$arg1  ;
  wire \f$false$bool$f$arg0  = \f$false$bool$f$arg0$arg0  && \f$false$bool$f$arg0$arg1  ;
  wire \f$false$bool$f  = !\f$false$bool$f$arg0  ;
  wire \f$false$bool  = \f$false$bool$f  ;
  wire[0:0] \f$false$true$content  = 1'd1 ;
  wire[0:0] \f$false$true  = \f$false$true$content  ;
  wire[0:0] \f$false$false$content  = 1'd0 ;
  wire[0:0] \f$false$false  = \f$false$false$content  ;
  wire[0:0] \f$false  = ( \f$false$bool  ? \f$false$true  : \f$false$false  ) ;
  wire[0:0] \f  = ( \f$bool  ? \f$true  : \f$false  ) ;
  
  assign \o0  = \f  ;
endmodule

module \OFUN_1$RECEPTION_0_0_2_2_Switch1 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , output [1:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[1:0] \f  = \i0$data  ;
  
  assign \o0  = \f  ;
endmodule

module \OFUN_2$RECEPTION_0_0_2_2_Switch1 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , output [1:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[1:0] \f  = \i0$data  ;
  
  assign \o0  = \f  ;
endmodule

module \SFUN_0$RECEPTION_0_0_2_2_Switch2 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , output [0:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[1:0] \f$bool$g0  = \i0$data  ;
  wire \f$bool$f$bool  = 1'd0 ;
  wire[1:0] \f$bool$f$true$arg0$arg0$arg0$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$true$arg0$arg0$arg0$arg0$conj  = \f$bool$f$true$arg0$arg0$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$true$arg0$arg0$arg0$arg0  = \f$bool$f$true$arg0$arg0$arg0$arg0$conj [1:1] ;
  wire[0:0] \f$bool$f$true$arg0$arg0$arg0$arg1  = 1'd0 ;
  wire \f$bool$f$true$arg0$arg0$arg0  = \f$bool$f$true$arg0$arg0$arg0$arg0  == \f$bool$f$true$arg0$arg0$arg0$arg1  ;
  wire \f$bool$f$true$arg0$arg0  = !\f$bool$f$true$arg0$arg0$arg0  ;
  wire[1:0] \f$bool$f$true$arg0$arg1$arg0$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$true$arg0$arg1$arg0$arg0$conj  = \f$bool$f$true$arg0$arg1$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$true$arg0$arg1$arg0$arg0  = \f$bool$f$true$arg0$arg1$arg0$arg0$conj [1:1] ;
  wire[0:0] \f$bool$f$true$arg0$arg1$arg0$arg1  = 1'd0 ;
  wire \f$bool$f$true$arg0$arg1$arg0  = \f$bool$f$true$arg0$arg1$arg0$arg0  > \f$bool$f$true$arg0$arg1$arg0$arg1  ;
  wire \f$bool$f$true$arg0$arg1  = !\f$bool$f$true$arg0$arg1$arg0  ;
  wire \f$bool$f$true$arg0  = \f$bool$f$true$arg0$arg0  && \f$bool$f$true$arg0$arg1  ;
  wire \f$bool$f$true$arg1$arg0  = 1'd1 ;
  wire[1:0] \f$bool$f$true$arg1$arg1$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$true$arg1$arg1$arg0$conj  = \f$bool$f$true$arg1$arg1$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$true$arg1$arg1$arg0  = \f$bool$f$true$arg1$arg1$arg0$conj [1:1] ;
  wire[0:0] \f$bool$f$true$arg1$arg1$arg1  = 1'd1 ;
  wire \f$bool$f$true$arg1$arg1  = \f$bool$f$true$arg1$arg1$arg0  == \f$bool$f$true$arg1$arg1$arg1  ;
  wire \f$bool$f$true$arg1  = \f$bool$f$true$arg1$arg0  && \f$bool$f$true$arg1$arg1  ;
  wire \f$bool$f$true  = \f$bool$f$true$arg0  || \f$bool$f$true$arg1  ;
  wire \f$bool$f$false$bool  = 1'd0 ;
  wire[1:0] \f$bool$f$false$true$arg0$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$false$true$arg0$arg0$conj  = \f$bool$f$false$true$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$false$true$arg0$arg0  = \f$bool$f$false$true$arg0$arg0$conj [1:1] ;
  wire[0:0] \f$bool$f$false$true$arg0$arg1  = 1'd0 ;
  wire \f$bool$f$false$true$arg0  = \f$bool$f$false$true$arg0$arg0  > \f$bool$f$false$true$arg0$arg1  ;
  wire \f$bool$f$false$true$arg1  = 1'd0 ;
  wire \f$bool$f$false$true  = \f$bool$f$false$true$arg0  || \f$bool$f$false$true$arg1  ;
  wire \f$bool$f$false$false$bool  = 1'd1 ;
  wire[1:0] \f$bool$f$false$false$true$arg0$arg0$arg0$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$false$false$true$arg0$arg0$arg0$arg0$conj  = \f$bool$f$false$false$true$arg0$arg0$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$false$false$true$arg0$arg0$arg0$arg0  = \f$bool$f$false$false$true$arg0$arg0$arg0$arg0$conj [0:0] ;
  wire[0:0] \f$bool$f$false$false$true$arg0$arg0$arg0$arg1  = 1'd0 ;
  wire \f$bool$f$false$false$true$arg0$arg0$arg0  = \f$bool$f$false$false$true$arg0$arg0$arg0$arg0  == \f$bool$f$false$false$true$arg0$arg0$arg0$arg1  ;
  wire \f$bool$f$false$false$true$arg0$arg0  = !\f$bool$f$false$false$true$arg0$arg0$arg0  ;
  wire[1:0] \f$bool$f$false$false$true$arg0$arg1$arg0$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$false$false$true$arg0$arg1$arg0$arg0$conj  = \f$bool$f$false$false$true$arg0$arg1$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$false$false$true$arg0$arg1$arg0$arg0  = \f$bool$f$false$false$true$arg0$arg1$arg0$arg0$conj [0:0] ;
  wire[0:0] \f$bool$f$false$false$true$arg0$arg1$arg0$arg1  = 1'd0 ;
  wire \f$bool$f$false$false$true$arg0$arg1$arg0  = \f$bool$f$false$false$true$arg0$arg1$arg0$arg0  > \f$bool$f$false$false$true$arg0$arg1$arg0$arg1  ;
  wire \f$bool$f$false$false$true$arg0$arg1  = !\f$bool$f$false$false$true$arg0$arg1$arg0  ;
  wire \f$bool$f$false$false$true$arg0  = \f$bool$f$false$false$true$arg0$arg0  && \f$bool$f$false$false$true$arg0$arg1  ;
  wire \f$bool$f$false$false$true$arg1$arg0  = 1'd1 ;
  wire[1:0] \f$bool$f$false$false$true$arg1$arg1$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$false$false$true$arg1$arg1$arg0$conj  = \f$bool$f$false$false$true$arg1$arg1$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$false$false$true$arg1$arg1$arg0  = \f$bool$f$false$false$true$arg1$arg1$arg0$conj [0:0] ;
  wire[0:0] \f$bool$f$false$false$true$arg1$arg1$arg1  = 1'd1 ;
  wire \f$bool$f$false$false$true$arg1$arg1  = \f$bool$f$false$false$true$arg1$arg1$arg0  == \f$bool$f$false$false$true$arg1$arg1$arg1  ;
  wire \f$bool$f$false$false$true$arg1  = \f$bool$f$false$false$true$arg1$arg0  && \f$bool$f$false$false$true$arg1$arg1  ;
  wire \f$bool$f$false$false$true  = \f$bool$f$false$false$true$arg0  || \f$bool$f$false$false$true$arg1  ;
  wire[1:0] \f$bool$f$false$false$false$arg0$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$false$false$false$arg0$arg0$conj  = \f$bool$f$false$false$false$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$false$false$false$arg0$arg0  = \f$bool$f$false$false$false$arg0$arg0$conj [0:0] ;
  wire[0:0] \f$bool$f$false$false$false$arg0$arg1  = 1'd0 ;
  wire \f$bool$f$false$false$false$arg0  = \f$bool$f$false$false$false$arg0$arg0  > \f$bool$f$false$false$false$arg0$arg1  ;
  wire \f$bool$f$false$false$false$arg1  = 1'd0 ;
  wire \f$bool$f$false$false$false  = \f$bool$f$false$false$false$arg0  || \f$bool$f$false$false$false$arg1  ;
  wire \f$bool$f$false$false  = ( \f$bool$f$false$false$bool  ? \f$bool$f$false$false$true  : \f$bool$f$false$false$false  ) ;
  wire \f$bool$f$false  = ( \f$bool$f$false$bool  ? \f$bool$f$false$true  : \f$bool$f$false$false  ) ;
  wire \f$bool$f  = ( \f$bool$f$bool  ? \f$bool$f$true  : \f$bool$f$false  ) ;
  wire \f$bool  = \f$bool$f  ;
  wire[0:0] \f$true$content  = 1'd0 ;
  wire[0:0] \f$true  = \f$true$content  ;
  wire[1:0] \f$false$bool$g0  = \i0$data  ;
  wire \f$false$bool$f$arg0$bool  = 1'd0 ;
  wire[1:0] \f$false$bool$f$arg0$true$arg0$arg0$arg0$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$true$arg0$arg0$arg0$arg0$conj  = \f$false$bool$f$arg0$true$arg0$arg0$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$true$arg0$arg0$arg0$arg0  = \f$false$bool$f$arg0$true$arg0$arg0$arg0$arg0$conj [1:1] ;
  wire[0:0] \f$false$bool$f$arg0$true$arg0$arg0$arg0$arg1  = 1'd0 ;
  wire \f$false$bool$f$arg0$true$arg0$arg0$arg0  = \f$false$bool$f$arg0$true$arg0$arg0$arg0$arg0  == \f$false$bool$f$arg0$true$arg0$arg0$arg0$arg1  ;
  wire \f$false$bool$f$arg0$true$arg0$arg0  = !\f$false$bool$f$arg0$true$arg0$arg0$arg0  ;
  wire[1:0] \f$false$bool$f$arg0$true$arg0$arg1$arg0$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$true$arg0$arg1$arg0$arg0$conj  = \f$false$bool$f$arg0$true$arg0$arg1$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$true$arg0$arg1$arg0$arg0  = \f$false$bool$f$arg0$true$arg0$arg1$arg0$arg0$conj [1:1] ;
  wire[0:0] \f$false$bool$f$arg0$true$arg0$arg1$arg0$arg1  = 1'd0 ;
  wire \f$false$bool$f$arg0$true$arg0$arg1$arg0  = \f$false$bool$f$arg0$true$arg0$arg1$arg0$arg0  > \f$false$bool$f$arg0$true$arg0$arg1$arg0$arg1  ;
  wire \f$false$bool$f$arg0$true$arg0$arg1  = !\f$false$bool$f$arg0$true$arg0$arg1$arg0  ;
  wire \f$false$bool$f$arg0$true$arg0  = \f$false$bool$f$arg0$true$arg0$arg0  && \f$false$bool$f$arg0$true$arg0$arg1  ;
  wire \f$false$bool$f$arg0$true$arg1$arg0  = 1'd1 ;
  wire[1:0] \f$false$bool$f$arg0$true$arg1$arg1$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$true$arg1$arg1$arg0$conj  = \f$false$bool$f$arg0$true$arg1$arg1$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$true$arg1$arg1$arg0  = \f$false$bool$f$arg0$true$arg1$arg1$arg0$conj [1:1] ;
  wire[0:0] \f$false$bool$f$arg0$true$arg1$arg1$arg1  = 1'd1 ;
  wire \f$false$bool$f$arg0$true$arg1$arg1  = \f$false$bool$f$arg0$true$arg1$arg1$arg0  == \f$false$bool$f$arg0$true$arg1$arg1$arg1  ;
  wire \f$false$bool$f$arg0$true$arg1  = \f$false$bool$f$arg0$true$arg1$arg0  && \f$false$bool$f$arg0$true$arg1$arg1  ;
  wire \f$false$bool$f$arg0$true  = \f$false$bool$f$arg0$true$arg0  || \f$false$bool$f$arg0$true$arg1  ;
  wire \f$false$bool$f$arg0$false$bool  = 1'd0 ;
  wire[1:0] \f$false$bool$f$arg0$false$true$arg0$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$false$true$arg0$arg0$conj  = \f$false$bool$f$arg0$false$true$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$false$true$arg0$arg0  = \f$false$bool$f$arg0$false$true$arg0$arg0$conj [1:1] ;
  wire[0:0] \f$false$bool$f$arg0$false$true$arg0$arg1  = 1'd0 ;
  wire \f$false$bool$f$arg0$false$true$arg0  = \f$false$bool$f$arg0$false$true$arg0$arg0  > \f$false$bool$f$arg0$false$true$arg0$arg1  ;
  wire \f$false$bool$f$arg0$false$true$arg1  = 1'd0 ;
  wire \f$false$bool$f$arg0$false$true  = \f$false$bool$f$arg0$false$true$arg0  || \f$false$bool$f$arg0$false$true$arg1  ;
  wire \f$false$bool$f$arg0$false$false$bool  = 1'd1 ;
  wire[1:0] \f$false$bool$f$arg0$false$false$true$arg0$arg0$arg0$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$false$false$true$arg0$arg0$arg0$arg0$conj  = \f$false$bool$f$arg0$false$false$true$arg0$arg0$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$false$false$true$arg0$arg0$arg0$arg0  = \f$false$bool$f$arg0$false$false$true$arg0$arg0$arg0$arg0$conj [0:0] ;
  wire[0:0] \f$false$bool$f$arg0$false$false$true$arg0$arg0$arg0$arg1  = 1'd0 ;
  wire \f$false$bool$f$arg0$false$false$true$arg0$arg0$arg0  = \f$false$bool$f$arg0$false$false$true$arg0$arg0$arg0$arg0  == \f$false$bool$f$arg0$false$false$true$arg0$arg0$arg0$arg1  ;
  wire \f$false$bool$f$arg0$false$false$true$arg0$arg0  = !\f$false$bool$f$arg0$false$false$true$arg0$arg0$arg0  ;
  wire[1:0] \f$false$bool$f$arg0$false$false$true$arg0$arg1$arg0$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$false$false$true$arg0$arg1$arg0$arg0$conj  = \f$false$bool$f$arg0$false$false$true$arg0$arg1$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$false$false$true$arg0$arg1$arg0$arg0  = \f$false$bool$f$arg0$false$false$true$arg0$arg1$arg0$arg0$conj [0:0] ;
  wire[0:0] \f$false$bool$f$arg0$false$false$true$arg0$arg1$arg0$arg1  = 1'd0 ;
  wire \f$false$bool$f$arg0$false$false$true$arg0$arg1$arg0  = \f$false$bool$f$arg0$false$false$true$arg0$arg1$arg0$arg0  > \f$false$bool$f$arg0$false$false$true$arg0$arg1$arg0$arg1  ;
  wire \f$false$bool$f$arg0$false$false$true$arg0$arg1  = !\f$false$bool$f$arg0$false$false$true$arg0$arg1$arg0  ;
  wire \f$false$bool$f$arg0$false$false$true$arg0  = \f$false$bool$f$arg0$false$false$true$arg0$arg0  && \f$false$bool$f$arg0$false$false$true$arg0$arg1  ;
  wire \f$false$bool$f$arg0$false$false$true$arg1$arg0  = 1'd1 ;
  wire[1:0] \f$false$bool$f$arg0$false$false$true$arg1$arg1$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$false$false$true$arg1$arg1$arg0$conj  = \f$false$bool$f$arg0$false$false$true$arg1$arg1$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$false$false$true$arg1$arg1$arg0  = \f$false$bool$f$arg0$false$false$true$arg1$arg1$arg0$conj [0:0] ;
  wire[0:0] \f$false$bool$f$arg0$false$false$true$arg1$arg1$arg1  = 1'd1 ;
  wire \f$false$bool$f$arg0$false$false$true$arg1$arg1  = \f$false$bool$f$arg0$false$false$true$arg1$arg1$arg0  == \f$false$bool$f$arg0$false$false$true$arg1$arg1$arg1  ;
  wire \f$false$bool$f$arg0$false$false$true$arg1  = \f$false$bool$f$arg0$false$false$true$arg1$arg0  && \f$false$bool$f$arg0$false$false$true$arg1$arg1  ;
  wire \f$false$bool$f$arg0$false$false$true  = \f$false$bool$f$arg0$false$false$true$arg0  || \f$false$bool$f$arg0$false$false$true$arg1  ;
  wire[1:0] \f$false$bool$f$arg0$false$false$false$arg0$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$false$false$false$arg0$arg0$conj  = \f$false$bool$f$arg0$false$false$false$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$false$false$false$arg0$arg0  = \f$false$bool$f$arg0$false$false$false$arg0$arg0$conj [0:0] ;
  wire[0:0] \f$false$bool$f$arg0$false$false$false$arg0$arg1  = 1'd0 ;
  wire \f$false$bool$f$arg0$false$false$false$arg0  = \f$false$bool$f$arg0$false$false$false$arg0$arg0  > \f$false$bool$f$arg0$false$false$false$arg0$arg1  ;
  wire \f$false$bool$f$arg0$false$false$false$arg1  = 1'd0 ;
  wire \f$false$bool$f$arg0$false$false$false  = \f$false$bool$f$arg0$false$false$false$arg0  || \f$false$bool$f$arg0$false$false$false$arg1  ;
  wire \f$false$bool$f$arg0$false$false  = ( \f$false$bool$f$arg0$false$false$bool  ? \f$false$bool$f$arg0$false$false$true  : \f$false$bool$f$arg0$false$false$false  ) ;
  wire \f$false$bool$f$arg0$false  = ( \f$false$bool$f$arg0$false$bool  ? \f$false$bool$f$arg0$false$true  : \f$false$bool$f$arg0$false$false  ) ;
  wire \f$false$bool$f$arg0  = ( \f$false$bool$f$arg0$bool  ? \f$false$bool$f$arg0$true  : \f$false$bool$f$arg0$false  ) ;
  wire \f$false$bool$f  = !\f$false$bool$f$arg0  ;
  wire \f$false$bool  = \f$false$bool$f  ;
  wire[0:0] \f$false$true$content  = 1'd1 ;
  wire[0:0] \f$false$true  = \f$false$true$content  ;
  wire[0:0] \f$false$false$content  = 1'd0 ;
  wire[0:0] \f$false$false  = \f$false$false$content  ;
  wire[0:0] \f$false  = ( \f$false$bool  ? \f$false$true  : \f$false$false  ) ;
  wire[0:0] \f  = ( \f$bool  ? \f$true  : \f$false  ) ;
  
  assign \o0  = \f  ;
endmodule

module \OFUN_1$RECEPTION_0_0_2_2_Switch2 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , output [1:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[1:0] \f  = \i0$data  ;
  
  assign \o0  = \f  ;
endmodule

module \OFUN_2$RECEPTION_0_0_2_2_Switch2 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , output [1:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[1:0] \f  = \i0$data  ;
  
  assign \o0  = \f  ;
endmodule

module \RECEPTION_1_0_3_2 (
      input \clk , input \rst , input [63:0] \t 
    , input \input$irdy , input [1:0] \input$data , output \input$trdy 
    , output \bus_outs1$irdy , output [1:0] \bus_outs1$data , input \bus_outs1$trdy 
    , output \bus_outs2$irdy , output [1:0] \bus_outs2$data , input \bus_outs2$trdy 
    , output \bus_outs3$irdy , output [1:0] \bus_outs3$data , input \bus_outs3$trdy 
    , output \bus_outs4$irdy , output [0:0] \bus_outs4$data , input \bus_outs4$trdy 
    , input \CreditCounter1$PatientSource1$unbound_irdy 
    , input [0:0] \CreditCounter1$PatientSource1$unbound_data 
    , output \CreditCounter1$PatientSource1$trdy 
    , input \CreditCounter1$Sink1$unbound_trdy 
    , output \CreditCounter1$Sink1$irdy 
    , output [0:0] \CreditCounter1$Sink1$data 
  );
  
  //
  // Channel declarations
  //
  wire \noCONS$irdy  ;
  wire [1:0] \noCONS$data  ;
  wire \noCONS$trdy  ;
  wire \toRCP$irdy  ;
  wire [1:0] \toRCP$data  ;
  wire \toRCP$trdy  ;
  wire \creditBack$irdy  ;
  wire [1:0] \creditBack$data  ;
  wire \creditBack$trdy  ;
  wire \channel1$irdy  ;
  wire [1:0] \channel1$data  ;
  wire \channel1$trdy  ;
  
  //
  // Function Channels
  //
  wire \sfunchan_0_Switch1$data  ;
  wire [1:0] \ofunchan_1_Switch1$data  ;
  wire [1:0] \ofunchan_2_Switch1$data  ;
  wire \sfunchan_0_Switch2$data  ;
  wire [1:0] \ofunchan_1_Switch2$data  ;
  wire [1:0] \ofunchan_2_Switch2$data  ;
  
  //
  // Component and Macro instantiations
  //
  \Fork2  #(
    .DATASIZE(2)
  ) \Fork1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\channel1$irdy )
    , .\i0$data (\channel1$data )
    , .\i0$trdy (\channel1$trdy )
    , .\o0$irdy (\toRCP$irdy )
    , .\o0$data (\toRCP$data )
    , .\o0$trdy (\toRCP$trdy )
    , .\o1$irdy (\creditBack$irdy )
    , .\o1$data (\creditBack$data )
    , .\o1$trdy (\creditBack$trdy )
  );
  
  \Queue  #(
    .NUM_DATA(0),
    .DATASIZE(2),
    .LENGTH(2)
  ) \Queue1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\input$irdy )
    , .\i0$data (\input$data )
    , .\i0$trdy (\input$trdy )
    , .\o0$irdy (\channel1$irdy )
    , .\o0$data (\channel1$data )
    , .\o0$trdy (\channel1$trdy )
  );
  
  \Switch2  #(
    .OUTPUTSIZE0(2),
    .OUTPUTSIZE1(2),
    .INPUTSIZE(2)
  ) \Switch1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\toRCP$irdy )
    , .\i0$data (\toRCP$data )
    , .\i0$trdy (\toRCP$trdy )
    , .\o0$irdy (\bus_outs1$irdy )
    , .\o0$data (\bus_outs1$data )
    , .\o0$trdy (\bus_outs1$trdy )
    , .\o1$irdy (\noCONS$irdy )
    , .\o1$data (\noCONS$data )
    , .\o1$trdy (\noCONS$trdy )
    , .\sel$data (\sfunchan_0_Switch1$data )
    , .\f0$data (\ofunchan_1_Switch1$data )
    , .\f1$data (\ofunchan_2_Switch1$data )
  );
  
  \SFUN_0$RECEPTION_1_0_3_2_Switch1  \sfun_0_Switch1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\toRCP$data )
    , .\o0 (\sfunchan_0_Switch1$data )
  );
  
  \OFUN_1$RECEPTION_1_0_3_2_Switch1  \ofun_1_Switch1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\toRCP$data )
    , .\o0 (\ofunchan_1_Switch1$data )
  );
  
  \OFUN_2$RECEPTION_1_0_3_2_Switch1  \ofun_2_Switch1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\toRCP$data )
    , .\o0 (\ofunchan_2_Switch1$data )
  );
  
  \Switch2  #(
    .OUTPUTSIZE0(2),
    .OUTPUTSIZE1(2),
    .INPUTSIZE(2)
  ) \Switch2  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\noCONS$irdy )
    , .\i0$data (\noCONS$data )
    , .\i0$trdy (\noCONS$trdy )
    , .\o0$irdy (\bus_outs2$irdy )
    , .\o0$data (\bus_outs2$data )
    , .\o0$trdy (\bus_outs2$trdy )
    , .\o1$irdy (\bus_outs3$irdy )
    , .\o1$data (\bus_outs3$data )
    , .\o1$trdy (\bus_outs3$trdy )
    , .\sel$data (\sfunchan_0_Switch2$data )
    , .\f0$data (\ofunchan_1_Switch2$data )
    , .\f1$data (\ofunchan_2_Switch2$data )
  );
  
  \SFUN_0$RECEPTION_1_0_3_2_Switch2  \sfun_0_Switch2  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\noCONS$data )
    , .\o0 (\sfunchan_0_Switch2$data )
  );
  
  \OFUN_1$RECEPTION_1_0_3_2_Switch2  \ofun_1_Switch2  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\noCONS$data )
    , .\o0 (\ofunchan_1_Switch2$data )
  );
  
  \OFUN_2$RECEPTION_1_0_3_2_Switch2  \ofun_2_Switch2  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\noCONS$data )
    , .\o0 (\ofunchan_2_Switch2$data )
  );
  
  \CreditCounter_2  \CreditCounter1  (
      .\clk (\clk ), .\rst (\rst ), .\t (\t )
    , .\i$irdy (\creditBack$irdy )
    , .\i$data (\creditBack$data )
    , .\i$trdy (\creditBack$trdy )
    , .\o$irdy (\bus_outs4$irdy )
    , .\o$data (\bus_outs4$data )
    , .\o$trdy (\bus_outs4$trdy )
    , .\PatientSource1$unbound_irdy (\CreditCounter1$PatientSource1$unbound_irdy )
    , .\PatientSource1$unbound_data (\CreditCounter1$PatientSource1$unbound_data )
    , .\PatientSource1$trdy (\CreditCounter1$PatientSource1$trdy )
    , .\Sink1$unbound_trdy (\CreditCounter1$Sink1$unbound_trdy )
    , .\Sink1$irdy (\CreditCounter1$Sink1$irdy )
    , .\Sink1$data (\CreditCounter1$Sink1$data )
  );
  
endmodule


//
// RECEPTION_1_0_3_2 switch functions
//
module \SFUN_0$RECEPTION_1_0_3_2_Switch1 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , output [0:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[1:0] \f$bool$g0  = \i0$data  ;
  wire[1:0] \f$bool$f$arg0$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$arg0$arg0$conj  = \f$bool$f$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$arg0$arg0  = \f$bool$f$arg0$arg0$conj [1:1] ;
  wire[0:0] \f$bool$f$arg0$arg1  = 1'd1 ;
  wire \f$bool$f$arg0  = \f$bool$f$arg0$arg0  == \f$bool$f$arg0$arg1  ;
  wire[1:0] \f$bool$f$arg1$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$arg1$arg0$conj  = \f$bool$f$arg1$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$arg1$arg0  = \f$bool$f$arg1$arg0$conj [0:0] ;
  wire[0:0] \f$bool$f$arg1$arg1  = 1'd0 ;
  wire \f$bool$f$arg1  = \f$bool$f$arg1$arg0  == \f$bool$f$arg1$arg1  ;
  wire \f$bool$f  = \f$bool$f$arg0  && \f$bool$f$arg1  ;
  wire \f$bool  = \f$bool$f  ;
  wire[0:0] \f$true$content  = 1'd0 ;
  wire[0:0] \f$true  = \f$true$content  ;
  wire[1:0] \f$false$bool$g0  = \i0$data  ;
  wire[1:0] \f$false$bool$f$arg0$arg0$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$arg0$arg0$conj  = \f$false$bool$f$arg0$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$arg0$arg0  = \f$false$bool$f$arg0$arg0$arg0$conj [1:1] ;
  wire[0:0] \f$false$bool$f$arg0$arg0$arg1  = 1'd1 ;
  wire \f$false$bool$f$arg0$arg0  = \f$false$bool$f$arg0$arg0$arg0  == \f$false$bool$f$arg0$arg0$arg1  ;
  wire[1:0] \f$false$bool$f$arg0$arg1$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$arg1$arg0$conj  = \f$false$bool$f$arg0$arg1$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$arg1$arg0  = \f$false$bool$f$arg0$arg1$arg0$conj [0:0] ;
  wire[0:0] \f$false$bool$f$arg0$arg1$arg1  = 1'd0 ;
  wire \f$false$bool$f$arg0$arg1  = \f$false$bool$f$arg0$arg1$arg0  == \f$false$bool$f$arg0$arg1$arg1  ;
  wire \f$false$bool$f$arg0  = \f$false$bool$f$arg0$arg0  && \f$false$bool$f$arg0$arg1  ;
  wire \f$false$bool$f  = !\f$false$bool$f$arg0  ;
  wire \f$false$bool  = \f$false$bool$f  ;
  wire[0:0] \f$false$true$content  = 1'd1 ;
  wire[0:0] \f$false$true  = \f$false$true$content  ;
  wire[0:0] \f$false$false$content  = 1'd0 ;
  wire[0:0] \f$false$false  = \f$false$false$content  ;
  wire[0:0] \f$false  = ( \f$false$bool  ? \f$false$true  : \f$false$false  ) ;
  wire[0:0] \f  = ( \f$bool  ? \f$true  : \f$false  ) ;
  
  assign \o0  = \f  ;
endmodule

module \OFUN_1$RECEPTION_1_0_3_2_Switch1 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , output [1:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[1:0] \f  = \i0$data  ;
  
  assign \o0  = \f  ;
endmodule

module \OFUN_2$RECEPTION_1_0_3_2_Switch1 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , output [1:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[1:0] \f  = \i0$data  ;
  
  assign \o0  = \f  ;
endmodule

module \SFUN_0$RECEPTION_1_0_3_2_Switch2 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , output [0:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[1:0] \f$bool$g0  = \i0$data  ;
  wire \f$bool$f$bool  = 1'd0 ;
  wire[1:0] \f$bool$f$true$arg0$arg0$arg0$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$true$arg0$arg0$arg0$arg0$conj  = \f$bool$f$true$arg0$arg0$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$true$arg0$arg0$arg0$arg0  = \f$bool$f$true$arg0$arg0$arg0$arg0$conj [1:1] ;
  wire[0:0] \f$bool$f$true$arg0$arg0$arg0$arg1  = 1'd1 ;
  wire \f$bool$f$true$arg0$arg0$arg0  = \f$bool$f$true$arg0$arg0$arg0$arg0  == \f$bool$f$true$arg0$arg0$arg0$arg1  ;
  wire \f$bool$f$true$arg0$arg0  = !\f$bool$f$true$arg0$arg0$arg0  ;
  wire[1:0] \f$bool$f$true$arg0$arg1$arg0$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$true$arg0$arg1$arg0$arg0$conj  = \f$bool$f$true$arg0$arg1$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$true$arg0$arg1$arg0$arg0  = \f$bool$f$true$arg0$arg1$arg0$arg0$conj [1:1] ;
  wire[0:0] \f$bool$f$true$arg0$arg1$arg0$arg1  = 1'd1 ;
  wire \f$bool$f$true$arg0$arg1$arg0  = \f$bool$f$true$arg0$arg1$arg0$arg0  > \f$bool$f$true$arg0$arg1$arg0$arg1  ;
  wire \f$bool$f$true$arg0$arg1  = !\f$bool$f$true$arg0$arg1$arg0  ;
  wire \f$bool$f$true$arg0  = \f$bool$f$true$arg0$arg0  && \f$bool$f$true$arg0$arg1  ;
  wire \f$bool$f$true$arg1  = 1'd0 ;
  wire \f$bool$f$true  = \f$bool$f$true$arg0  || \f$bool$f$true$arg1  ;
  wire \f$bool$f$false$bool  = 1'd0 ;
  wire[1:0] \f$bool$f$false$true$arg0$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$false$true$arg0$arg0$conj  = \f$bool$f$false$true$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$false$true$arg0$arg0  = \f$bool$f$false$true$arg0$arg0$conj [1:1] ;
  wire[0:0] \f$bool$f$false$true$arg0$arg1  = 1'd1 ;
  wire \f$bool$f$false$true$arg0  = \f$bool$f$false$true$arg0$arg0  > \f$bool$f$false$true$arg0$arg1  ;
  wire \f$bool$f$false$true$arg1$arg0  = 1'd1 ;
  wire[1:0] \f$bool$f$false$true$arg1$arg1$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$false$true$arg1$arg1$arg0$conj  = \f$bool$f$false$true$arg1$arg1$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$false$true$arg1$arg1$arg0  = \f$bool$f$false$true$arg1$arg1$arg0$conj [1:1] ;
  wire[0:0] \f$bool$f$false$true$arg1$arg1$arg1  = 1'd0 ;
  wire \f$bool$f$false$true$arg1$arg1  = \f$bool$f$false$true$arg1$arg1$arg0  == \f$bool$f$false$true$arg1$arg1$arg1  ;
  wire \f$bool$f$false$true$arg1  = \f$bool$f$false$true$arg1$arg0  && \f$bool$f$false$true$arg1$arg1  ;
  wire \f$bool$f$false$true  = \f$bool$f$false$true$arg0  || \f$bool$f$false$true$arg1  ;
  wire \f$bool$f$false$false$bool  = 1'd0 ;
  wire[1:0] \f$bool$f$false$false$true$arg0$arg0$arg0$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$false$false$true$arg0$arg0$arg0$arg0$conj  = \f$bool$f$false$false$true$arg0$arg0$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$false$false$true$arg0$arg0$arg0$arg0  = \f$bool$f$false$false$true$arg0$arg0$arg0$arg0$conj [0:0] ;
  wire[0:0] \f$bool$f$false$false$true$arg0$arg0$arg0$arg1  = 1'd0 ;
  wire \f$bool$f$false$false$true$arg0$arg0$arg0  = \f$bool$f$false$false$true$arg0$arg0$arg0$arg0  == \f$bool$f$false$false$true$arg0$arg0$arg0$arg1  ;
  wire \f$bool$f$false$false$true$arg0$arg0  = !\f$bool$f$false$false$true$arg0$arg0$arg0  ;
  wire[1:0] \f$bool$f$false$false$true$arg0$arg1$arg0$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$false$false$true$arg0$arg1$arg0$arg0$conj  = \f$bool$f$false$false$true$arg0$arg1$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$false$false$true$arg0$arg1$arg0$arg0  = \f$bool$f$false$false$true$arg0$arg1$arg0$arg0$conj [0:0] ;
  wire[0:0] \f$bool$f$false$false$true$arg0$arg1$arg0$arg1  = 1'd0 ;
  wire \f$bool$f$false$false$true$arg0$arg1$arg0  = \f$bool$f$false$false$true$arg0$arg1$arg0$arg0  > \f$bool$f$false$false$true$arg0$arg1$arg0$arg1  ;
  wire \f$bool$f$false$false$true$arg0$arg1  = !\f$bool$f$false$false$true$arg0$arg1$arg0  ;
  wire \f$bool$f$false$false$true$arg0  = \f$bool$f$false$false$true$arg0$arg0  && \f$bool$f$false$false$true$arg0$arg1  ;
  wire \f$bool$f$false$false$true$arg1$arg0  = 1'd1 ;
  wire[1:0] \f$bool$f$false$false$true$arg1$arg1$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$false$false$true$arg1$arg1$arg0$conj  = \f$bool$f$false$false$true$arg1$arg1$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$false$false$true$arg1$arg1$arg0  = \f$bool$f$false$false$true$arg1$arg1$arg0$conj [0:0] ;
  wire[0:0] \f$bool$f$false$false$true$arg1$arg1$arg1  = 1'd1 ;
  wire \f$bool$f$false$false$true$arg1$arg1  = \f$bool$f$false$false$true$arg1$arg1$arg0  == \f$bool$f$false$false$true$arg1$arg1$arg1  ;
  wire \f$bool$f$false$false$true$arg1  = \f$bool$f$false$false$true$arg1$arg0  && \f$bool$f$false$false$true$arg1$arg1  ;
  wire \f$bool$f$false$false$true  = \f$bool$f$false$false$true$arg0  || \f$bool$f$false$false$true$arg1  ;
  wire[1:0] \f$bool$f$false$false$false$arg0$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$false$false$false$arg0$arg0$conj  = \f$bool$f$false$false$false$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$false$false$false$arg0$arg0  = \f$bool$f$false$false$false$arg0$arg0$conj [0:0] ;
  wire[0:0] \f$bool$f$false$false$false$arg0$arg1  = 1'd0 ;
  wire \f$bool$f$false$false$false$arg0  = \f$bool$f$false$false$false$arg0$arg0  > \f$bool$f$false$false$false$arg0$arg1  ;
  wire \f$bool$f$false$false$false$arg1  = 1'd0 ;
  wire \f$bool$f$false$false$false  = \f$bool$f$false$false$false$arg0  || \f$bool$f$false$false$false$arg1  ;
  wire \f$bool$f$false$false  = ( \f$bool$f$false$false$bool  ? \f$bool$f$false$false$true  : \f$bool$f$false$false$false  ) ;
  wire \f$bool$f$false  = ( \f$bool$f$false$bool  ? \f$bool$f$false$true  : \f$bool$f$false$false  ) ;
  wire \f$bool$f  = ( \f$bool$f$bool  ? \f$bool$f$true  : \f$bool$f$false  ) ;
  wire \f$bool  = \f$bool$f  ;
  wire[0:0] \f$true$content  = 1'd0 ;
  wire[0:0] \f$true  = \f$true$content  ;
  wire[1:0] \f$false$bool$g0  = \i0$data  ;
  wire \f$false$bool$f$arg0$bool  = 1'd0 ;
  wire[1:0] \f$false$bool$f$arg0$true$arg0$arg0$arg0$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$true$arg0$arg0$arg0$arg0$conj  = \f$false$bool$f$arg0$true$arg0$arg0$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$true$arg0$arg0$arg0$arg0  = \f$false$bool$f$arg0$true$arg0$arg0$arg0$arg0$conj [1:1] ;
  wire[0:0] \f$false$bool$f$arg0$true$arg0$arg0$arg0$arg1  = 1'd1 ;
  wire \f$false$bool$f$arg0$true$arg0$arg0$arg0  = \f$false$bool$f$arg0$true$arg0$arg0$arg0$arg0  == \f$false$bool$f$arg0$true$arg0$arg0$arg0$arg1  ;
  wire \f$false$bool$f$arg0$true$arg0$arg0  = !\f$false$bool$f$arg0$true$arg0$arg0$arg0  ;
  wire[1:0] \f$false$bool$f$arg0$true$arg0$arg1$arg0$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$true$arg0$arg1$arg0$arg0$conj  = \f$false$bool$f$arg0$true$arg0$arg1$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$true$arg0$arg1$arg0$arg0  = \f$false$bool$f$arg0$true$arg0$arg1$arg0$arg0$conj [1:1] ;
  wire[0:0] \f$false$bool$f$arg0$true$arg0$arg1$arg0$arg1  = 1'd1 ;
  wire \f$false$bool$f$arg0$true$arg0$arg1$arg0  = \f$false$bool$f$arg0$true$arg0$arg1$arg0$arg0  > \f$false$bool$f$arg0$true$arg0$arg1$arg0$arg1  ;
  wire \f$false$bool$f$arg0$true$arg0$arg1  = !\f$false$bool$f$arg0$true$arg0$arg1$arg0  ;
  wire \f$false$bool$f$arg0$true$arg0  = \f$false$bool$f$arg0$true$arg0$arg0  && \f$false$bool$f$arg0$true$arg0$arg1  ;
  wire \f$false$bool$f$arg0$true$arg1  = 1'd0 ;
  wire \f$false$bool$f$arg0$true  = \f$false$bool$f$arg0$true$arg0  || \f$false$bool$f$arg0$true$arg1  ;
  wire \f$false$bool$f$arg0$false$bool  = 1'd0 ;
  wire[1:0] \f$false$bool$f$arg0$false$true$arg0$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$false$true$arg0$arg0$conj  = \f$false$bool$f$arg0$false$true$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$false$true$arg0$arg0  = \f$false$bool$f$arg0$false$true$arg0$arg0$conj [1:1] ;
  wire[0:0] \f$false$bool$f$arg0$false$true$arg0$arg1  = 1'd1 ;
  wire \f$false$bool$f$arg0$false$true$arg0  = \f$false$bool$f$arg0$false$true$arg0$arg0  > \f$false$bool$f$arg0$false$true$arg0$arg1  ;
  wire \f$false$bool$f$arg0$false$true$arg1$arg0  = 1'd1 ;
  wire[1:0] \f$false$bool$f$arg0$false$true$arg1$arg1$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$false$true$arg1$arg1$arg0$conj  = \f$false$bool$f$arg0$false$true$arg1$arg1$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$false$true$arg1$arg1$arg0  = \f$false$bool$f$arg0$false$true$arg1$arg1$arg0$conj [1:1] ;
  wire[0:0] \f$false$bool$f$arg0$false$true$arg1$arg1$arg1  = 1'd0 ;
  wire \f$false$bool$f$arg0$false$true$arg1$arg1  = \f$false$bool$f$arg0$false$true$arg1$arg1$arg0  == \f$false$bool$f$arg0$false$true$arg1$arg1$arg1  ;
  wire \f$false$bool$f$arg0$false$true$arg1  = \f$false$bool$f$arg0$false$true$arg1$arg0  && \f$false$bool$f$arg0$false$true$arg1$arg1  ;
  wire \f$false$bool$f$arg0$false$true  = \f$false$bool$f$arg0$false$true$arg0  || \f$false$bool$f$arg0$false$true$arg1  ;
  wire \f$false$bool$f$arg0$false$false$bool  = 1'd0 ;
  wire[1:0] \f$false$bool$f$arg0$false$false$true$arg0$arg0$arg0$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$false$false$true$arg0$arg0$arg0$arg0$conj  = \f$false$bool$f$arg0$false$false$true$arg0$arg0$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$false$false$true$arg0$arg0$arg0$arg0  = \f$false$bool$f$arg0$false$false$true$arg0$arg0$arg0$arg0$conj [0:0] ;
  wire[0:0] \f$false$bool$f$arg0$false$false$true$arg0$arg0$arg0$arg1  = 1'd0 ;
  wire \f$false$bool$f$arg0$false$false$true$arg0$arg0$arg0  = \f$false$bool$f$arg0$false$false$true$arg0$arg0$arg0$arg0  == \f$false$bool$f$arg0$false$false$true$arg0$arg0$arg0$arg1  ;
  wire \f$false$bool$f$arg0$false$false$true$arg0$arg0  = !\f$false$bool$f$arg0$false$false$true$arg0$arg0$arg0  ;
  wire[1:0] \f$false$bool$f$arg0$false$false$true$arg0$arg1$arg0$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$false$false$true$arg0$arg1$arg0$arg0$conj  = \f$false$bool$f$arg0$false$false$true$arg0$arg1$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$false$false$true$arg0$arg1$arg0$arg0  = \f$false$bool$f$arg0$false$false$true$arg0$arg1$arg0$arg0$conj [0:0] ;
  wire[0:0] \f$false$bool$f$arg0$false$false$true$arg0$arg1$arg0$arg1  = 1'd0 ;
  wire \f$false$bool$f$arg0$false$false$true$arg0$arg1$arg0  = \f$false$bool$f$arg0$false$false$true$arg0$arg1$arg0$arg0  > \f$false$bool$f$arg0$false$false$true$arg0$arg1$arg0$arg1  ;
  wire \f$false$bool$f$arg0$false$false$true$arg0$arg1  = !\f$false$bool$f$arg0$false$false$true$arg0$arg1$arg0  ;
  wire \f$false$bool$f$arg0$false$false$true$arg0  = \f$false$bool$f$arg0$false$false$true$arg0$arg0  && \f$false$bool$f$arg0$false$false$true$arg0$arg1  ;
  wire \f$false$bool$f$arg0$false$false$true$arg1$arg0  = 1'd1 ;
  wire[1:0] \f$false$bool$f$arg0$false$false$true$arg1$arg1$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$false$false$true$arg1$arg1$arg0$conj  = \f$false$bool$f$arg0$false$false$true$arg1$arg1$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$false$false$true$arg1$arg1$arg0  = \f$false$bool$f$arg0$false$false$true$arg1$arg1$arg0$conj [0:0] ;
  wire[0:0] \f$false$bool$f$arg0$false$false$true$arg1$arg1$arg1  = 1'd1 ;
  wire \f$false$bool$f$arg0$false$false$true$arg1$arg1  = \f$false$bool$f$arg0$false$false$true$arg1$arg1$arg0  == \f$false$bool$f$arg0$false$false$true$arg1$arg1$arg1  ;
  wire \f$false$bool$f$arg0$false$false$true$arg1  = \f$false$bool$f$arg0$false$false$true$arg1$arg0  && \f$false$bool$f$arg0$false$false$true$arg1$arg1  ;
  wire \f$false$bool$f$arg0$false$false$true  = \f$false$bool$f$arg0$false$false$true$arg0  || \f$false$bool$f$arg0$false$false$true$arg1  ;
  wire[1:0] \f$false$bool$f$arg0$false$false$false$arg0$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$false$false$false$arg0$arg0$conj  = \f$false$bool$f$arg0$false$false$false$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$false$false$false$arg0$arg0  = \f$false$bool$f$arg0$false$false$false$arg0$arg0$conj [0:0] ;
  wire[0:0] \f$false$bool$f$arg0$false$false$false$arg0$arg1  = 1'd0 ;
  wire \f$false$bool$f$arg0$false$false$false$arg0  = \f$false$bool$f$arg0$false$false$false$arg0$arg0  > \f$false$bool$f$arg0$false$false$false$arg0$arg1  ;
  wire \f$false$bool$f$arg0$false$false$false$arg1  = 1'd0 ;
  wire \f$false$bool$f$arg0$false$false$false  = \f$false$bool$f$arg0$false$false$false$arg0  || \f$false$bool$f$arg0$false$false$false$arg1  ;
  wire \f$false$bool$f$arg0$false$false  = ( \f$false$bool$f$arg0$false$false$bool  ? \f$false$bool$f$arg0$false$false$true  : \f$false$bool$f$arg0$false$false$false  ) ;
  wire \f$false$bool$f$arg0$false  = ( \f$false$bool$f$arg0$false$bool  ? \f$false$bool$f$arg0$false$true  : \f$false$bool$f$arg0$false$false  ) ;
  wire \f$false$bool$f$arg0  = ( \f$false$bool$f$arg0$bool  ? \f$false$bool$f$arg0$true  : \f$false$bool$f$arg0$false  ) ;
  wire \f$false$bool$f  = !\f$false$bool$f$arg0  ;
  wire \f$false$bool  = \f$false$bool$f  ;
  wire[0:0] \f$false$true$content  = 1'd1 ;
  wire[0:0] \f$false$true  = \f$false$true$content  ;
  wire[0:0] \f$false$false$content  = 1'd0 ;
  wire[0:0] \f$false$false  = \f$false$false$content  ;
  wire[0:0] \f$false  = ( \f$false$bool  ? \f$false$true  : \f$false$false  ) ;
  wire[0:0] \f  = ( \f$bool  ? \f$true  : \f$false  ) ;
  
  assign \o0  = \f  ;
endmodule

module \OFUN_1$RECEPTION_1_0_3_2_Switch2 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , output [1:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[1:0] \f  = \i0$data  ;
  
  assign \o0  = \f  ;
endmodule

module \OFUN_2$RECEPTION_1_0_3_2_Switch2 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , output [1:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[1:0] \f  = \i0$data  ;
  
  assign \o0  = \f  ;
endmodule

module \RECEPTION_1_1_1_2 (
      input \clk , input \rst , input [63:0] \t 
    , input \input$irdy , input [1:0] \input$data , output \input$trdy 
    , output \bus_outs1$irdy , output [1:0] \bus_outs1$data , input \bus_outs1$trdy 
    , output \bus_outs2$irdy , output [1:0] \bus_outs2$data , input \bus_outs2$trdy 
    , output \bus_outs3$irdy , output [1:0] \bus_outs3$data , input \bus_outs3$trdy 
    , output \bus_outs4$irdy , output [0:0] \bus_outs4$data , input \bus_outs4$trdy 
    , input \CreditCounter1$PatientSource1$unbound_irdy 
    , input [0:0] \CreditCounter1$PatientSource1$unbound_data 
    , output \CreditCounter1$PatientSource1$trdy 
    , input \CreditCounter1$Sink1$unbound_trdy 
    , output \CreditCounter1$Sink1$irdy 
    , output [0:0] \CreditCounter1$Sink1$data 
  );
  
  //
  // Channel declarations
  //
  wire \noCONS$irdy  ;
  wire [1:0] \noCONS$data  ;
  wire \noCONS$trdy  ;
  wire \toRCP$irdy  ;
  wire [1:0] \toRCP$data  ;
  wire \toRCP$trdy  ;
  wire \creditBack$irdy  ;
  wire [1:0] \creditBack$data  ;
  wire \creditBack$trdy  ;
  wire \channel1$irdy  ;
  wire [1:0] \channel1$data  ;
  wire \channel1$trdy  ;
  
  //
  // Function Channels
  //
  wire \sfunchan_0_Switch1$data  ;
  wire [1:0] \ofunchan_1_Switch1$data  ;
  wire [1:0] \ofunchan_2_Switch1$data  ;
  wire \sfunchan_0_Switch2$data  ;
  wire [1:0] \ofunchan_1_Switch2$data  ;
  wire [1:0] \ofunchan_2_Switch2$data  ;
  
  //
  // Component and Macro instantiations
  //
  \Fork2  #(
    .DATASIZE(2)
  ) \Fork1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\channel1$irdy )
    , .\i0$data (\channel1$data )
    , .\i0$trdy (\channel1$trdy )
    , .\o0$irdy (\toRCP$irdy )
    , .\o0$data (\toRCP$data )
    , .\o0$trdy (\toRCP$trdy )
    , .\o1$irdy (\creditBack$irdy )
    , .\o1$data (\creditBack$data )
    , .\o1$trdy (\creditBack$trdy )
  );
  
  \Queue  #(
    .NUM_DATA(0),
    .DATASIZE(2),
    .LENGTH(2)
  ) \Queue1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\input$irdy )
    , .\i0$data (\input$data )
    , .\i0$trdy (\input$trdy )
    , .\o0$irdy (\channel1$irdy )
    , .\o0$data (\channel1$data )
    , .\o0$trdy (\channel1$trdy )
  );
  
  \Switch2  #(
    .OUTPUTSIZE0(2),
    .OUTPUTSIZE1(2),
    .INPUTSIZE(2)
  ) \Switch1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\toRCP$irdy )
    , .\i0$data (\toRCP$data )
    , .\i0$trdy (\toRCP$trdy )
    , .\o0$irdy (\bus_outs1$irdy )
    , .\o0$data (\bus_outs1$data )
    , .\o0$trdy (\bus_outs1$trdy )
    , .\o1$irdy (\noCONS$irdy )
    , .\o1$data (\noCONS$data )
    , .\o1$trdy (\noCONS$trdy )
    , .\sel$data (\sfunchan_0_Switch1$data )
    , .\f0$data (\ofunchan_1_Switch1$data )
    , .\f1$data (\ofunchan_2_Switch1$data )
  );
  
  \SFUN_0$RECEPTION_1_1_1_2_Switch1  \sfun_0_Switch1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\toRCP$data )
    , .\o0 (\sfunchan_0_Switch1$data )
  );
  
  \OFUN_1$RECEPTION_1_1_1_2_Switch1  \ofun_1_Switch1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\toRCP$data )
    , .\o0 (\ofunchan_1_Switch1$data )
  );
  
  \OFUN_2$RECEPTION_1_1_1_2_Switch1  \ofun_2_Switch1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\toRCP$data )
    , .\o0 (\ofunchan_2_Switch1$data )
  );
  
  \Switch2  #(
    .OUTPUTSIZE0(2),
    .OUTPUTSIZE1(2),
    .INPUTSIZE(2)
  ) \Switch2  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\noCONS$irdy )
    , .\i0$data (\noCONS$data )
    , .\i0$trdy (\noCONS$trdy )
    , .\o0$irdy (\bus_outs2$irdy )
    , .\o0$data (\bus_outs2$data )
    , .\o0$trdy (\bus_outs2$trdy )
    , .\o1$irdy (\bus_outs3$irdy )
    , .\o1$data (\bus_outs3$data )
    , .\o1$trdy (\bus_outs3$trdy )
    , .\sel$data (\sfunchan_0_Switch2$data )
    , .\f0$data (\ofunchan_1_Switch2$data )
    , .\f1$data (\ofunchan_2_Switch2$data )
  );
  
  \SFUN_0$RECEPTION_1_1_1_2_Switch2  \sfun_0_Switch2  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\noCONS$data )
    , .\o0 (\sfunchan_0_Switch2$data )
  );
  
  \OFUN_1$RECEPTION_1_1_1_2_Switch2  \ofun_1_Switch2  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\noCONS$data )
    , .\o0 (\ofunchan_1_Switch2$data )
  );
  
  \OFUN_2$RECEPTION_1_1_1_2_Switch2  \ofun_2_Switch2  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\noCONS$data )
    , .\o0 (\ofunchan_2_Switch2$data )
  );
  
  \CreditCounter_2  \CreditCounter1  (
      .\clk (\clk ), .\rst (\rst ), .\t (\t )
    , .\i$irdy (\creditBack$irdy )
    , .\i$data (\creditBack$data )
    , .\i$trdy (\creditBack$trdy )
    , .\o$irdy (\bus_outs4$irdy )
    , .\o$data (\bus_outs4$data )
    , .\o$trdy (\bus_outs4$trdy )
    , .\PatientSource1$unbound_irdy (\CreditCounter1$PatientSource1$unbound_irdy )
    , .\PatientSource1$unbound_data (\CreditCounter1$PatientSource1$unbound_data )
    , .\PatientSource1$trdy (\CreditCounter1$PatientSource1$trdy )
    , .\Sink1$unbound_trdy (\CreditCounter1$Sink1$unbound_trdy )
    , .\Sink1$irdy (\CreditCounter1$Sink1$irdy )
    , .\Sink1$data (\CreditCounter1$Sink1$data )
  );
  
endmodule


//
// RECEPTION_1_1_1_2 switch functions
//
module \SFUN_0$RECEPTION_1_1_1_2_Switch1 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , output [0:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[1:0] \f$bool$g0  = \i0$data  ;
  wire[1:0] \f$bool$f$arg0$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$arg0$arg0$conj  = \f$bool$f$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$arg0$arg0  = \f$bool$f$arg0$arg0$conj [1:1] ;
  wire[0:0] \f$bool$f$arg0$arg1  = 1'd1 ;
  wire \f$bool$f$arg0  = \f$bool$f$arg0$arg0  == \f$bool$f$arg0$arg1  ;
  wire[1:0] \f$bool$f$arg1$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$arg1$arg0$conj  = \f$bool$f$arg1$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$arg1$arg0  = \f$bool$f$arg1$arg0$conj [0:0] ;
  wire[0:0] \f$bool$f$arg1$arg1  = 1'd1 ;
  wire \f$bool$f$arg1  = \f$bool$f$arg1$arg0  == \f$bool$f$arg1$arg1  ;
  wire \f$bool$f  = \f$bool$f$arg0  && \f$bool$f$arg1  ;
  wire \f$bool  = \f$bool$f  ;
  wire[0:0] \f$true$content  = 1'd0 ;
  wire[0:0] \f$true  = \f$true$content  ;
  wire[1:0] \f$false$bool$g0  = \i0$data  ;
  wire[1:0] \f$false$bool$f$arg0$arg0$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$arg0$arg0$conj  = \f$false$bool$f$arg0$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$arg0$arg0  = \f$false$bool$f$arg0$arg0$arg0$conj [1:1] ;
  wire[0:0] \f$false$bool$f$arg0$arg0$arg1  = 1'd1 ;
  wire \f$false$bool$f$arg0$arg0  = \f$false$bool$f$arg0$arg0$arg0  == \f$false$bool$f$arg0$arg0$arg1  ;
  wire[1:0] \f$false$bool$f$arg0$arg1$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$arg1$arg0$conj  = \f$false$bool$f$arg0$arg1$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$arg1$arg0  = \f$false$bool$f$arg0$arg1$arg0$conj [0:0] ;
  wire[0:0] \f$false$bool$f$arg0$arg1$arg1  = 1'd1 ;
  wire \f$false$bool$f$arg0$arg1  = \f$false$bool$f$arg0$arg1$arg0  == \f$false$bool$f$arg0$arg1$arg1  ;
  wire \f$false$bool$f$arg0  = \f$false$bool$f$arg0$arg0  && \f$false$bool$f$arg0$arg1  ;
  wire \f$false$bool$f  = !\f$false$bool$f$arg0  ;
  wire \f$false$bool  = \f$false$bool$f  ;
  wire[0:0] \f$false$true$content  = 1'd1 ;
  wire[0:0] \f$false$true  = \f$false$true$content  ;
  wire[0:0] \f$false$false$content  = 1'd0 ;
  wire[0:0] \f$false$false  = \f$false$false$content  ;
  wire[0:0] \f$false  = ( \f$false$bool  ? \f$false$true  : \f$false$false  ) ;
  wire[0:0] \f  = ( \f$bool  ? \f$true  : \f$false  ) ;
  
  assign \o0  = \f  ;
endmodule

module \OFUN_1$RECEPTION_1_1_1_2_Switch1 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , output [1:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[1:0] \f  = \i0$data  ;
  
  assign \o0  = \f  ;
endmodule

module \OFUN_2$RECEPTION_1_1_1_2_Switch1 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , output [1:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[1:0] \f  = \i0$data  ;
  
  assign \o0  = \f  ;
endmodule

module \SFUN_0$RECEPTION_1_1_1_2_Switch2 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , output [0:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[1:0] \f$bool$g0  = \i0$data  ;
  wire \f$bool$f$bool  = 1'd0 ;
  wire[1:0] \f$bool$f$true$arg0$arg0$arg0$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$true$arg0$arg0$arg0$arg0$conj  = \f$bool$f$true$arg0$arg0$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$true$arg0$arg0$arg0$arg0  = \f$bool$f$true$arg0$arg0$arg0$arg0$conj [1:1] ;
  wire[0:0] \f$bool$f$true$arg0$arg0$arg0$arg1  = 1'd1 ;
  wire \f$bool$f$true$arg0$arg0$arg0  = \f$bool$f$true$arg0$arg0$arg0$arg0  == \f$bool$f$true$arg0$arg0$arg0$arg1  ;
  wire \f$bool$f$true$arg0$arg0  = !\f$bool$f$true$arg0$arg0$arg0  ;
  wire[1:0] \f$bool$f$true$arg0$arg1$arg0$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$true$arg0$arg1$arg0$arg0$conj  = \f$bool$f$true$arg0$arg1$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$true$arg0$arg1$arg0$arg0  = \f$bool$f$true$arg0$arg1$arg0$arg0$conj [1:1] ;
  wire[0:0] \f$bool$f$true$arg0$arg1$arg0$arg1  = 1'd1 ;
  wire \f$bool$f$true$arg0$arg1$arg0  = \f$bool$f$true$arg0$arg1$arg0$arg0  > \f$bool$f$true$arg0$arg1$arg0$arg1  ;
  wire \f$bool$f$true$arg0$arg1  = !\f$bool$f$true$arg0$arg1$arg0  ;
  wire \f$bool$f$true$arg0  = \f$bool$f$true$arg0$arg0  && \f$bool$f$true$arg0$arg1  ;
  wire \f$bool$f$true$arg1  = 1'd0 ;
  wire \f$bool$f$true  = \f$bool$f$true$arg0  || \f$bool$f$true$arg1  ;
  wire \f$bool$f$false$bool  = 1'd1 ;
  wire[1:0] \f$bool$f$false$true$arg0$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$false$true$arg0$arg0$conj  = \f$bool$f$false$true$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$false$true$arg0$arg0  = \f$bool$f$false$true$arg0$arg0$conj [1:1] ;
  wire[0:0] \f$bool$f$false$true$arg0$arg1  = 1'd1 ;
  wire \f$bool$f$false$true$arg0  = \f$bool$f$false$true$arg0$arg0  > \f$bool$f$false$true$arg0$arg1  ;
  wire \f$bool$f$false$true$arg1$arg0  = 1'd1 ;
  wire[1:0] \f$bool$f$false$true$arg1$arg1$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$false$true$arg1$arg1$arg0$conj  = \f$bool$f$false$true$arg1$arg1$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$false$true$arg1$arg1$arg0  = \f$bool$f$false$true$arg1$arg1$arg0$conj [1:1] ;
  wire[0:0] \f$bool$f$false$true$arg1$arg1$arg1  = 1'd0 ;
  wire \f$bool$f$false$true$arg1$arg1  = \f$bool$f$false$true$arg1$arg1$arg0  == \f$bool$f$false$true$arg1$arg1$arg1  ;
  wire \f$bool$f$false$true$arg1  = \f$bool$f$false$true$arg1$arg0  && \f$bool$f$false$true$arg1$arg1  ;
  wire \f$bool$f$false$true  = \f$bool$f$false$true$arg0  || \f$bool$f$false$true$arg1  ;
  wire \f$bool$f$false$false$bool  = 1'd0 ;
  wire[1:0] \f$bool$f$false$false$true$arg0$arg0$arg0$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$false$false$true$arg0$arg0$arg0$arg0$conj  = \f$bool$f$false$false$true$arg0$arg0$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$false$false$true$arg0$arg0$arg0$arg0  = \f$bool$f$false$false$true$arg0$arg0$arg0$arg0$conj [0:0] ;
  wire[0:0] \f$bool$f$false$false$true$arg0$arg0$arg0$arg1  = 1'd1 ;
  wire \f$bool$f$false$false$true$arg0$arg0$arg0  = \f$bool$f$false$false$true$arg0$arg0$arg0$arg0  == \f$bool$f$false$false$true$arg0$arg0$arg0$arg1  ;
  wire \f$bool$f$false$false$true$arg0$arg0  = !\f$bool$f$false$false$true$arg0$arg0$arg0  ;
  wire[1:0] \f$bool$f$false$false$true$arg0$arg1$arg0$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$false$false$true$arg0$arg1$arg0$arg0$conj  = \f$bool$f$false$false$true$arg0$arg1$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$false$false$true$arg0$arg1$arg0$arg0  = \f$bool$f$false$false$true$arg0$arg1$arg0$arg0$conj [0:0] ;
  wire[0:0] \f$bool$f$false$false$true$arg0$arg1$arg0$arg1  = 1'd1 ;
  wire \f$bool$f$false$false$true$arg0$arg1$arg0  = \f$bool$f$false$false$true$arg0$arg1$arg0$arg0  > \f$bool$f$false$false$true$arg0$arg1$arg0$arg1  ;
  wire \f$bool$f$false$false$true$arg0$arg1  = !\f$bool$f$false$false$true$arg0$arg1$arg0  ;
  wire \f$bool$f$false$false$true$arg0  = \f$bool$f$false$false$true$arg0$arg0  && \f$bool$f$false$false$true$arg0$arg1  ;
  wire \f$bool$f$false$false$true$arg1  = 1'd0 ;
  wire \f$bool$f$false$false$true  = \f$bool$f$false$false$true$arg0  || \f$bool$f$false$false$true$arg1  ;
  wire[1:0] \f$bool$f$false$false$false$arg0$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$false$false$false$arg0$arg0$conj  = \f$bool$f$false$false$false$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$false$false$false$arg0$arg0  = \f$bool$f$false$false$false$arg0$arg0$conj [0:0] ;
  wire[0:0] \f$bool$f$false$false$false$arg0$arg1  = 1'd1 ;
  wire \f$bool$f$false$false$false$arg0  = \f$bool$f$false$false$false$arg0$arg0  > \f$bool$f$false$false$false$arg0$arg1  ;
  wire \f$bool$f$false$false$false$arg1$arg0  = 1'd1 ;
  wire[1:0] \f$bool$f$false$false$false$arg1$arg1$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$false$false$false$arg1$arg1$arg0$conj  = \f$bool$f$false$false$false$arg1$arg1$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$false$false$false$arg1$arg1$arg0  = \f$bool$f$false$false$false$arg1$arg1$arg0$conj [0:0] ;
  wire[0:0] \f$bool$f$false$false$false$arg1$arg1$arg1  = 1'd0 ;
  wire \f$bool$f$false$false$false$arg1$arg1  = \f$bool$f$false$false$false$arg1$arg1$arg0  == \f$bool$f$false$false$false$arg1$arg1$arg1  ;
  wire \f$bool$f$false$false$false$arg1  = \f$bool$f$false$false$false$arg1$arg0  && \f$bool$f$false$false$false$arg1$arg1  ;
  wire \f$bool$f$false$false$false  = \f$bool$f$false$false$false$arg0  || \f$bool$f$false$false$false$arg1  ;
  wire \f$bool$f$false$false  = ( \f$bool$f$false$false$bool  ? \f$bool$f$false$false$true  : \f$bool$f$false$false$false  ) ;
  wire \f$bool$f$false  = ( \f$bool$f$false$bool  ? \f$bool$f$false$true  : \f$bool$f$false$false  ) ;
  wire \f$bool$f  = ( \f$bool$f$bool  ? \f$bool$f$true  : \f$bool$f$false  ) ;
  wire \f$bool  = \f$bool$f  ;
  wire[0:0] \f$true$content  = 1'd0 ;
  wire[0:0] \f$true  = \f$true$content  ;
  wire[1:0] \f$false$bool$g0  = \i0$data  ;
  wire \f$false$bool$f$arg0$bool  = 1'd0 ;
  wire[1:0] \f$false$bool$f$arg0$true$arg0$arg0$arg0$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$true$arg0$arg0$arg0$arg0$conj  = \f$false$bool$f$arg0$true$arg0$arg0$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$true$arg0$arg0$arg0$arg0  = \f$false$bool$f$arg0$true$arg0$arg0$arg0$arg0$conj [1:1] ;
  wire[0:0] \f$false$bool$f$arg0$true$arg0$arg0$arg0$arg1  = 1'd1 ;
  wire \f$false$bool$f$arg0$true$arg0$arg0$arg0  = \f$false$bool$f$arg0$true$arg0$arg0$arg0$arg0  == \f$false$bool$f$arg0$true$arg0$arg0$arg0$arg1  ;
  wire \f$false$bool$f$arg0$true$arg0$arg0  = !\f$false$bool$f$arg0$true$arg0$arg0$arg0  ;
  wire[1:0] \f$false$bool$f$arg0$true$arg0$arg1$arg0$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$true$arg0$arg1$arg0$arg0$conj  = \f$false$bool$f$arg0$true$arg0$arg1$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$true$arg0$arg1$arg0$arg0  = \f$false$bool$f$arg0$true$arg0$arg1$arg0$arg0$conj [1:1] ;
  wire[0:0] \f$false$bool$f$arg0$true$arg0$arg1$arg0$arg1  = 1'd1 ;
  wire \f$false$bool$f$arg0$true$arg0$arg1$arg0  = \f$false$bool$f$arg0$true$arg0$arg1$arg0$arg0  > \f$false$bool$f$arg0$true$arg0$arg1$arg0$arg1  ;
  wire \f$false$bool$f$arg0$true$arg0$arg1  = !\f$false$bool$f$arg0$true$arg0$arg1$arg0  ;
  wire \f$false$bool$f$arg0$true$arg0  = \f$false$bool$f$arg0$true$arg0$arg0  && \f$false$bool$f$arg0$true$arg0$arg1  ;
  wire \f$false$bool$f$arg0$true$arg1  = 1'd0 ;
  wire \f$false$bool$f$arg0$true  = \f$false$bool$f$arg0$true$arg0  || \f$false$bool$f$arg0$true$arg1  ;
  wire \f$false$bool$f$arg0$false$bool  = 1'd1 ;
  wire[1:0] \f$false$bool$f$arg0$false$true$arg0$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$false$true$arg0$arg0$conj  = \f$false$bool$f$arg0$false$true$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$false$true$arg0$arg0  = \f$false$bool$f$arg0$false$true$arg0$arg0$conj [1:1] ;
  wire[0:0] \f$false$bool$f$arg0$false$true$arg0$arg1  = 1'd1 ;
  wire \f$false$bool$f$arg0$false$true$arg0  = \f$false$bool$f$arg0$false$true$arg0$arg0  > \f$false$bool$f$arg0$false$true$arg0$arg1  ;
  wire \f$false$bool$f$arg0$false$true$arg1$arg0  = 1'd1 ;
  wire[1:0] \f$false$bool$f$arg0$false$true$arg1$arg1$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$false$true$arg1$arg1$arg0$conj  = \f$false$bool$f$arg0$false$true$arg1$arg1$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$false$true$arg1$arg1$arg0  = \f$false$bool$f$arg0$false$true$arg1$arg1$arg0$conj [1:1] ;
  wire[0:0] \f$false$bool$f$arg0$false$true$arg1$arg1$arg1  = 1'd0 ;
  wire \f$false$bool$f$arg0$false$true$arg1$arg1  = \f$false$bool$f$arg0$false$true$arg1$arg1$arg0  == \f$false$bool$f$arg0$false$true$arg1$arg1$arg1  ;
  wire \f$false$bool$f$arg0$false$true$arg1  = \f$false$bool$f$arg0$false$true$arg1$arg0  && \f$false$bool$f$arg0$false$true$arg1$arg1  ;
  wire \f$false$bool$f$arg0$false$true  = \f$false$bool$f$arg0$false$true$arg0  || \f$false$bool$f$arg0$false$true$arg1  ;
  wire \f$false$bool$f$arg0$false$false$bool  = 1'd0 ;
  wire[1:0] \f$false$bool$f$arg0$false$false$true$arg0$arg0$arg0$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$false$false$true$arg0$arg0$arg0$arg0$conj  = \f$false$bool$f$arg0$false$false$true$arg0$arg0$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$false$false$true$arg0$arg0$arg0$arg0  = \f$false$bool$f$arg0$false$false$true$arg0$arg0$arg0$arg0$conj [0:0] ;
  wire[0:0] \f$false$bool$f$arg0$false$false$true$arg0$arg0$arg0$arg1  = 1'd1 ;
  wire \f$false$bool$f$arg0$false$false$true$arg0$arg0$arg0  = \f$false$bool$f$arg0$false$false$true$arg0$arg0$arg0$arg0  == \f$false$bool$f$arg0$false$false$true$arg0$arg0$arg0$arg1  ;
  wire \f$false$bool$f$arg0$false$false$true$arg0$arg0  = !\f$false$bool$f$arg0$false$false$true$arg0$arg0$arg0  ;
  wire[1:0] \f$false$bool$f$arg0$false$false$true$arg0$arg1$arg0$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$false$false$true$arg0$arg1$arg0$arg0$conj  = \f$false$bool$f$arg0$false$false$true$arg0$arg1$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$false$false$true$arg0$arg1$arg0$arg0  = \f$false$bool$f$arg0$false$false$true$arg0$arg1$arg0$arg0$conj [0:0] ;
  wire[0:0] \f$false$bool$f$arg0$false$false$true$arg0$arg1$arg0$arg1  = 1'd1 ;
  wire \f$false$bool$f$arg0$false$false$true$arg0$arg1$arg0  = \f$false$bool$f$arg0$false$false$true$arg0$arg1$arg0$arg0  > \f$false$bool$f$arg0$false$false$true$arg0$arg1$arg0$arg1  ;
  wire \f$false$bool$f$arg0$false$false$true$arg0$arg1  = !\f$false$bool$f$arg0$false$false$true$arg0$arg1$arg0  ;
  wire \f$false$bool$f$arg0$false$false$true$arg0  = \f$false$bool$f$arg0$false$false$true$arg0$arg0  && \f$false$bool$f$arg0$false$false$true$arg0$arg1  ;
  wire \f$false$bool$f$arg0$false$false$true$arg1  = 1'd0 ;
  wire \f$false$bool$f$arg0$false$false$true  = \f$false$bool$f$arg0$false$false$true$arg0  || \f$false$bool$f$arg0$false$false$true$arg1  ;
  wire[1:0] \f$false$bool$f$arg0$false$false$false$arg0$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$false$false$false$arg0$arg0$conj  = \f$false$bool$f$arg0$false$false$false$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$false$false$false$arg0$arg0  = \f$false$bool$f$arg0$false$false$false$arg0$arg0$conj [0:0] ;
  wire[0:0] \f$false$bool$f$arg0$false$false$false$arg0$arg1  = 1'd1 ;
  wire \f$false$bool$f$arg0$false$false$false$arg0  = \f$false$bool$f$arg0$false$false$false$arg0$arg0  > \f$false$bool$f$arg0$false$false$false$arg0$arg1  ;
  wire \f$false$bool$f$arg0$false$false$false$arg1$arg0  = 1'd1 ;
  wire[1:0] \f$false$bool$f$arg0$false$false$false$arg1$arg1$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$false$false$false$arg1$arg1$arg0$conj  = \f$false$bool$f$arg0$false$false$false$arg1$arg1$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$false$false$false$arg1$arg1$arg0  = \f$false$bool$f$arg0$false$false$false$arg1$arg1$arg0$conj [0:0] ;
  wire[0:0] \f$false$bool$f$arg0$false$false$false$arg1$arg1$arg1  = 1'd0 ;
  wire \f$false$bool$f$arg0$false$false$false$arg1$arg1  = \f$false$bool$f$arg0$false$false$false$arg1$arg1$arg0  == \f$false$bool$f$arg0$false$false$false$arg1$arg1$arg1  ;
  wire \f$false$bool$f$arg0$false$false$false$arg1  = \f$false$bool$f$arg0$false$false$false$arg1$arg0  && \f$false$bool$f$arg0$false$false$false$arg1$arg1  ;
  wire \f$false$bool$f$arg0$false$false$false  = \f$false$bool$f$arg0$false$false$false$arg0  || \f$false$bool$f$arg0$false$false$false$arg1  ;
  wire \f$false$bool$f$arg0$false$false  = ( \f$false$bool$f$arg0$false$false$bool  ? \f$false$bool$f$arg0$false$false$true  : \f$false$bool$f$arg0$false$false$false  ) ;
  wire \f$false$bool$f$arg0$false  = ( \f$false$bool$f$arg0$false$bool  ? \f$false$bool$f$arg0$false$true  : \f$false$bool$f$arg0$false$false  ) ;
  wire \f$false$bool$f$arg0  = ( \f$false$bool$f$arg0$bool  ? \f$false$bool$f$arg0$true  : \f$false$bool$f$arg0$false  ) ;
  wire \f$false$bool$f  = !\f$false$bool$f$arg0  ;
  wire \f$false$bool  = \f$false$bool$f  ;
  wire[0:0] \f$false$true$content  = 1'd1 ;
  wire[0:0] \f$false$true  = \f$false$true$content  ;
  wire[0:0] \f$false$false$content  = 1'd0 ;
  wire[0:0] \f$false$false  = \f$false$false$content  ;
  wire[0:0] \f$false  = ( \f$false$bool  ? \f$false$true  : \f$false$false  ) ;
  wire[0:0] \f  = ( \f$bool  ? \f$true  : \f$false  ) ;
  
  assign \o0  = \f  ;
endmodule

module \OFUN_1$RECEPTION_1_1_1_2_Switch2 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , output [1:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[1:0] \f  = \i0$data  ;
  
  assign \o0  = \f  ;
endmodule

module \OFUN_2$RECEPTION_1_1_1_2_Switch2 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , output [1:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[1:0] \f  = \i0$data  ;
  
  assign \o0  = \f  ;
endmodule

module \RECEPTION_0_0_1_2 (
      input \clk , input \rst , input [63:0] \t 
    , input \input$irdy , input [1:0] \input$data , output \input$trdy 
    , output \bus_outs1$irdy , output [1:0] \bus_outs1$data , input \bus_outs1$trdy 
    , output \bus_outs2$irdy , output [1:0] \bus_outs2$data , input \bus_outs2$trdy 
    , output \bus_outs3$irdy , output [1:0] \bus_outs3$data , input \bus_outs3$trdy 
    , output \bus_outs4$irdy , output [0:0] \bus_outs4$data , input \bus_outs4$trdy 
    , input \CreditCounter1$PatientSource1$unbound_irdy 
    , input [0:0] \CreditCounter1$PatientSource1$unbound_data 
    , output \CreditCounter1$PatientSource1$trdy 
    , input \CreditCounter1$Sink1$unbound_trdy 
    , output \CreditCounter1$Sink1$irdy 
    , output [0:0] \CreditCounter1$Sink1$data 
  );
  
  //
  // Channel declarations
  //
  wire \noCONS$irdy  ;
  wire [1:0] \noCONS$data  ;
  wire \noCONS$trdy  ;
  wire \toRCP$irdy  ;
  wire [1:0] \toRCP$data  ;
  wire \toRCP$trdy  ;
  wire \creditBack$irdy  ;
  wire [1:0] \creditBack$data  ;
  wire \creditBack$trdy  ;
  wire \channel1$irdy  ;
  wire [1:0] \channel1$data  ;
  wire \channel1$trdy  ;
  
  //
  // Function Channels
  //
  wire \sfunchan_0_Switch1$data  ;
  wire [1:0] \ofunchan_1_Switch1$data  ;
  wire [1:0] \ofunchan_2_Switch1$data  ;
  wire \sfunchan_0_Switch2$data  ;
  wire [1:0] \ofunchan_1_Switch2$data  ;
  wire [1:0] \ofunchan_2_Switch2$data  ;
  
  //
  // Component and Macro instantiations
  //
  \Fork2  #(
    .DATASIZE(2)
  ) \Fork1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\channel1$irdy )
    , .\i0$data (\channel1$data )
    , .\i0$trdy (\channel1$trdy )
    , .\o0$irdy (\toRCP$irdy )
    , .\o0$data (\toRCP$data )
    , .\o0$trdy (\toRCP$trdy )
    , .\o1$irdy (\creditBack$irdy )
    , .\o1$data (\creditBack$data )
    , .\o1$trdy (\creditBack$trdy )
  );
  
  \Queue  #(
    .NUM_DATA(0),
    .DATASIZE(2),
    .LENGTH(2)
  ) \Queue1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\input$irdy )
    , .\i0$data (\input$data )
    , .\i0$trdy (\input$trdy )
    , .\o0$irdy (\channel1$irdy )
    , .\o0$data (\channel1$data )
    , .\o0$trdy (\channel1$trdy )
  );
  
  \Switch2  #(
    .OUTPUTSIZE0(2),
    .OUTPUTSIZE1(2),
    .INPUTSIZE(2)
  ) \Switch1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\toRCP$irdy )
    , .\i0$data (\toRCP$data )
    , .\i0$trdy (\toRCP$trdy )
    , .\o0$irdy (\bus_outs1$irdy )
    , .\o0$data (\bus_outs1$data )
    , .\o0$trdy (\bus_outs1$trdy )
    , .\o1$irdy (\noCONS$irdy )
    , .\o1$data (\noCONS$data )
    , .\o1$trdy (\noCONS$trdy )
    , .\sel$data (\sfunchan_0_Switch1$data )
    , .\f0$data (\ofunchan_1_Switch1$data )
    , .\f1$data (\ofunchan_2_Switch1$data )
  );
  
  \SFUN_0$RECEPTION_0_0_1_2_Switch1  \sfun_0_Switch1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\toRCP$data )
    , .\o0 (\sfunchan_0_Switch1$data )
  );
  
  \OFUN_1$RECEPTION_0_0_1_2_Switch1  \ofun_1_Switch1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\toRCP$data )
    , .\o0 (\ofunchan_1_Switch1$data )
  );
  
  \OFUN_2$RECEPTION_0_0_1_2_Switch1  \ofun_2_Switch1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\toRCP$data )
    , .\o0 (\ofunchan_2_Switch1$data )
  );
  
  \Switch2  #(
    .OUTPUTSIZE0(2),
    .OUTPUTSIZE1(2),
    .INPUTSIZE(2)
  ) \Switch2  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\noCONS$irdy )
    , .\i0$data (\noCONS$data )
    , .\i0$trdy (\noCONS$trdy )
    , .\o0$irdy (\bus_outs2$irdy )
    , .\o0$data (\bus_outs2$data )
    , .\o0$trdy (\bus_outs2$trdy )
    , .\o1$irdy (\bus_outs3$irdy )
    , .\o1$data (\bus_outs3$data )
    , .\o1$trdy (\bus_outs3$trdy )
    , .\sel$data (\sfunchan_0_Switch2$data )
    , .\f0$data (\ofunchan_1_Switch2$data )
    , .\f1$data (\ofunchan_2_Switch2$data )
  );
  
  \SFUN_0$RECEPTION_0_0_1_2_Switch2  \sfun_0_Switch2  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\noCONS$data )
    , .\o0 (\sfunchan_0_Switch2$data )
  );
  
  \OFUN_1$RECEPTION_0_0_1_2_Switch2  \ofun_1_Switch2  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\noCONS$data )
    , .\o0 (\ofunchan_1_Switch2$data )
  );
  
  \OFUN_2$RECEPTION_0_0_1_2_Switch2  \ofun_2_Switch2  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\noCONS$data )
    , .\o0 (\ofunchan_2_Switch2$data )
  );
  
  \CreditCounter_2  \CreditCounter1  (
      .\clk (\clk ), .\rst (\rst ), .\t (\t )
    , .\i$irdy (\creditBack$irdy )
    , .\i$data (\creditBack$data )
    , .\i$trdy (\creditBack$trdy )
    , .\o$irdy (\bus_outs4$irdy )
    , .\o$data (\bus_outs4$data )
    , .\o$trdy (\bus_outs4$trdy )
    , .\PatientSource1$unbound_irdy (\CreditCounter1$PatientSource1$unbound_irdy )
    , .\PatientSource1$unbound_data (\CreditCounter1$PatientSource1$unbound_data )
    , .\PatientSource1$trdy (\CreditCounter1$PatientSource1$trdy )
    , .\Sink1$unbound_trdy (\CreditCounter1$Sink1$unbound_trdy )
    , .\Sink1$irdy (\CreditCounter1$Sink1$irdy )
    , .\Sink1$data (\CreditCounter1$Sink1$data )
  );
  
endmodule


//
// RECEPTION_0_0_1_2 switch functions
//
module \SFUN_0$RECEPTION_0_0_1_2_Switch1 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , output [0:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[1:0] \f$bool$g0  = \i0$data  ;
  wire[1:0] \f$bool$f$arg0$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$arg0$arg0$conj  = \f$bool$f$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$arg0$arg0  = \f$bool$f$arg0$arg0$conj [1:1] ;
  wire[0:0] \f$bool$f$arg0$arg1  = 1'd0 ;
  wire \f$bool$f$arg0  = \f$bool$f$arg0$arg0  == \f$bool$f$arg0$arg1  ;
  wire[1:0] \f$bool$f$arg1$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$arg1$arg0$conj  = \f$bool$f$arg1$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$arg1$arg0  = \f$bool$f$arg1$arg0$conj [0:0] ;
  wire[0:0] \f$bool$f$arg1$arg1  = 1'd0 ;
  wire \f$bool$f$arg1  = \f$bool$f$arg1$arg0  == \f$bool$f$arg1$arg1  ;
  wire \f$bool$f  = \f$bool$f$arg0  && \f$bool$f$arg1  ;
  wire \f$bool  = \f$bool$f  ;
  wire[0:0] \f$true$content  = 1'd0 ;
  wire[0:0] \f$true  = \f$true$content  ;
  wire[1:0] \f$false$bool$g0  = \i0$data  ;
  wire[1:0] \f$false$bool$f$arg0$arg0$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$arg0$arg0$conj  = \f$false$bool$f$arg0$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$arg0$arg0  = \f$false$bool$f$arg0$arg0$arg0$conj [1:1] ;
  wire[0:0] \f$false$bool$f$arg0$arg0$arg1  = 1'd0 ;
  wire \f$false$bool$f$arg0$arg0  = \f$false$bool$f$arg0$arg0$arg0  == \f$false$bool$f$arg0$arg0$arg1  ;
  wire[1:0] \f$false$bool$f$arg0$arg1$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$arg1$arg0$conj  = \f$false$bool$f$arg0$arg1$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$arg1$arg0  = \f$false$bool$f$arg0$arg1$arg0$conj [0:0] ;
  wire[0:0] \f$false$bool$f$arg0$arg1$arg1  = 1'd0 ;
  wire \f$false$bool$f$arg0$arg1  = \f$false$bool$f$arg0$arg1$arg0  == \f$false$bool$f$arg0$arg1$arg1  ;
  wire \f$false$bool$f$arg0  = \f$false$bool$f$arg0$arg0  && \f$false$bool$f$arg0$arg1  ;
  wire \f$false$bool$f  = !\f$false$bool$f$arg0  ;
  wire \f$false$bool  = \f$false$bool$f  ;
  wire[0:0] \f$false$true$content  = 1'd1 ;
  wire[0:0] \f$false$true  = \f$false$true$content  ;
  wire[0:0] \f$false$false$content  = 1'd0 ;
  wire[0:0] \f$false$false  = \f$false$false$content  ;
  wire[0:0] \f$false  = ( \f$false$bool  ? \f$false$true  : \f$false$false  ) ;
  wire[0:0] \f  = ( \f$bool  ? \f$true  : \f$false  ) ;
  
  assign \o0  = \f  ;
endmodule

module \OFUN_1$RECEPTION_0_0_1_2_Switch1 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , output [1:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[1:0] \f  = \i0$data  ;
  
  assign \o0  = \f  ;
endmodule

module \OFUN_2$RECEPTION_0_0_1_2_Switch1 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , output [1:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[1:0] \f  = \i0$data  ;
  
  assign \o0  = \f  ;
endmodule

module \SFUN_0$RECEPTION_0_0_1_2_Switch2 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , output [0:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[1:0] \f$bool$g0  = \i0$data  ;
  wire \f$bool$f$bool  = 1'd0 ;
  wire[1:0] \f$bool$f$true$arg0$arg0$arg0$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$true$arg0$arg0$arg0$arg0$conj  = \f$bool$f$true$arg0$arg0$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$true$arg0$arg0$arg0$arg0  = \f$bool$f$true$arg0$arg0$arg0$arg0$conj [1:1] ;
  wire[0:0] \f$bool$f$true$arg0$arg0$arg0$arg1  = 1'd0 ;
  wire \f$bool$f$true$arg0$arg0$arg0  = \f$bool$f$true$arg0$arg0$arg0$arg0  == \f$bool$f$true$arg0$arg0$arg0$arg1  ;
  wire \f$bool$f$true$arg0$arg0  = !\f$bool$f$true$arg0$arg0$arg0  ;
  wire[1:0] \f$bool$f$true$arg0$arg1$arg0$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$true$arg0$arg1$arg0$arg0$conj  = \f$bool$f$true$arg0$arg1$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$true$arg0$arg1$arg0$arg0  = \f$bool$f$true$arg0$arg1$arg0$arg0$conj [1:1] ;
  wire[0:0] \f$bool$f$true$arg0$arg1$arg0$arg1  = 1'd0 ;
  wire \f$bool$f$true$arg0$arg1$arg0  = \f$bool$f$true$arg0$arg1$arg0$arg0  > \f$bool$f$true$arg0$arg1$arg0$arg1  ;
  wire \f$bool$f$true$arg0$arg1  = !\f$bool$f$true$arg0$arg1$arg0  ;
  wire \f$bool$f$true$arg0  = \f$bool$f$true$arg0$arg0  && \f$bool$f$true$arg0$arg1  ;
  wire \f$bool$f$true$arg1$arg0  = 1'd1 ;
  wire[1:0] \f$bool$f$true$arg1$arg1$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$true$arg1$arg1$arg0$conj  = \f$bool$f$true$arg1$arg1$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$true$arg1$arg1$arg0  = \f$bool$f$true$arg1$arg1$arg0$conj [1:1] ;
  wire[0:0] \f$bool$f$true$arg1$arg1$arg1  = 1'd1 ;
  wire \f$bool$f$true$arg1$arg1  = \f$bool$f$true$arg1$arg1$arg0  == \f$bool$f$true$arg1$arg1$arg1  ;
  wire \f$bool$f$true$arg1  = \f$bool$f$true$arg1$arg0  && \f$bool$f$true$arg1$arg1  ;
  wire \f$bool$f$true  = \f$bool$f$true$arg0  || \f$bool$f$true$arg1  ;
  wire \f$bool$f$false$bool  = 1'd1 ;
  wire[1:0] \f$bool$f$false$true$arg0$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$false$true$arg0$arg0$conj  = \f$bool$f$false$true$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$false$true$arg0$arg0  = \f$bool$f$false$true$arg0$arg0$conj [1:1] ;
  wire[0:0] \f$bool$f$false$true$arg0$arg1  = 1'd0 ;
  wire \f$bool$f$false$true$arg0  = \f$bool$f$false$true$arg0$arg0  > \f$bool$f$false$true$arg0$arg1  ;
  wire \f$bool$f$false$true$arg1  = 1'd0 ;
  wire \f$bool$f$false$true  = \f$bool$f$false$true$arg0  || \f$bool$f$false$true$arg1  ;
  wire \f$bool$f$false$false$bool  = 1'd0 ;
  wire[1:0] \f$bool$f$false$false$true$arg0$arg0$arg0$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$false$false$true$arg0$arg0$arg0$arg0$conj  = \f$bool$f$false$false$true$arg0$arg0$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$false$false$true$arg0$arg0$arg0$arg0  = \f$bool$f$false$false$true$arg0$arg0$arg0$arg0$conj [0:0] ;
  wire[0:0] \f$bool$f$false$false$true$arg0$arg0$arg0$arg1  = 1'd0 ;
  wire \f$bool$f$false$false$true$arg0$arg0$arg0  = \f$bool$f$false$false$true$arg0$arg0$arg0$arg0  == \f$bool$f$false$false$true$arg0$arg0$arg0$arg1  ;
  wire \f$bool$f$false$false$true$arg0$arg0  = !\f$bool$f$false$false$true$arg0$arg0$arg0  ;
  wire[1:0] \f$bool$f$false$false$true$arg0$arg1$arg0$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$false$false$true$arg0$arg1$arg0$arg0$conj  = \f$bool$f$false$false$true$arg0$arg1$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$false$false$true$arg0$arg1$arg0$arg0  = \f$bool$f$false$false$true$arg0$arg1$arg0$arg0$conj [0:0] ;
  wire[0:0] \f$bool$f$false$false$true$arg0$arg1$arg0$arg1  = 1'd0 ;
  wire \f$bool$f$false$false$true$arg0$arg1$arg0  = \f$bool$f$false$false$true$arg0$arg1$arg0$arg0  > \f$bool$f$false$false$true$arg0$arg1$arg0$arg1  ;
  wire \f$bool$f$false$false$true$arg0$arg1  = !\f$bool$f$false$false$true$arg0$arg1$arg0  ;
  wire \f$bool$f$false$false$true$arg0  = \f$bool$f$false$false$true$arg0$arg0  && \f$bool$f$false$false$true$arg0$arg1  ;
  wire \f$bool$f$false$false$true$arg1$arg0  = 1'd1 ;
  wire[1:0] \f$bool$f$false$false$true$arg1$arg1$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$false$false$true$arg1$arg1$arg0$conj  = \f$bool$f$false$false$true$arg1$arg1$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$false$false$true$arg1$arg1$arg0  = \f$bool$f$false$false$true$arg1$arg1$arg0$conj [0:0] ;
  wire[0:0] \f$bool$f$false$false$true$arg1$arg1$arg1  = 1'd1 ;
  wire \f$bool$f$false$false$true$arg1$arg1  = \f$bool$f$false$false$true$arg1$arg1$arg0  == \f$bool$f$false$false$true$arg1$arg1$arg1  ;
  wire \f$bool$f$false$false$true$arg1  = \f$bool$f$false$false$true$arg1$arg0  && \f$bool$f$false$false$true$arg1$arg1  ;
  wire \f$bool$f$false$false$true  = \f$bool$f$false$false$true$arg0  || \f$bool$f$false$false$true$arg1  ;
  wire[1:0] \f$bool$f$false$false$false$arg0$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$false$false$false$arg0$arg0$conj  = \f$bool$f$false$false$false$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$false$false$false$arg0$arg0  = \f$bool$f$false$false$false$arg0$arg0$conj [0:0] ;
  wire[0:0] \f$bool$f$false$false$false$arg0$arg1  = 1'd0 ;
  wire \f$bool$f$false$false$false$arg0  = \f$bool$f$false$false$false$arg0$arg0  > \f$bool$f$false$false$false$arg0$arg1  ;
  wire \f$bool$f$false$false$false$arg1  = 1'd0 ;
  wire \f$bool$f$false$false$false  = \f$bool$f$false$false$false$arg0  || \f$bool$f$false$false$false$arg1  ;
  wire \f$bool$f$false$false  = ( \f$bool$f$false$false$bool  ? \f$bool$f$false$false$true  : \f$bool$f$false$false$false  ) ;
  wire \f$bool$f$false  = ( \f$bool$f$false$bool  ? \f$bool$f$false$true  : \f$bool$f$false$false  ) ;
  wire \f$bool$f  = ( \f$bool$f$bool  ? \f$bool$f$true  : \f$bool$f$false  ) ;
  wire \f$bool  = \f$bool$f  ;
  wire[0:0] \f$true$content  = 1'd0 ;
  wire[0:0] \f$true  = \f$true$content  ;
  wire[1:0] \f$false$bool$g0  = \i0$data  ;
  wire \f$false$bool$f$arg0$bool  = 1'd0 ;
  wire[1:0] \f$false$bool$f$arg0$true$arg0$arg0$arg0$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$true$arg0$arg0$arg0$arg0$conj  = \f$false$bool$f$arg0$true$arg0$arg0$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$true$arg0$arg0$arg0$arg0  = \f$false$bool$f$arg0$true$arg0$arg0$arg0$arg0$conj [1:1] ;
  wire[0:0] \f$false$bool$f$arg0$true$arg0$arg0$arg0$arg1  = 1'd0 ;
  wire \f$false$bool$f$arg0$true$arg0$arg0$arg0  = \f$false$bool$f$arg0$true$arg0$arg0$arg0$arg0  == \f$false$bool$f$arg0$true$arg0$arg0$arg0$arg1  ;
  wire \f$false$bool$f$arg0$true$arg0$arg0  = !\f$false$bool$f$arg0$true$arg0$arg0$arg0  ;
  wire[1:0] \f$false$bool$f$arg0$true$arg0$arg1$arg0$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$true$arg0$arg1$arg0$arg0$conj  = \f$false$bool$f$arg0$true$arg0$arg1$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$true$arg0$arg1$arg0$arg0  = \f$false$bool$f$arg0$true$arg0$arg1$arg0$arg0$conj [1:1] ;
  wire[0:0] \f$false$bool$f$arg0$true$arg0$arg1$arg0$arg1  = 1'd0 ;
  wire \f$false$bool$f$arg0$true$arg0$arg1$arg0  = \f$false$bool$f$arg0$true$arg0$arg1$arg0$arg0  > \f$false$bool$f$arg0$true$arg0$arg1$arg0$arg1  ;
  wire \f$false$bool$f$arg0$true$arg0$arg1  = !\f$false$bool$f$arg0$true$arg0$arg1$arg0  ;
  wire \f$false$bool$f$arg0$true$arg0  = \f$false$bool$f$arg0$true$arg0$arg0  && \f$false$bool$f$arg0$true$arg0$arg1  ;
  wire \f$false$bool$f$arg0$true$arg1$arg0  = 1'd1 ;
  wire[1:0] \f$false$bool$f$arg0$true$arg1$arg1$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$true$arg1$arg1$arg0$conj  = \f$false$bool$f$arg0$true$arg1$arg1$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$true$arg1$arg1$arg0  = \f$false$bool$f$arg0$true$arg1$arg1$arg0$conj [1:1] ;
  wire[0:0] \f$false$bool$f$arg0$true$arg1$arg1$arg1  = 1'd1 ;
  wire \f$false$bool$f$arg0$true$arg1$arg1  = \f$false$bool$f$arg0$true$arg1$arg1$arg0  == \f$false$bool$f$arg0$true$arg1$arg1$arg1  ;
  wire \f$false$bool$f$arg0$true$arg1  = \f$false$bool$f$arg0$true$arg1$arg0  && \f$false$bool$f$arg0$true$arg1$arg1  ;
  wire \f$false$bool$f$arg0$true  = \f$false$bool$f$arg0$true$arg0  || \f$false$bool$f$arg0$true$arg1  ;
  wire \f$false$bool$f$arg0$false$bool  = 1'd1 ;
  wire[1:0] \f$false$bool$f$arg0$false$true$arg0$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$false$true$arg0$arg0$conj  = \f$false$bool$f$arg0$false$true$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$false$true$arg0$arg0  = \f$false$bool$f$arg0$false$true$arg0$arg0$conj [1:1] ;
  wire[0:0] \f$false$bool$f$arg0$false$true$arg0$arg1  = 1'd0 ;
  wire \f$false$bool$f$arg0$false$true$arg0  = \f$false$bool$f$arg0$false$true$arg0$arg0  > \f$false$bool$f$arg0$false$true$arg0$arg1  ;
  wire \f$false$bool$f$arg0$false$true$arg1  = 1'd0 ;
  wire \f$false$bool$f$arg0$false$true  = \f$false$bool$f$arg0$false$true$arg0  || \f$false$bool$f$arg0$false$true$arg1  ;
  wire \f$false$bool$f$arg0$false$false$bool  = 1'd0 ;
  wire[1:0] \f$false$bool$f$arg0$false$false$true$arg0$arg0$arg0$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$false$false$true$arg0$arg0$arg0$arg0$conj  = \f$false$bool$f$arg0$false$false$true$arg0$arg0$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$false$false$true$arg0$arg0$arg0$arg0  = \f$false$bool$f$arg0$false$false$true$arg0$arg0$arg0$arg0$conj [0:0] ;
  wire[0:0] \f$false$bool$f$arg0$false$false$true$arg0$arg0$arg0$arg1  = 1'd0 ;
  wire \f$false$bool$f$arg0$false$false$true$arg0$arg0$arg0  = \f$false$bool$f$arg0$false$false$true$arg0$arg0$arg0$arg0  == \f$false$bool$f$arg0$false$false$true$arg0$arg0$arg0$arg1  ;
  wire \f$false$bool$f$arg0$false$false$true$arg0$arg0  = !\f$false$bool$f$arg0$false$false$true$arg0$arg0$arg0  ;
  wire[1:0] \f$false$bool$f$arg0$false$false$true$arg0$arg1$arg0$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$false$false$true$arg0$arg1$arg0$arg0$conj  = \f$false$bool$f$arg0$false$false$true$arg0$arg1$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$false$false$true$arg0$arg1$arg0$arg0  = \f$false$bool$f$arg0$false$false$true$arg0$arg1$arg0$arg0$conj [0:0] ;
  wire[0:0] \f$false$bool$f$arg0$false$false$true$arg0$arg1$arg0$arg1  = 1'd0 ;
  wire \f$false$bool$f$arg0$false$false$true$arg0$arg1$arg0  = \f$false$bool$f$arg0$false$false$true$arg0$arg1$arg0$arg0  > \f$false$bool$f$arg0$false$false$true$arg0$arg1$arg0$arg1  ;
  wire \f$false$bool$f$arg0$false$false$true$arg0$arg1  = !\f$false$bool$f$arg0$false$false$true$arg0$arg1$arg0  ;
  wire \f$false$bool$f$arg0$false$false$true$arg0  = \f$false$bool$f$arg0$false$false$true$arg0$arg0  && \f$false$bool$f$arg0$false$false$true$arg0$arg1  ;
  wire \f$false$bool$f$arg0$false$false$true$arg1$arg0  = 1'd1 ;
  wire[1:0] \f$false$bool$f$arg0$false$false$true$arg1$arg1$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$false$false$true$arg1$arg1$arg0$conj  = \f$false$bool$f$arg0$false$false$true$arg1$arg1$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$false$false$true$arg1$arg1$arg0  = \f$false$bool$f$arg0$false$false$true$arg1$arg1$arg0$conj [0:0] ;
  wire[0:0] \f$false$bool$f$arg0$false$false$true$arg1$arg1$arg1  = 1'd1 ;
  wire \f$false$bool$f$arg0$false$false$true$arg1$arg1  = \f$false$bool$f$arg0$false$false$true$arg1$arg1$arg0  == \f$false$bool$f$arg0$false$false$true$arg1$arg1$arg1  ;
  wire \f$false$bool$f$arg0$false$false$true$arg1  = \f$false$bool$f$arg0$false$false$true$arg1$arg0  && \f$false$bool$f$arg0$false$false$true$arg1$arg1  ;
  wire \f$false$bool$f$arg0$false$false$true  = \f$false$bool$f$arg0$false$false$true$arg0  || \f$false$bool$f$arg0$false$false$true$arg1  ;
  wire[1:0] \f$false$bool$f$arg0$false$false$false$arg0$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$false$false$false$arg0$arg0$conj  = \f$false$bool$f$arg0$false$false$false$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$false$false$false$arg0$arg0  = \f$false$bool$f$arg0$false$false$false$arg0$arg0$conj [0:0] ;
  wire[0:0] \f$false$bool$f$arg0$false$false$false$arg0$arg1  = 1'd0 ;
  wire \f$false$bool$f$arg0$false$false$false$arg0  = \f$false$bool$f$arg0$false$false$false$arg0$arg0  > \f$false$bool$f$arg0$false$false$false$arg0$arg1  ;
  wire \f$false$bool$f$arg0$false$false$false$arg1  = 1'd0 ;
  wire \f$false$bool$f$arg0$false$false$false  = \f$false$bool$f$arg0$false$false$false$arg0  || \f$false$bool$f$arg0$false$false$false$arg1  ;
  wire \f$false$bool$f$arg0$false$false  = ( \f$false$bool$f$arg0$false$false$bool  ? \f$false$bool$f$arg0$false$false$true  : \f$false$bool$f$arg0$false$false$false  ) ;
  wire \f$false$bool$f$arg0$false  = ( \f$false$bool$f$arg0$false$bool  ? \f$false$bool$f$arg0$false$true  : \f$false$bool$f$arg0$false$false  ) ;
  wire \f$false$bool$f$arg0  = ( \f$false$bool$f$arg0$bool  ? \f$false$bool$f$arg0$true  : \f$false$bool$f$arg0$false  ) ;
  wire \f$false$bool$f  = !\f$false$bool$f$arg0  ;
  wire \f$false$bool  = \f$false$bool$f  ;
  wire[0:0] \f$false$true$content  = 1'd1 ;
  wire[0:0] \f$false$true  = \f$false$true$content  ;
  wire[0:0] \f$false$false$content  = 1'd0 ;
  wire[0:0] \f$false$false  = \f$false$false$content  ;
  wire[0:0] \f$false  = ( \f$false$bool  ? \f$false$true  : \f$false$false  ) ;
  wire[0:0] \f  = ( \f$bool  ? \f$true  : \f$false  ) ;
  
  assign \o0  = \f  ;
endmodule

module \OFUN_1$RECEPTION_0_0_1_2_Switch2 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , output [1:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[1:0] \f  = \i0$data  ;
  
  assign \o0  = \f  ;
endmodule

module \OFUN_2$RECEPTION_0_0_1_2_Switch2 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , output [1:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[1:0] \f  = \i0$data  ;
  
  assign \o0  = \f  ;
endmodule

module \RECEPTION_0_0_0_2 (
      input \clk , input \rst , input [63:0] \t 
    , input \input$irdy , input [1:0] \input$data , output \input$trdy 
    , output \bus_outs1$irdy , output [1:0] \bus_outs1$data , input \bus_outs1$trdy 
    , output \bus_outs2$irdy , output [1:0] \bus_outs2$data , input \bus_outs2$trdy 
    , output \bus_outs3$irdy , output [1:0] \bus_outs3$data , input \bus_outs3$trdy 
    , output \bus_outs4$irdy , output [0:0] \bus_outs4$data , input \bus_outs4$trdy 
    , input \CreditCounter1$PatientSource1$unbound_irdy 
    , input [0:0] \CreditCounter1$PatientSource1$unbound_data 
    , output \CreditCounter1$PatientSource1$trdy 
    , input \CreditCounter1$Sink1$unbound_trdy 
    , output \CreditCounter1$Sink1$irdy 
    , output [0:0] \CreditCounter1$Sink1$data 
  );
  
  //
  // Channel declarations
  //
  wire \noCONS$irdy  ;
  wire [1:0] \noCONS$data  ;
  wire \noCONS$trdy  ;
  wire \toRCP$irdy  ;
  wire [1:0] \toRCP$data  ;
  wire \toRCP$trdy  ;
  wire \creditBack$irdy  ;
  wire [1:0] \creditBack$data  ;
  wire \creditBack$trdy  ;
  wire \channel1$irdy  ;
  wire [1:0] \channel1$data  ;
  wire \channel1$trdy  ;
  
  //
  // Function Channels
  //
  wire \sfunchan_0_Switch1$data  ;
  wire [1:0] \ofunchan_1_Switch1$data  ;
  wire [1:0] \ofunchan_2_Switch1$data  ;
  wire \sfunchan_0_Switch2$data  ;
  wire [1:0] \ofunchan_1_Switch2$data  ;
  wire [1:0] \ofunchan_2_Switch2$data  ;
  
  //
  // Component and Macro instantiations
  //
  \Fork2  #(
    .DATASIZE(2)
  ) \Fork1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\channel1$irdy )
    , .\i0$data (\channel1$data )
    , .\i0$trdy (\channel1$trdy )
    , .\o0$irdy (\toRCP$irdy )
    , .\o0$data (\toRCP$data )
    , .\o0$trdy (\toRCP$trdy )
    , .\o1$irdy (\creditBack$irdy )
    , .\o1$data (\creditBack$data )
    , .\o1$trdy (\creditBack$trdy )
  );
  
  \Queue  #(
    .NUM_DATA(0),
    .DATASIZE(2),
    .LENGTH(2)
  ) \Queue1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\input$irdy )
    , .\i0$data (\input$data )
    , .\i0$trdy (\input$trdy )
    , .\o0$irdy (\channel1$irdy )
    , .\o0$data (\channel1$data )
    , .\o0$trdy (\channel1$trdy )
  );
  
  \Switch2  #(
    .OUTPUTSIZE0(2),
    .OUTPUTSIZE1(2),
    .INPUTSIZE(2)
  ) \Switch1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\toRCP$irdy )
    , .\i0$data (\toRCP$data )
    , .\i0$trdy (\toRCP$trdy )
    , .\o0$irdy (\bus_outs1$irdy )
    , .\o0$data (\bus_outs1$data )
    , .\o0$trdy (\bus_outs1$trdy )
    , .\o1$irdy (\noCONS$irdy )
    , .\o1$data (\noCONS$data )
    , .\o1$trdy (\noCONS$trdy )
    , .\sel$data (\sfunchan_0_Switch1$data )
    , .\f0$data (\ofunchan_1_Switch1$data )
    , .\f1$data (\ofunchan_2_Switch1$data )
  );
  
  \SFUN_0$RECEPTION_0_0_0_2_Switch1  \sfun_0_Switch1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\toRCP$data )
    , .\o0 (\sfunchan_0_Switch1$data )
  );
  
  \OFUN_1$RECEPTION_0_0_0_2_Switch1  \ofun_1_Switch1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\toRCP$data )
    , .\o0 (\ofunchan_1_Switch1$data )
  );
  
  \OFUN_2$RECEPTION_0_0_0_2_Switch1  \ofun_2_Switch1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\toRCP$data )
    , .\o0 (\ofunchan_2_Switch1$data )
  );
  
  \Switch2  #(
    .OUTPUTSIZE0(2),
    .OUTPUTSIZE1(2),
    .INPUTSIZE(2)
  ) \Switch2  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\noCONS$irdy )
    , .\i0$data (\noCONS$data )
    , .\i0$trdy (\noCONS$trdy )
    , .\o0$irdy (\bus_outs2$irdy )
    , .\o0$data (\bus_outs2$data )
    , .\o0$trdy (\bus_outs2$trdy )
    , .\o1$irdy (\bus_outs3$irdy )
    , .\o1$data (\bus_outs3$data )
    , .\o1$trdy (\bus_outs3$trdy )
    , .\sel$data (\sfunchan_0_Switch2$data )
    , .\f0$data (\ofunchan_1_Switch2$data )
    , .\f1$data (\ofunchan_2_Switch2$data )
  );
  
  \SFUN_0$RECEPTION_0_0_0_2_Switch2  \sfun_0_Switch2  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\noCONS$data )
    , .\o0 (\sfunchan_0_Switch2$data )
  );
  
  \OFUN_1$RECEPTION_0_0_0_2_Switch2  \ofun_1_Switch2  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\noCONS$data )
    , .\o0 (\ofunchan_1_Switch2$data )
  );
  
  \OFUN_2$RECEPTION_0_0_0_2_Switch2  \ofun_2_Switch2  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\noCONS$data )
    , .\o0 (\ofunchan_2_Switch2$data )
  );
  
  \CreditCounter_2  \CreditCounter1  (
      .\clk (\clk ), .\rst (\rst ), .\t (\t )
    , .\i$irdy (\creditBack$irdy )
    , .\i$data (\creditBack$data )
    , .\i$trdy (\creditBack$trdy )
    , .\o$irdy (\bus_outs4$irdy )
    , .\o$data (\bus_outs4$data )
    , .\o$trdy (\bus_outs4$trdy )
    , .\PatientSource1$unbound_irdy (\CreditCounter1$PatientSource1$unbound_irdy )
    , .\PatientSource1$unbound_data (\CreditCounter1$PatientSource1$unbound_data )
    , .\PatientSource1$trdy (\CreditCounter1$PatientSource1$trdy )
    , .\Sink1$unbound_trdy (\CreditCounter1$Sink1$unbound_trdy )
    , .\Sink1$irdy (\CreditCounter1$Sink1$irdy )
    , .\Sink1$data (\CreditCounter1$Sink1$data )
  );
  
endmodule


//
// RECEPTION_0_0_0_2 switch functions
//
module \SFUN_0$RECEPTION_0_0_0_2_Switch1 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , output [0:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[1:0] \f$bool$g0  = \i0$data  ;
  wire[1:0] \f$bool$f$arg0$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$arg0$arg0$conj  = \f$bool$f$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$arg0$arg0  = \f$bool$f$arg0$arg0$conj [1:1] ;
  wire[0:0] \f$bool$f$arg0$arg1  = 1'd0 ;
  wire \f$bool$f$arg0  = \f$bool$f$arg0$arg0  == \f$bool$f$arg0$arg1  ;
  wire[1:0] \f$bool$f$arg1$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$arg1$arg0$conj  = \f$bool$f$arg1$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$arg1$arg0  = \f$bool$f$arg1$arg0$conj [0:0] ;
  wire[0:0] \f$bool$f$arg1$arg1  = 1'd0 ;
  wire \f$bool$f$arg1  = \f$bool$f$arg1$arg0  == \f$bool$f$arg1$arg1  ;
  wire \f$bool$f  = \f$bool$f$arg0  && \f$bool$f$arg1  ;
  wire \f$bool  = \f$bool$f  ;
  wire[0:0] \f$true$content  = 1'd0 ;
  wire[0:0] \f$true  = \f$true$content  ;
  wire[1:0] \f$false$bool$g0  = \i0$data  ;
  wire[1:0] \f$false$bool$f$arg0$arg0$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$arg0$arg0$conj  = \f$false$bool$f$arg0$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$arg0$arg0  = \f$false$bool$f$arg0$arg0$arg0$conj [1:1] ;
  wire[0:0] \f$false$bool$f$arg0$arg0$arg1  = 1'd0 ;
  wire \f$false$bool$f$arg0$arg0  = \f$false$bool$f$arg0$arg0$arg0  == \f$false$bool$f$arg0$arg0$arg1  ;
  wire[1:0] \f$false$bool$f$arg0$arg1$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$arg1$arg0$conj  = \f$false$bool$f$arg0$arg1$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$arg1$arg0  = \f$false$bool$f$arg0$arg1$arg0$conj [0:0] ;
  wire[0:0] \f$false$bool$f$arg0$arg1$arg1  = 1'd0 ;
  wire \f$false$bool$f$arg0$arg1  = \f$false$bool$f$arg0$arg1$arg0  == \f$false$bool$f$arg0$arg1$arg1  ;
  wire \f$false$bool$f$arg0  = \f$false$bool$f$arg0$arg0  && \f$false$bool$f$arg0$arg1  ;
  wire \f$false$bool$f  = !\f$false$bool$f$arg0  ;
  wire \f$false$bool  = \f$false$bool$f  ;
  wire[0:0] \f$false$true$content  = 1'd1 ;
  wire[0:0] \f$false$true  = \f$false$true$content  ;
  wire[0:0] \f$false$false$content  = 1'd0 ;
  wire[0:0] \f$false$false  = \f$false$false$content  ;
  wire[0:0] \f$false  = ( \f$false$bool  ? \f$false$true  : \f$false$false  ) ;
  wire[0:0] \f  = ( \f$bool  ? \f$true  : \f$false  ) ;
  
  assign \o0  = \f  ;
endmodule

module \OFUN_1$RECEPTION_0_0_0_2_Switch1 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , output [1:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[1:0] \f  = \i0$data  ;
  
  assign \o0  = \f  ;
endmodule

module \OFUN_2$RECEPTION_0_0_0_2_Switch1 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , output [1:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[1:0] \f  = \i0$data  ;
  
  assign \o0  = \f  ;
endmodule

module \SFUN_0$RECEPTION_0_0_0_2_Switch2 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , output [0:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[1:0] \f$bool$g0  = \i0$data  ;
  wire \f$bool$f$bool  = 1'd1 ;
  wire[1:0] \f$bool$f$true$arg0$arg0$arg0$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$true$arg0$arg0$arg0$arg0$conj  = \f$bool$f$true$arg0$arg0$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$true$arg0$arg0$arg0$arg0  = \f$bool$f$true$arg0$arg0$arg0$arg0$conj [1:1] ;
  wire[0:0] \f$bool$f$true$arg0$arg0$arg0$arg1  = 1'd0 ;
  wire \f$bool$f$true$arg0$arg0$arg0  = \f$bool$f$true$arg0$arg0$arg0$arg0  == \f$bool$f$true$arg0$arg0$arg0$arg1  ;
  wire \f$bool$f$true$arg0$arg0  = !\f$bool$f$true$arg0$arg0$arg0  ;
  wire[1:0] \f$bool$f$true$arg0$arg1$arg0$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$true$arg0$arg1$arg0$arg0$conj  = \f$bool$f$true$arg0$arg1$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$true$arg0$arg1$arg0$arg0  = \f$bool$f$true$arg0$arg1$arg0$arg0$conj [1:1] ;
  wire[0:0] \f$bool$f$true$arg0$arg1$arg0$arg1  = 1'd0 ;
  wire \f$bool$f$true$arg0$arg1$arg0  = \f$bool$f$true$arg0$arg1$arg0$arg0  > \f$bool$f$true$arg0$arg1$arg0$arg1  ;
  wire \f$bool$f$true$arg0$arg1  = !\f$bool$f$true$arg0$arg1$arg0  ;
  wire \f$bool$f$true$arg0  = \f$bool$f$true$arg0$arg0  && \f$bool$f$true$arg0$arg1  ;
  wire \f$bool$f$true$arg1$arg0  = 1'd1 ;
  wire[1:0] \f$bool$f$true$arg1$arg1$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$true$arg1$arg1$arg0$conj  = \f$bool$f$true$arg1$arg1$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$true$arg1$arg1$arg0  = \f$bool$f$true$arg1$arg1$arg0$conj [1:1] ;
  wire[0:0] \f$bool$f$true$arg1$arg1$arg1  = 1'd1 ;
  wire \f$bool$f$true$arg1$arg1  = \f$bool$f$true$arg1$arg1$arg0  == \f$bool$f$true$arg1$arg1$arg1  ;
  wire \f$bool$f$true$arg1  = \f$bool$f$true$arg1$arg0  && \f$bool$f$true$arg1$arg1  ;
  wire \f$bool$f$true  = \f$bool$f$true$arg0  || \f$bool$f$true$arg1  ;
  wire \f$bool$f$false$bool  = 1'd0 ;
  wire[1:0] \f$bool$f$false$true$arg0$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$false$true$arg0$arg0$conj  = \f$bool$f$false$true$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$false$true$arg0$arg0  = \f$bool$f$false$true$arg0$arg0$conj [1:1] ;
  wire[0:0] \f$bool$f$false$true$arg0$arg1  = 1'd0 ;
  wire \f$bool$f$false$true$arg0  = \f$bool$f$false$true$arg0$arg0  > \f$bool$f$false$true$arg0$arg1  ;
  wire \f$bool$f$false$true$arg1  = 1'd0 ;
  wire \f$bool$f$false$true  = \f$bool$f$false$true$arg0  || \f$bool$f$false$true$arg1  ;
  wire \f$bool$f$false$false$bool  = 1'd0 ;
  wire[1:0] \f$bool$f$false$false$true$arg0$arg0$arg0$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$false$false$true$arg0$arg0$arg0$arg0$conj  = \f$bool$f$false$false$true$arg0$arg0$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$false$false$true$arg0$arg0$arg0$arg0  = \f$bool$f$false$false$true$arg0$arg0$arg0$arg0$conj [0:0] ;
  wire[0:0] \f$bool$f$false$false$true$arg0$arg0$arg0$arg1  = 1'd0 ;
  wire \f$bool$f$false$false$true$arg0$arg0$arg0  = \f$bool$f$false$false$true$arg0$arg0$arg0$arg0  == \f$bool$f$false$false$true$arg0$arg0$arg0$arg1  ;
  wire \f$bool$f$false$false$true$arg0$arg0  = !\f$bool$f$false$false$true$arg0$arg0$arg0  ;
  wire[1:0] \f$bool$f$false$false$true$arg0$arg1$arg0$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$false$false$true$arg0$arg1$arg0$arg0$conj  = \f$bool$f$false$false$true$arg0$arg1$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$false$false$true$arg0$arg1$arg0$arg0  = \f$bool$f$false$false$true$arg0$arg1$arg0$arg0$conj [0:0] ;
  wire[0:0] \f$bool$f$false$false$true$arg0$arg1$arg0$arg1  = 1'd0 ;
  wire \f$bool$f$false$false$true$arg0$arg1$arg0  = \f$bool$f$false$false$true$arg0$arg1$arg0$arg0  > \f$bool$f$false$false$true$arg0$arg1$arg0$arg1  ;
  wire \f$bool$f$false$false$true$arg0$arg1  = !\f$bool$f$false$false$true$arg0$arg1$arg0  ;
  wire \f$bool$f$false$false$true$arg0  = \f$bool$f$false$false$true$arg0$arg0  && \f$bool$f$false$false$true$arg0$arg1  ;
  wire \f$bool$f$false$false$true$arg1$arg0  = 1'd1 ;
  wire[1:0] \f$bool$f$false$false$true$arg1$arg1$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$false$false$true$arg1$arg1$arg0$conj  = \f$bool$f$false$false$true$arg1$arg1$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$false$false$true$arg1$arg1$arg0  = \f$bool$f$false$false$true$arg1$arg1$arg0$conj [0:0] ;
  wire[0:0] \f$bool$f$false$false$true$arg1$arg1$arg1  = 1'd1 ;
  wire \f$bool$f$false$false$true$arg1$arg1  = \f$bool$f$false$false$true$arg1$arg1$arg0  == \f$bool$f$false$false$true$arg1$arg1$arg1  ;
  wire \f$bool$f$false$false$true$arg1  = \f$bool$f$false$false$true$arg1$arg0  && \f$bool$f$false$false$true$arg1$arg1  ;
  wire \f$bool$f$false$false$true  = \f$bool$f$false$false$true$arg0  || \f$bool$f$false$false$true$arg1  ;
  wire[1:0] \f$bool$f$false$false$false$arg0$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$false$false$false$arg0$arg0$conj  = \f$bool$f$false$false$false$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$false$false$false$arg0$arg0  = \f$bool$f$false$false$false$arg0$arg0$conj [0:0] ;
  wire[0:0] \f$bool$f$false$false$false$arg0$arg1  = 1'd0 ;
  wire \f$bool$f$false$false$false$arg0  = \f$bool$f$false$false$false$arg0$arg0  > \f$bool$f$false$false$false$arg0$arg1  ;
  wire \f$bool$f$false$false$false$arg1  = 1'd0 ;
  wire \f$bool$f$false$false$false  = \f$bool$f$false$false$false$arg0  || \f$bool$f$false$false$false$arg1  ;
  wire \f$bool$f$false$false  = ( \f$bool$f$false$false$bool  ? \f$bool$f$false$false$true  : \f$bool$f$false$false$false  ) ;
  wire \f$bool$f$false  = ( \f$bool$f$false$bool  ? \f$bool$f$false$true  : \f$bool$f$false$false  ) ;
  wire \f$bool$f  = ( \f$bool$f$bool  ? \f$bool$f$true  : \f$bool$f$false  ) ;
  wire \f$bool  = \f$bool$f  ;
  wire[0:0] \f$true$content  = 1'd0 ;
  wire[0:0] \f$true  = \f$true$content  ;
  wire[1:0] \f$false$bool$g0  = \i0$data  ;
  wire \f$false$bool$f$arg0$bool  = 1'd1 ;
  wire[1:0] \f$false$bool$f$arg0$true$arg0$arg0$arg0$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$true$arg0$arg0$arg0$arg0$conj  = \f$false$bool$f$arg0$true$arg0$arg0$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$true$arg0$arg0$arg0$arg0  = \f$false$bool$f$arg0$true$arg0$arg0$arg0$arg0$conj [1:1] ;
  wire[0:0] \f$false$bool$f$arg0$true$arg0$arg0$arg0$arg1  = 1'd0 ;
  wire \f$false$bool$f$arg0$true$arg0$arg0$arg0  = \f$false$bool$f$arg0$true$arg0$arg0$arg0$arg0  == \f$false$bool$f$arg0$true$arg0$arg0$arg0$arg1  ;
  wire \f$false$bool$f$arg0$true$arg0$arg0  = !\f$false$bool$f$arg0$true$arg0$arg0$arg0  ;
  wire[1:0] \f$false$bool$f$arg0$true$arg0$arg1$arg0$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$true$arg0$arg1$arg0$arg0$conj  = \f$false$bool$f$arg0$true$arg0$arg1$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$true$arg0$arg1$arg0$arg0  = \f$false$bool$f$arg0$true$arg0$arg1$arg0$arg0$conj [1:1] ;
  wire[0:0] \f$false$bool$f$arg0$true$arg0$arg1$arg0$arg1  = 1'd0 ;
  wire \f$false$bool$f$arg0$true$arg0$arg1$arg0  = \f$false$bool$f$arg0$true$arg0$arg1$arg0$arg0  > \f$false$bool$f$arg0$true$arg0$arg1$arg0$arg1  ;
  wire \f$false$bool$f$arg0$true$arg0$arg1  = !\f$false$bool$f$arg0$true$arg0$arg1$arg0  ;
  wire \f$false$bool$f$arg0$true$arg0  = \f$false$bool$f$arg0$true$arg0$arg0  && \f$false$bool$f$arg0$true$arg0$arg1  ;
  wire \f$false$bool$f$arg0$true$arg1$arg0  = 1'd1 ;
  wire[1:0] \f$false$bool$f$arg0$true$arg1$arg1$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$true$arg1$arg1$arg0$conj  = \f$false$bool$f$arg0$true$arg1$arg1$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$true$arg1$arg1$arg0  = \f$false$bool$f$arg0$true$arg1$arg1$arg0$conj [1:1] ;
  wire[0:0] \f$false$bool$f$arg0$true$arg1$arg1$arg1  = 1'd1 ;
  wire \f$false$bool$f$arg0$true$arg1$arg1  = \f$false$bool$f$arg0$true$arg1$arg1$arg0  == \f$false$bool$f$arg0$true$arg1$arg1$arg1  ;
  wire \f$false$bool$f$arg0$true$arg1  = \f$false$bool$f$arg0$true$arg1$arg0  && \f$false$bool$f$arg0$true$arg1$arg1  ;
  wire \f$false$bool$f$arg0$true  = \f$false$bool$f$arg0$true$arg0  || \f$false$bool$f$arg0$true$arg1  ;
  wire \f$false$bool$f$arg0$false$bool  = 1'd0 ;
  wire[1:0] \f$false$bool$f$arg0$false$true$arg0$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$false$true$arg0$arg0$conj  = \f$false$bool$f$arg0$false$true$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$false$true$arg0$arg0  = \f$false$bool$f$arg0$false$true$arg0$arg0$conj [1:1] ;
  wire[0:0] \f$false$bool$f$arg0$false$true$arg0$arg1  = 1'd0 ;
  wire \f$false$bool$f$arg0$false$true$arg0  = \f$false$bool$f$arg0$false$true$arg0$arg0  > \f$false$bool$f$arg0$false$true$arg0$arg1  ;
  wire \f$false$bool$f$arg0$false$true$arg1  = 1'd0 ;
  wire \f$false$bool$f$arg0$false$true  = \f$false$bool$f$arg0$false$true$arg0  || \f$false$bool$f$arg0$false$true$arg1  ;
  wire \f$false$bool$f$arg0$false$false$bool  = 1'd0 ;
  wire[1:0] \f$false$bool$f$arg0$false$false$true$arg0$arg0$arg0$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$false$false$true$arg0$arg0$arg0$arg0$conj  = \f$false$bool$f$arg0$false$false$true$arg0$arg0$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$false$false$true$arg0$arg0$arg0$arg0  = \f$false$bool$f$arg0$false$false$true$arg0$arg0$arg0$arg0$conj [0:0] ;
  wire[0:0] \f$false$bool$f$arg0$false$false$true$arg0$arg0$arg0$arg1  = 1'd0 ;
  wire \f$false$bool$f$arg0$false$false$true$arg0$arg0$arg0  = \f$false$bool$f$arg0$false$false$true$arg0$arg0$arg0$arg0  == \f$false$bool$f$arg0$false$false$true$arg0$arg0$arg0$arg1  ;
  wire \f$false$bool$f$arg0$false$false$true$arg0$arg0  = !\f$false$bool$f$arg0$false$false$true$arg0$arg0$arg0  ;
  wire[1:0] \f$false$bool$f$arg0$false$false$true$arg0$arg1$arg0$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$false$false$true$arg0$arg1$arg0$arg0$conj  = \f$false$bool$f$arg0$false$false$true$arg0$arg1$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$false$false$true$arg0$arg1$arg0$arg0  = \f$false$bool$f$arg0$false$false$true$arg0$arg1$arg0$arg0$conj [0:0] ;
  wire[0:0] \f$false$bool$f$arg0$false$false$true$arg0$arg1$arg0$arg1  = 1'd0 ;
  wire \f$false$bool$f$arg0$false$false$true$arg0$arg1$arg0  = \f$false$bool$f$arg0$false$false$true$arg0$arg1$arg0$arg0  > \f$false$bool$f$arg0$false$false$true$arg0$arg1$arg0$arg1  ;
  wire \f$false$bool$f$arg0$false$false$true$arg0$arg1  = !\f$false$bool$f$arg0$false$false$true$arg0$arg1$arg0  ;
  wire \f$false$bool$f$arg0$false$false$true$arg0  = \f$false$bool$f$arg0$false$false$true$arg0$arg0  && \f$false$bool$f$arg0$false$false$true$arg0$arg1  ;
  wire \f$false$bool$f$arg0$false$false$true$arg1$arg0  = 1'd1 ;
  wire[1:0] \f$false$bool$f$arg0$false$false$true$arg1$arg1$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$false$false$true$arg1$arg1$arg0$conj  = \f$false$bool$f$arg0$false$false$true$arg1$arg1$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$false$false$true$arg1$arg1$arg0  = \f$false$bool$f$arg0$false$false$true$arg1$arg1$arg0$conj [0:0] ;
  wire[0:0] \f$false$bool$f$arg0$false$false$true$arg1$arg1$arg1  = 1'd1 ;
  wire \f$false$bool$f$arg0$false$false$true$arg1$arg1  = \f$false$bool$f$arg0$false$false$true$arg1$arg1$arg0  == \f$false$bool$f$arg0$false$false$true$arg1$arg1$arg1  ;
  wire \f$false$bool$f$arg0$false$false$true$arg1  = \f$false$bool$f$arg0$false$false$true$arg1$arg0  && \f$false$bool$f$arg0$false$false$true$arg1$arg1  ;
  wire \f$false$bool$f$arg0$false$false$true  = \f$false$bool$f$arg0$false$false$true$arg0  || \f$false$bool$f$arg0$false$false$true$arg1  ;
  wire[1:0] \f$false$bool$f$arg0$false$false$false$arg0$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$false$false$false$arg0$arg0$conj  = \f$false$bool$f$arg0$false$false$false$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$false$false$false$arg0$arg0  = \f$false$bool$f$arg0$false$false$false$arg0$arg0$conj [0:0] ;
  wire[0:0] \f$false$bool$f$arg0$false$false$false$arg0$arg1  = 1'd0 ;
  wire \f$false$bool$f$arg0$false$false$false$arg0  = \f$false$bool$f$arg0$false$false$false$arg0$arg0  > \f$false$bool$f$arg0$false$false$false$arg0$arg1  ;
  wire \f$false$bool$f$arg0$false$false$false$arg1  = 1'd0 ;
  wire \f$false$bool$f$arg0$false$false$false  = \f$false$bool$f$arg0$false$false$false$arg0  || \f$false$bool$f$arg0$false$false$false$arg1  ;
  wire \f$false$bool$f$arg0$false$false  = ( \f$false$bool$f$arg0$false$false$bool  ? \f$false$bool$f$arg0$false$false$true  : \f$false$bool$f$arg0$false$false$false  ) ;
  wire \f$false$bool$f$arg0$false  = ( \f$false$bool$f$arg0$false$bool  ? \f$false$bool$f$arg0$false$true  : \f$false$bool$f$arg0$false$false  ) ;
  wire \f$false$bool$f$arg0  = ( \f$false$bool$f$arg0$bool  ? \f$false$bool$f$arg0$true  : \f$false$bool$f$arg0$false  ) ;
  wire \f$false$bool$f  = !\f$false$bool$f$arg0  ;
  wire \f$false$bool  = \f$false$bool$f  ;
  wire[0:0] \f$false$true$content  = 1'd1 ;
  wire[0:0] \f$false$true  = \f$false$true$content  ;
  wire[0:0] \f$false$false$content  = 1'd0 ;
  wire[0:0] \f$false$false  = \f$false$false$content  ;
  wire[0:0] \f$false  = ( \f$false$bool  ? \f$false$true  : \f$false$false  ) ;
  wire[0:0] \f  = ( \f$bool  ? \f$true  : \f$false  ) ;
  
  assign \o0  = \f  ;
endmodule

module \OFUN_1$RECEPTION_0_0_0_2_Switch2 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , output [1:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[1:0] \f  = \i0$data  ;
  
  assign \o0  = \f  ;
endmodule

module \OFUN_2$RECEPTION_0_0_0_2_Switch2 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , output [1:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[1:0] \f  = \i0$data  ;
  
  assign \o0  = \f  ;
endmodule

module \EJECTION_2$type0 (
      input \clk , input \rst 
    , input \bus_ins1$irdy , input [1:0] \bus_ins1$data , output \bus_ins1$trdy 
    , input \bus_ins2$irdy , input [1:0] \bus_ins2$data , output \bus_ins2$trdy 
    , input \bus_ins3$irdy , input [1:0] \bus_ins3$data , output \bus_ins3$trdy 
    , output \output$irdy , output [1:0] \output$data , input \output$trdy 
  );
  
  //
  // Channel declarations
  //
  wire \channel1$irdy  ;
  wire [1:0] \channel1$data  ;
  wire \channel1$trdy  ;
  wire \channel2$irdy  ;
  wire [1:0] \channel2$data  ;
  wire \channel2$trdy  ;
  wire \channel3$irdy  ;
  wire [1:0] \channel3$data  ;
  wire \channel3$trdy  ;
  
  //
  // Component and Macro instantiations
  //
  \Queue  #(
    .NUM_DATA(0),
    .DATASIZE(2),
    .LENGTH(2)
  ) \Queue1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\bus_ins3$irdy )
    , .\i0$data (\bus_ins3$data )
    , .\i0$trdy (\bus_ins3$trdy )
    , .\o0$irdy (\channel3$irdy )
    , .\o0$data (\channel3$data )
    , .\o0$trdy (\channel3$trdy )
  );
  
  \Merge3$type0  \Merge31  (
      .\clk (\clk ), .\rst (\rst )
    , .\bus_ins1$irdy (\channel1$irdy )
    , .\bus_ins1$data (\channel1$data )
    , .\bus_ins1$trdy (\channel1$trdy )
    , .\bus_ins2$irdy (\channel2$irdy )
    , .\bus_ins2$data (\channel2$data )
    , .\bus_ins2$trdy (\channel2$trdy )
    , .\bus_ins3$irdy (\channel3$irdy )
    , .\bus_ins3$data (\channel3$data )
    , .\bus_ins3$trdy (\channel3$trdy )
    , .\output$irdy (\output$irdy )
    , .\output$data (\output$data )
    , .\output$trdy (\output$trdy )
  );
  
  \Latch$type0  \Latch1  (
      .\clk (\clk ), .\rst (\rst )
    , .\input$irdy (\bus_ins1$irdy )
    , .\input$data (\bus_ins1$data )
    , .\input$trdy (\bus_ins1$trdy )
    , .\output$irdy (\channel1$irdy )
    , .\output$data (\channel1$data )
    , .\output$trdy (\channel1$trdy )
  );
  
  \Latch$type1  \Latch2  (
      .\clk (\clk ), .\rst (\rst )
    , .\input$irdy (\bus_ins2$irdy )
    , .\input$data (\bus_ins2$data )
    , .\input$trdy (\bus_ins2$trdy )
    , .\output$irdy (\channel2$irdy )
    , .\output$data (\channel2$data )
    , .\output$trdy (\channel2$trdy )
  );
  
endmodule

module \EJECTION_2$type1 (
      input \clk , input \rst 
    , input \bus_ins1$irdy , input [1:0] \bus_ins1$data , output \bus_ins1$trdy 
    , input \bus_ins2$irdy , input [1:0] \bus_ins2$data , output \bus_ins2$trdy 
    , input \bus_ins3$irdy , input [1:0] \bus_ins3$data , output \bus_ins3$trdy 
    , output \output$irdy , output [1:0] \output$data , input \output$trdy 
  );
  
  //
  // Channel declarations
  //
  wire \channel1$irdy  ;
  wire [1:0] \channel1$data  ;
  wire \channel1$trdy  ;
  wire \channel2$irdy  ;
  wire [1:0] \channel2$data  ;
  wire \channel2$trdy  ;
  wire \channel3$irdy  ;
  wire [1:0] \channel3$data  ;
  wire \channel3$trdy  ;
  
  //
  // Component and Macro instantiations
  //
  \Queue  #(
    .NUM_DATA(0),
    .DATASIZE(2),
    .LENGTH(2)
  ) \Queue1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\bus_ins3$irdy )
    , .\i0$data (\bus_ins3$data )
    , .\i0$trdy (\bus_ins3$trdy )
    , .\o0$irdy (\channel3$irdy )
    , .\o0$data (\channel3$data )
    , .\o0$trdy (\channel3$trdy )
  );
  
  \Merge3$type1  \Merge31  (
      .\clk (\clk ), .\rst (\rst )
    , .\bus_ins1$irdy (\channel1$irdy )
    , .\bus_ins1$data (\channel1$data )
    , .\bus_ins1$trdy (\channel1$trdy )
    , .\bus_ins2$irdy (\channel2$irdy )
    , .\bus_ins2$data (\channel2$data )
    , .\bus_ins2$trdy (\channel2$trdy )
    , .\bus_ins3$irdy (\channel3$irdy )
    , .\bus_ins3$data (\channel3$data )
    , .\bus_ins3$trdy (\channel3$trdy )
    , .\output$irdy (\output$irdy )
    , .\output$data (\output$data )
    , .\output$trdy (\output$trdy )
  );
  
  \Latch$type0  \Latch1  (
      .\clk (\clk ), .\rst (\rst )
    , .\input$irdy (\bus_ins1$irdy )
    , .\input$data (\bus_ins1$data )
    , .\input$trdy (\bus_ins1$trdy )
    , .\output$irdy (\channel1$irdy )
    , .\output$data (\channel1$data )
    , .\output$trdy (\channel1$trdy )
  );
  
  \Latch$type3  \Latch2  (
      .\clk (\clk ), .\rst (\rst )
    , .\input$irdy (\bus_ins2$irdy )
    , .\input$data (\bus_ins2$data )
    , .\input$trdy (\bus_ins2$trdy )
    , .\output$irdy (\channel2$irdy )
    , .\output$data (\channel2$data )
    , .\output$trdy (\channel2$trdy )
  );
  
endmodule

module \EJECTION_2$type2 (
      input \clk , input \rst 
    , input \bus_ins1$irdy , input [1:0] \bus_ins1$data , output \bus_ins1$trdy 
    , input \bus_ins2$irdy , input [1:0] \bus_ins2$data , output \bus_ins2$trdy 
    , input \bus_ins3$irdy , input [1:0] \bus_ins3$data , output \bus_ins3$trdy 
    , output \output$irdy , output [1:0] \output$data , input \output$trdy 
  );
  
  //
  // Channel declarations
  //
  wire \channel1$irdy  ;
  wire [1:0] \channel1$data  ;
  wire \channel1$trdy  ;
  wire \channel2$irdy  ;
  wire [1:0] \channel2$data  ;
  wire \channel2$trdy  ;
  wire \channel3$irdy  ;
  wire [1:0] \channel3$data  ;
  wire \channel3$trdy  ;
  
  //
  // Component and Macro instantiations
  //
  \Queue  #(
    .NUM_DATA(0),
    .DATASIZE(2),
    .LENGTH(2)
  ) \Queue1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\bus_ins3$irdy )
    , .\i0$data (\bus_ins3$data )
    , .\i0$trdy (\bus_ins3$trdy )
    , .\o0$irdy (\channel3$irdy )
    , .\o0$data (\channel3$data )
    , .\o0$trdy (\channel3$trdy )
  );
  
  \Merge3$type2  \Merge31  (
      .\clk (\clk ), .\rst (\rst )
    , .\bus_ins1$irdy (\channel1$irdy )
    , .\bus_ins1$data (\channel1$data )
    , .\bus_ins1$trdy (\channel1$trdy )
    , .\bus_ins2$irdy (\channel2$irdy )
    , .\bus_ins2$data (\channel2$data )
    , .\bus_ins2$trdy (\channel2$trdy )
    , .\bus_ins3$irdy (\channel3$irdy )
    , .\bus_ins3$data (\channel3$data )
    , .\bus_ins3$trdy (\channel3$trdy )
    , .\output$irdy (\output$irdy )
    , .\output$data (\output$data )
    , .\output$trdy (\output$trdy )
  );
  
  \Latch$type2  \Latch1  (
      .\clk (\clk ), .\rst (\rst )
    , .\input$irdy (\bus_ins1$irdy )
    , .\input$data (\bus_ins1$data )
    , .\input$trdy (\bus_ins1$trdy )
    , .\output$irdy (\channel1$irdy )
    , .\output$data (\channel1$data )
    , .\output$trdy (\channel1$trdy )
  );
  
  \Latch$type1  \Latch2  (
      .\clk (\clk ), .\rst (\rst )
    , .\input$irdy (\bus_ins2$irdy )
    , .\input$data (\bus_ins2$data )
    , .\input$trdy (\bus_ins2$trdy )
    , .\output$irdy (\channel2$irdy )
    , .\output$data (\channel2$data )
    , .\output$trdy (\channel2$trdy )
  );
  
endmodule

module \EJECTION_2$type3 (
      input \clk , input \rst 
    , input \bus_ins1$irdy , input [1:0] \bus_ins1$data , output \bus_ins1$trdy 
    , input \bus_ins2$irdy , input [1:0] \bus_ins2$data , output \bus_ins2$trdy 
    , input \bus_ins3$irdy , input [1:0] \bus_ins3$data , output \bus_ins3$trdy 
    , output \output$irdy , output [1:0] \output$data , input \output$trdy 
  );
  
  //
  // Channel declarations
  //
  wire \channel1$irdy  ;
  wire [1:0] \channel1$data  ;
  wire \channel1$trdy  ;
  wire \channel2$irdy  ;
  wire [1:0] \channel2$data  ;
  wire \channel2$trdy  ;
  wire \channel3$irdy  ;
  wire [1:0] \channel3$data  ;
  wire \channel3$trdy  ;
  
  //
  // Component and Macro instantiations
  //
  \Queue  #(
    .NUM_DATA(0),
    .DATASIZE(2),
    .LENGTH(2)
  ) \Queue1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\bus_ins3$irdy )
    , .\i0$data (\bus_ins3$data )
    , .\i0$trdy (\bus_ins3$trdy )
    , .\o0$irdy (\channel3$irdy )
    , .\o0$data (\channel3$data )
    , .\o0$trdy (\channel3$trdy )
  );
  
  \Merge3$type3  \Merge31  (
      .\clk (\clk ), .\rst (\rst )
    , .\bus_ins1$irdy (\channel1$irdy )
    , .\bus_ins1$data (\channel1$data )
    , .\bus_ins1$trdy (\channel1$trdy )
    , .\bus_ins2$irdy (\channel2$irdy )
    , .\bus_ins2$data (\channel2$data )
    , .\bus_ins2$trdy (\channel2$trdy )
    , .\bus_ins3$irdy (\channel3$irdy )
    , .\bus_ins3$data (\channel3$data )
    , .\bus_ins3$trdy (\channel3$trdy )
    , .\output$irdy (\output$irdy )
    , .\output$data (\output$data )
    , .\output$trdy (\output$trdy )
  );
  
  \Latch$type2  \Latch1  (
      .\clk (\clk ), .\rst (\rst )
    , .\input$irdy (\bus_ins1$irdy )
    , .\input$data (\bus_ins1$data )
    , .\input$trdy (\bus_ins1$trdy )
    , .\output$irdy (\channel1$irdy )
    , .\output$data (\channel1$data )
    , .\output$trdy (\channel1$trdy )
  );
  
  \Latch$type5  \Latch2  (
      .\clk (\clk ), .\rst (\rst )
    , .\input$irdy (\bus_ins2$irdy )
    , .\input$data (\bus_ins2$data )
    , .\input$trdy (\bus_ins2$trdy )
    , .\output$irdy (\channel2$irdy )
    , .\output$data (\channel2$data )
    , .\output$trdy (\channel2$trdy )
  );
  
endmodule

module \EJECTION_2$type4 (
      input \clk , input \rst 
    , input \bus_ins1$irdy , input [1:0] \bus_ins1$data , output \bus_ins1$trdy 
    , input \bus_ins2$irdy , input [1:0] \bus_ins2$data , output \bus_ins2$trdy 
    , input \bus_ins3$irdy , input [1:0] \bus_ins3$data , output \bus_ins3$trdy 
    , output \output$irdy , output [1:0] \output$data , input \output$trdy 
  );
  
  //
  // Channel declarations
  //
  wire \channel1$irdy  ;
  wire [1:0] \channel1$data  ;
  wire \channel1$trdy  ;
  wire \channel2$irdy  ;
  wire [1:0] \channel2$data  ;
  wire \channel2$trdy  ;
  wire \channel3$irdy  ;
  wire [1:0] \channel3$data  ;
  wire \channel3$trdy  ;
  
  //
  // Component and Macro instantiations
  //
  \Queue  #(
    .NUM_DATA(0),
    .DATASIZE(2),
    .LENGTH(2)
  ) \Queue1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\bus_ins3$irdy )
    , .\i0$data (\bus_ins3$data )
    , .\i0$trdy (\bus_ins3$trdy )
    , .\o0$irdy (\channel3$irdy )
    , .\o0$data (\channel3$data )
    , .\o0$trdy (\channel3$trdy )
  );
  
  \Merge3$type4  \Merge31  (
      .\clk (\clk ), .\rst (\rst )
    , .\bus_ins1$irdy (\channel1$irdy )
    , .\bus_ins1$data (\channel1$data )
    , .\bus_ins1$trdy (\channel1$trdy )
    , .\bus_ins2$irdy (\channel2$irdy )
    , .\bus_ins2$data (\channel2$data )
    , .\bus_ins2$trdy (\channel2$trdy )
    , .\bus_ins3$irdy (\channel3$irdy )
    , .\bus_ins3$data (\channel3$data )
    , .\bus_ins3$trdy (\channel3$trdy )
    , .\output$irdy (\output$irdy )
    , .\output$data (\output$data )
    , .\output$trdy (\output$trdy )
  );
  
  \Latch$type6  \Latch1  (
      .\clk (\clk ), .\rst (\rst )
    , .\input$irdy (\bus_ins1$irdy )
    , .\input$data (\bus_ins1$data )
    , .\input$trdy (\bus_ins1$trdy )
    , .\output$irdy (\channel1$irdy )
    , .\output$data (\channel1$data )
    , .\output$trdy (\channel1$trdy )
  );
  
  \Latch$type3  \Latch2  (
      .\clk (\clk ), .\rst (\rst )
    , .\input$irdy (\bus_ins2$irdy )
    , .\input$data (\bus_ins2$data )
    , .\input$trdy (\bus_ins2$trdy )
    , .\output$irdy (\channel2$irdy )
    , .\output$data (\channel2$data )
    , .\output$trdy (\channel2$trdy )
  );
  
endmodule

module \EJECTION_2$type5 (
      input \clk , input \rst 
    , input \bus_ins1$irdy , input [1:0] \bus_ins1$data , output \bus_ins1$trdy 
    , input \bus_ins2$irdy , input [1:0] \bus_ins2$data , output \bus_ins2$trdy 
    , input \bus_ins3$irdy , input [1:0] \bus_ins3$data , output \bus_ins3$trdy 
    , output \output$irdy , output [1:0] \output$data , input \output$trdy 
  );
  
  //
  // Channel declarations
  //
  wire \channel1$irdy  ;
  wire [1:0] \channel1$data  ;
  wire \channel1$trdy  ;
  wire \channel2$irdy  ;
  wire [1:0] \channel2$data  ;
  wire \channel2$trdy  ;
  wire \channel3$irdy  ;
  wire [1:0] \channel3$data  ;
  wire \channel3$trdy  ;
  
  //
  // Component and Macro instantiations
  //
  \Queue  #(
    .NUM_DATA(0),
    .DATASIZE(2),
    .LENGTH(2)
  ) \Queue1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\bus_ins3$irdy )
    , .\i0$data (\bus_ins3$data )
    , .\i0$trdy (\bus_ins3$trdy )
    , .\o0$irdy (\channel3$irdy )
    , .\o0$data (\channel3$data )
    , .\o0$trdy (\channel3$trdy )
  );
  
  \Merge3$type5  \Merge31  (
      .\clk (\clk ), .\rst (\rst )
    , .\bus_ins1$irdy (\channel1$irdy )
    , .\bus_ins1$data (\channel1$data )
    , .\bus_ins1$trdy (\channel1$trdy )
    , .\bus_ins2$irdy (\channel2$irdy )
    , .\bus_ins2$data (\channel2$data )
    , .\bus_ins2$trdy (\channel2$trdy )
    , .\bus_ins3$irdy (\channel3$irdy )
    , .\bus_ins3$data (\channel3$data )
    , .\bus_ins3$trdy (\channel3$trdy )
    , .\output$irdy (\output$irdy )
    , .\output$data (\output$data )
    , .\output$trdy (\output$trdy )
  );
  
  \Latch$type6  \Latch1  (
      .\clk (\clk ), .\rst (\rst )
    , .\input$irdy (\bus_ins1$irdy )
    , .\input$data (\bus_ins1$data )
    , .\input$trdy (\bus_ins1$trdy )
    , .\output$irdy (\channel1$irdy )
    , .\output$data (\channel1$data )
    , .\output$trdy (\channel1$trdy )
  );
  
  \Latch$type7  \Latch2  (
      .\clk (\clk ), .\rst (\rst )
    , .\input$irdy (\bus_ins2$irdy )
    , .\input$data (\bus_ins2$data )
    , .\input$trdy (\bus_ins2$trdy )
    , .\output$irdy (\channel2$irdy )
    , .\output$data (\channel2$data )
    , .\output$trdy (\channel2$trdy )
  );
  
endmodule

module \EJECTION_2$type6 (
      input \clk , input \rst 
    , input \bus_ins1$irdy , input [1:0] \bus_ins1$data , output \bus_ins1$trdy 
    , input \bus_ins2$irdy , input [1:0] \bus_ins2$data , output \bus_ins2$trdy 
    , input \bus_ins3$irdy , input [1:0] \bus_ins3$data , output \bus_ins3$trdy 
    , output \output$irdy , output [1:0] \output$data , input \output$trdy 
  );
  
  //
  // Channel declarations
  //
  wire \channel1$irdy  ;
  wire [1:0] \channel1$data  ;
  wire \channel1$trdy  ;
  wire \channel2$irdy  ;
  wire [1:0] \channel2$data  ;
  wire \channel2$trdy  ;
  wire \channel3$irdy  ;
  wire [1:0] \channel3$data  ;
  wire \channel3$trdy  ;
  
  //
  // Component and Macro instantiations
  //
  \Queue  #(
    .NUM_DATA(0),
    .DATASIZE(2),
    .LENGTH(2)
  ) \Queue1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\bus_ins3$irdy )
    , .\i0$data (\bus_ins3$data )
    , .\i0$trdy (\bus_ins3$trdy )
    , .\o0$irdy (\channel3$irdy )
    , .\o0$data (\channel3$data )
    , .\o0$trdy (\channel3$trdy )
  );
  
  \Merge3$type6  \Merge31  (
      .\clk (\clk ), .\rst (\rst )
    , .\bus_ins1$irdy (\channel1$irdy )
    , .\bus_ins1$data (\channel1$data )
    , .\bus_ins1$trdy (\channel1$trdy )
    , .\bus_ins2$irdy (\channel2$irdy )
    , .\bus_ins2$data (\channel2$data )
    , .\bus_ins2$trdy (\channel2$trdy )
    , .\bus_ins3$irdy (\channel3$irdy )
    , .\bus_ins3$data (\channel3$data )
    , .\bus_ins3$trdy (\channel3$trdy )
    , .\output$irdy (\output$irdy )
    , .\output$data (\output$data )
    , .\output$trdy (\output$trdy )
  );
  
  \Latch$type8  \Latch1  (
      .\clk (\clk ), .\rst (\rst )
    , .\input$irdy (\bus_ins1$irdy )
    , .\input$data (\bus_ins1$data )
    , .\input$trdy (\bus_ins1$trdy )
    , .\output$irdy (\channel1$irdy )
    , .\output$data (\channel1$data )
    , .\output$trdy (\channel1$trdy )
  );
  
  \Latch$type5  \Latch2  (
      .\clk (\clk ), .\rst (\rst )
    , .\input$irdy (\bus_ins2$irdy )
    , .\input$data (\bus_ins2$data )
    , .\input$trdy (\bus_ins2$trdy )
    , .\output$irdy (\channel2$irdy )
    , .\output$data (\channel2$data )
    , .\output$trdy (\channel2$trdy )
  );
  
endmodule

module \EJECTION_2$type7 (
      input \clk , input \rst 
    , input \bus_ins1$irdy , input [1:0] \bus_ins1$data , output \bus_ins1$trdy 
    , input \bus_ins2$irdy , input [1:0] \bus_ins2$data , output \bus_ins2$trdy 
    , input \bus_ins3$irdy , input [1:0] \bus_ins3$data , output \bus_ins3$trdy 
    , output \output$irdy , output [1:0] \output$data , input \output$trdy 
  );
  
  //
  // Channel declarations
  //
  wire \channel1$irdy  ;
  wire [1:0] \channel1$data  ;
  wire \channel1$trdy  ;
  wire \channel2$irdy  ;
  wire [1:0] \channel2$data  ;
  wire \channel2$trdy  ;
  wire \channel3$irdy  ;
  wire [1:0] \channel3$data  ;
  wire \channel3$trdy  ;
  
  //
  // Component and Macro instantiations
  //
  \Queue  #(
    .NUM_DATA(0),
    .DATASIZE(2),
    .LENGTH(2)
  ) \Queue1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\bus_ins3$irdy )
    , .\i0$data (\bus_ins3$data )
    , .\i0$trdy (\bus_ins3$trdy )
    , .\o0$irdy (\channel3$irdy )
    , .\o0$data (\channel3$data )
    , .\o0$trdy (\channel3$trdy )
  );
  
  \Merge3$type7  \Merge31  (
      .\clk (\clk ), .\rst (\rst )
    , .\bus_ins1$irdy (\channel1$irdy )
    , .\bus_ins1$data (\channel1$data )
    , .\bus_ins1$trdy (\channel1$trdy )
    , .\bus_ins2$irdy (\channel2$irdy )
    , .\bus_ins2$data (\channel2$data )
    , .\bus_ins2$trdy (\channel2$trdy )
    , .\bus_ins3$irdy (\channel3$irdy )
    , .\bus_ins3$data (\channel3$data )
    , .\bus_ins3$trdy (\channel3$trdy )
    , .\output$irdy (\output$irdy )
    , .\output$data (\output$data )
    , .\output$trdy (\output$trdy )
  );
  
  \Latch$type8  \Latch1  (
      .\clk (\clk ), .\rst (\rst )
    , .\input$irdy (\bus_ins1$irdy )
    , .\input$data (\bus_ins1$data )
    , .\input$trdy (\bus_ins1$trdy )
    , .\output$irdy (\channel1$irdy )
    , .\output$data (\channel1$data )
    , .\output$trdy (\channel1$trdy )
  );
  
  \Latch$type7  \Latch2  (
      .\clk (\clk ), .\rst (\rst )
    , .\input$irdy (\bus_ins2$irdy )
    , .\input$data (\bus_ins2$data )
    , .\input$trdy (\bus_ins2$trdy )
    , .\output$irdy (\channel2$irdy )
    , .\output$data (\channel2$data )
    , .\output$trdy (\channel2$trdy )
  );
  
endmodule

module \RECEPTION_0_1_0_2 (
      input \clk , input \rst , input [63:0] \t 
    , input \input$irdy , input [1:0] \input$data , output \input$trdy 
    , output \bus_outs1$irdy , output [1:0] \bus_outs1$data , input \bus_outs1$trdy 
    , output \bus_outs2$irdy , output [1:0] \bus_outs2$data , input \bus_outs2$trdy 
    , output \bus_outs3$irdy , output [1:0] \bus_outs3$data , input \bus_outs3$trdy 
    , output \bus_outs4$irdy , output [0:0] \bus_outs4$data , input \bus_outs4$trdy 
    , input \CreditCounter1$PatientSource1$unbound_irdy 
    , input [0:0] \CreditCounter1$PatientSource1$unbound_data 
    , output \CreditCounter1$PatientSource1$trdy 
    , input \CreditCounter1$Sink1$unbound_trdy 
    , output \CreditCounter1$Sink1$irdy 
    , output [0:0] \CreditCounter1$Sink1$data 
  );
  
  //
  // Channel declarations
  //
  wire \noCONS$irdy  ;
  wire [1:0] \noCONS$data  ;
  wire \noCONS$trdy  ;
  wire \toRCP$irdy  ;
  wire [1:0] \toRCP$data  ;
  wire \toRCP$trdy  ;
  wire \creditBack$irdy  ;
  wire [1:0] \creditBack$data  ;
  wire \creditBack$trdy  ;
  wire \channel1$irdy  ;
  wire [1:0] \channel1$data  ;
  wire \channel1$trdy  ;
  
  //
  // Function Channels
  //
  wire \sfunchan_0_Switch1$data  ;
  wire [1:0] \ofunchan_1_Switch1$data  ;
  wire [1:0] \ofunchan_2_Switch1$data  ;
  wire \sfunchan_0_Switch2$data  ;
  wire [1:0] \ofunchan_1_Switch2$data  ;
  wire [1:0] \ofunchan_2_Switch2$data  ;
  
  //
  // Component and Macro instantiations
  //
  \Fork2  #(
    .DATASIZE(2)
  ) \Fork1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\channel1$irdy )
    , .\i0$data (\channel1$data )
    , .\i0$trdy (\channel1$trdy )
    , .\o0$irdy (\toRCP$irdy )
    , .\o0$data (\toRCP$data )
    , .\o0$trdy (\toRCP$trdy )
    , .\o1$irdy (\creditBack$irdy )
    , .\o1$data (\creditBack$data )
    , .\o1$trdy (\creditBack$trdy )
  );
  
  \Queue  #(
    .NUM_DATA(0),
    .DATASIZE(2),
    .LENGTH(2)
  ) \Queue1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\input$irdy )
    , .\i0$data (\input$data )
    , .\i0$trdy (\input$trdy )
    , .\o0$irdy (\channel1$irdy )
    , .\o0$data (\channel1$data )
    , .\o0$trdy (\channel1$trdy )
  );
  
  \Switch2  #(
    .OUTPUTSIZE0(2),
    .OUTPUTSIZE1(2),
    .INPUTSIZE(2)
  ) \Switch1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\toRCP$irdy )
    , .\i0$data (\toRCP$data )
    , .\i0$trdy (\toRCP$trdy )
    , .\o0$irdy (\bus_outs1$irdy )
    , .\o0$data (\bus_outs1$data )
    , .\o0$trdy (\bus_outs1$trdy )
    , .\o1$irdy (\noCONS$irdy )
    , .\o1$data (\noCONS$data )
    , .\o1$trdy (\noCONS$trdy )
    , .\sel$data (\sfunchan_0_Switch1$data )
    , .\f0$data (\ofunchan_1_Switch1$data )
    , .\f1$data (\ofunchan_2_Switch1$data )
  );
  
  \SFUN_0$RECEPTION_0_1_0_2_Switch1  \sfun_0_Switch1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\toRCP$data )
    , .\o0 (\sfunchan_0_Switch1$data )
  );
  
  \OFUN_1$RECEPTION_0_1_0_2_Switch1  \ofun_1_Switch1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\toRCP$data )
    , .\o0 (\ofunchan_1_Switch1$data )
  );
  
  \OFUN_2$RECEPTION_0_1_0_2_Switch1  \ofun_2_Switch1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\toRCP$data )
    , .\o0 (\ofunchan_2_Switch1$data )
  );
  
  \Switch2  #(
    .OUTPUTSIZE0(2),
    .OUTPUTSIZE1(2),
    .INPUTSIZE(2)
  ) \Switch2  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\noCONS$irdy )
    , .\i0$data (\noCONS$data )
    , .\i0$trdy (\noCONS$trdy )
    , .\o0$irdy (\bus_outs2$irdy )
    , .\o0$data (\bus_outs2$data )
    , .\o0$trdy (\bus_outs2$trdy )
    , .\o1$irdy (\bus_outs3$irdy )
    , .\o1$data (\bus_outs3$data )
    , .\o1$trdy (\bus_outs3$trdy )
    , .\sel$data (\sfunchan_0_Switch2$data )
    , .\f0$data (\ofunchan_1_Switch2$data )
    , .\f1$data (\ofunchan_2_Switch2$data )
  );
  
  \SFUN_0$RECEPTION_0_1_0_2_Switch2  \sfun_0_Switch2  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\noCONS$data )
    , .\o0 (\sfunchan_0_Switch2$data )
  );
  
  \OFUN_1$RECEPTION_0_1_0_2_Switch2  \ofun_1_Switch2  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\noCONS$data )
    , .\o0 (\ofunchan_1_Switch2$data )
  );
  
  \OFUN_2$RECEPTION_0_1_0_2_Switch2  \ofun_2_Switch2  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\noCONS$data )
    , .\o0 (\ofunchan_2_Switch2$data )
  );
  
  \CreditCounter_2  \CreditCounter1  (
      .\clk (\clk ), .\rst (\rst ), .\t (\t )
    , .\i$irdy (\creditBack$irdy )
    , .\i$data (\creditBack$data )
    , .\i$trdy (\creditBack$trdy )
    , .\o$irdy (\bus_outs4$irdy )
    , .\o$data (\bus_outs4$data )
    , .\o$trdy (\bus_outs4$trdy )
    , .\PatientSource1$unbound_irdy (\CreditCounter1$PatientSource1$unbound_irdy )
    , .\PatientSource1$unbound_data (\CreditCounter1$PatientSource1$unbound_data )
    , .\PatientSource1$trdy (\CreditCounter1$PatientSource1$trdy )
    , .\Sink1$unbound_trdy (\CreditCounter1$Sink1$unbound_trdy )
    , .\Sink1$irdy (\CreditCounter1$Sink1$irdy )
    , .\Sink1$data (\CreditCounter1$Sink1$data )
  );
  
endmodule


//
// RECEPTION_0_1_0_2 switch functions
//
module \SFUN_0$RECEPTION_0_1_0_2_Switch1 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , output [0:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[1:0] \f$bool$g0  = \i0$data  ;
  wire[1:0] \f$bool$f$arg0$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$arg0$arg0$conj  = \f$bool$f$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$arg0$arg0  = \f$bool$f$arg0$arg0$conj [1:1] ;
  wire[0:0] \f$bool$f$arg0$arg1  = 1'd0 ;
  wire \f$bool$f$arg0  = \f$bool$f$arg0$arg0  == \f$bool$f$arg0$arg1  ;
  wire[1:0] \f$bool$f$arg1$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$arg1$arg0$conj  = \f$bool$f$arg1$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$arg1$arg0  = \f$bool$f$arg1$arg0$conj [0:0] ;
  wire[0:0] \f$bool$f$arg1$arg1  = 1'd1 ;
  wire \f$bool$f$arg1  = \f$bool$f$arg1$arg0  == \f$bool$f$arg1$arg1  ;
  wire \f$bool$f  = \f$bool$f$arg0  && \f$bool$f$arg1  ;
  wire \f$bool  = \f$bool$f  ;
  wire[0:0] \f$true$content  = 1'd0 ;
  wire[0:0] \f$true  = \f$true$content  ;
  wire[1:0] \f$false$bool$g0  = \i0$data  ;
  wire[1:0] \f$false$bool$f$arg0$arg0$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$arg0$arg0$conj  = \f$false$bool$f$arg0$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$arg0$arg0  = \f$false$bool$f$arg0$arg0$arg0$conj [1:1] ;
  wire[0:0] \f$false$bool$f$arg0$arg0$arg1  = 1'd0 ;
  wire \f$false$bool$f$arg0$arg0  = \f$false$bool$f$arg0$arg0$arg0  == \f$false$bool$f$arg0$arg0$arg1  ;
  wire[1:0] \f$false$bool$f$arg0$arg1$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$arg1$arg0$conj  = \f$false$bool$f$arg0$arg1$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$arg1$arg0  = \f$false$bool$f$arg0$arg1$arg0$conj [0:0] ;
  wire[0:0] \f$false$bool$f$arg0$arg1$arg1  = 1'd1 ;
  wire \f$false$bool$f$arg0$arg1  = \f$false$bool$f$arg0$arg1$arg0  == \f$false$bool$f$arg0$arg1$arg1  ;
  wire \f$false$bool$f$arg0  = \f$false$bool$f$arg0$arg0  && \f$false$bool$f$arg0$arg1  ;
  wire \f$false$bool$f  = !\f$false$bool$f$arg0  ;
  wire \f$false$bool  = \f$false$bool$f  ;
  wire[0:0] \f$false$true$content  = 1'd1 ;
  wire[0:0] \f$false$true  = \f$false$true$content  ;
  wire[0:0] \f$false$false$content  = 1'd0 ;
  wire[0:0] \f$false$false  = \f$false$false$content  ;
  wire[0:0] \f$false  = ( \f$false$bool  ? \f$false$true  : \f$false$false  ) ;
  wire[0:0] \f  = ( \f$bool  ? \f$true  : \f$false  ) ;
  
  assign \o0  = \f  ;
endmodule

module \OFUN_1$RECEPTION_0_1_0_2_Switch1 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , output [1:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[1:0] \f  = \i0$data  ;
  
  assign \o0  = \f  ;
endmodule

module \OFUN_2$RECEPTION_0_1_0_2_Switch1 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , output [1:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[1:0] \f  = \i0$data  ;
  
  assign \o0  = \f  ;
endmodule

module \SFUN_0$RECEPTION_0_1_0_2_Switch2 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , output [0:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[1:0] \f$bool$g0  = \i0$data  ;
  wire \f$bool$f$bool  = 1'd1 ;
  wire[1:0] \f$bool$f$true$arg0$arg0$arg0$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$true$arg0$arg0$arg0$arg0$conj  = \f$bool$f$true$arg0$arg0$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$true$arg0$arg0$arg0$arg0  = \f$bool$f$true$arg0$arg0$arg0$arg0$conj [1:1] ;
  wire[0:0] \f$bool$f$true$arg0$arg0$arg0$arg1  = 1'd0 ;
  wire \f$bool$f$true$arg0$arg0$arg0  = \f$bool$f$true$arg0$arg0$arg0$arg0  == \f$bool$f$true$arg0$arg0$arg0$arg1  ;
  wire \f$bool$f$true$arg0$arg0  = !\f$bool$f$true$arg0$arg0$arg0  ;
  wire[1:0] \f$bool$f$true$arg0$arg1$arg0$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$true$arg0$arg1$arg0$arg0$conj  = \f$bool$f$true$arg0$arg1$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$true$arg0$arg1$arg0$arg0  = \f$bool$f$true$arg0$arg1$arg0$arg0$conj [1:1] ;
  wire[0:0] \f$bool$f$true$arg0$arg1$arg0$arg1  = 1'd0 ;
  wire \f$bool$f$true$arg0$arg1$arg0  = \f$bool$f$true$arg0$arg1$arg0$arg0  > \f$bool$f$true$arg0$arg1$arg0$arg1  ;
  wire \f$bool$f$true$arg0$arg1  = !\f$bool$f$true$arg0$arg1$arg0  ;
  wire \f$bool$f$true$arg0  = \f$bool$f$true$arg0$arg0  && \f$bool$f$true$arg0$arg1  ;
  wire \f$bool$f$true$arg1$arg0  = 1'd1 ;
  wire[1:0] \f$bool$f$true$arg1$arg1$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$true$arg1$arg1$arg0$conj  = \f$bool$f$true$arg1$arg1$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$true$arg1$arg1$arg0  = \f$bool$f$true$arg1$arg1$arg0$conj [1:1] ;
  wire[0:0] \f$bool$f$true$arg1$arg1$arg1  = 1'd1 ;
  wire \f$bool$f$true$arg1$arg1  = \f$bool$f$true$arg1$arg1$arg0  == \f$bool$f$true$arg1$arg1$arg1  ;
  wire \f$bool$f$true$arg1  = \f$bool$f$true$arg1$arg0  && \f$bool$f$true$arg1$arg1  ;
  wire \f$bool$f$true  = \f$bool$f$true$arg0  || \f$bool$f$true$arg1  ;
  wire \f$bool$f$false$bool  = 1'd0 ;
  wire[1:0] \f$bool$f$false$true$arg0$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$false$true$arg0$arg0$conj  = \f$bool$f$false$true$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$false$true$arg0$arg0  = \f$bool$f$false$true$arg0$arg0$conj [1:1] ;
  wire[0:0] \f$bool$f$false$true$arg0$arg1  = 1'd0 ;
  wire \f$bool$f$false$true$arg0  = \f$bool$f$false$true$arg0$arg0  > \f$bool$f$false$true$arg0$arg1  ;
  wire \f$bool$f$false$true$arg1  = 1'd0 ;
  wire \f$bool$f$false$true  = \f$bool$f$false$true$arg0  || \f$bool$f$false$true$arg1  ;
  wire \f$bool$f$false$false$bool  = 1'd0 ;
  wire[1:0] \f$bool$f$false$false$true$arg0$arg0$arg0$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$false$false$true$arg0$arg0$arg0$arg0$conj  = \f$bool$f$false$false$true$arg0$arg0$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$false$false$true$arg0$arg0$arg0$arg0  = \f$bool$f$false$false$true$arg0$arg0$arg0$arg0$conj [0:0] ;
  wire[0:0] \f$bool$f$false$false$true$arg0$arg0$arg0$arg1  = 1'd1 ;
  wire \f$bool$f$false$false$true$arg0$arg0$arg0  = \f$bool$f$false$false$true$arg0$arg0$arg0$arg0  == \f$bool$f$false$false$true$arg0$arg0$arg0$arg1  ;
  wire \f$bool$f$false$false$true$arg0$arg0  = !\f$bool$f$false$false$true$arg0$arg0$arg0  ;
  wire[1:0] \f$bool$f$false$false$true$arg0$arg1$arg0$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$false$false$true$arg0$arg1$arg0$arg0$conj  = \f$bool$f$false$false$true$arg0$arg1$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$false$false$true$arg0$arg1$arg0$arg0  = \f$bool$f$false$false$true$arg0$arg1$arg0$arg0$conj [0:0] ;
  wire[0:0] \f$bool$f$false$false$true$arg0$arg1$arg0$arg1  = 1'd1 ;
  wire \f$bool$f$false$false$true$arg0$arg1$arg0  = \f$bool$f$false$false$true$arg0$arg1$arg0$arg0  > \f$bool$f$false$false$true$arg0$arg1$arg0$arg1  ;
  wire \f$bool$f$false$false$true$arg0$arg1  = !\f$bool$f$false$false$true$arg0$arg1$arg0  ;
  wire \f$bool$f$false$false$true$arg0  = \f$bool$f$false$false$true$arg0$arg0  && \f$bool$f$false$false$true$arg0$arg1  ;
  wire \f$bool$f$false$false$true$arg1  = 1'd0 ;
  wire \f$bool$f$false$false$true  = \f$bool$f$false$false$true$arg0  || \f$bool$f$false$false$true$arg1  ;
  wire[1:0] \f$bool$f$false$false$false$arg0$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$false$false$false$arg0$arg0$conj  = \f$bool$f$false$false$false$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$false$false$false$arg0$arg0  = \f$bool$f$false$false$false$arg0$arg0$conj [0:0] ;
  wire[0:0] \f$bool$f$false$false$false$arg0$arg1  = 1'd1 ;
  wire \f$bool$f$false$false$false$arg0  = \f$bool$f$false$false$false$arg0$arg0  > \f$bool$f$false$false$false$arg0$arg1  ;
  wire \f$bool$f$false$false$false$arg1$arg0  = 1'd1 ;
  wire[1:0] \f$bool$f$false$false$false$arg1$arg1$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$false$false$false$arg1$arg1$arg0$conj  = \f$bool$f$false$false$false$arg1$arg1$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$false$false$false$arg1$arg1$arg0  = \f$bool$f$false$false$false$arg1$arg1$arg0$conj [0:0] ;
  wire[0:0] \f$bool$f$false$false$false$arg1$arg1$arg1  = 1'd0 ;
  wire \f$bool$f$false$false$false$arg1$arg1  = \f$bool$f$false$false$false$arg1$arg1$arg0  == \f$bool$f$false$false$false$arg1$arg1$arg1  ;
  wire \f$bool$f$false$false$false$arg1  = \f$bool$f$false$false$false$arg1$arg0  && \f$bool$f$false$false$false$arg1$arg1  ;
  wire \f$bool$f$false$false$false  = \f$bool$f$false$false$false$arg0  || \f$bool$f$false$false$false$arg1  ;
  wire \f$bool$f$false$false  = ( \f$bool$f$false$false$bool  ? \f$bool$f$false$false$true  : \f$bool$f$false$false$false  ) ;
  wire \f$bool$f$false  = ( \f$bool$f$false$bool  ? \f$bool$f$false$true  : \f$bool$f$false$false  ) ;
  wire \f$bool$f  = ( \f$bool$f$bool  ? \f$bool$f$true  : \f$bool$f$false  ) ;
  wire \f$bool  = \f$bool$f  ;
  wire[0:0] \f$true$content  = 1'd0 ;
  wire[0:0] \f$true  = \f$true$content  ;
  wire[1:0] \f$false$bool$g0  = \i0$data  ;
  wire \f$false$bool$f$arg0$bool  = 1'd1 ;
  wire[1:0] \f$false$bool$f$arg0$true$arg0$arg0$arg0$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$true$arg0$arg0$arg0$arg0$conj  = \f$false$bool$f$arg0$true$arg0$arg0$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$true$arg0$arg0$arg0$arg0  = \f$false$bool$f$arg0$true$arg0$arg0$arg0$arg0$conj [1:1] ;
  wire[0:0] \f$false$bool$f$arg0$true$arg0$arg0$arg0$arg1  = 1'd0 ;
  wire \f$false$bool$f$arg0$true$arg0$arg0$arg0  = \f$false$bool$f$arg0$true$arg0$arg0$arg0$arg0  == \f$false$bool$f$arg0$true$arg0$arg0$arg0$arg1  ;
  wire \f$false$bool$f$arg0$true$arg0$arg0  = !\f$false$bool$f$arg0$true$arg0$arg0$arg0  ;
  wire[1:0] \f$false$bool$f$arg0$true$arg0$arg1$arg0$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$true$arg0$arg1$arg0$arg0$conj  = \f$false$bool$f$arg0$true$arg0$arg1$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$true$arg0$arg1$arg0$arg0  = \f$false$bool$f$arg0$true$arg0$arg1$arg0$arg0$conj [1:1] ;
  wire[0:0] \f$false$bool$f$arg0$true$arg0$arg1$arg0$arg1  = 1'd0 ;
  wire \f$false$bool$f$arg0$true$arg0$arg1$arg0  = \f$false$bool$f$arg0$true$arg0$arg1$arg0$arg0  > \f$false$bool$f$arg0$true$arg0$arg1$arg0$arg1  ;
  wire \f$false$bool$f$arg0$true$arg0$arg1  = !\f$false$bool$f$arg0$true$arg0$arg1$arg0  ;
  wire \f$false$bool$f$arg0$true$arg0  = \f$false$bool$f$arg0$true$arg0$arg0  && \f$false$bool$f$arg0$true$arg0$arg1  ;
  wire \f$false$bool$f$arg0$true$arg1$arg0  = 1'd1 ;
  wire[1:0] \f$false$bool$f$arg0$true$arg1$arg1$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$true$arg1$arg1$arg0$conj  = \f$false$bool$f$arg0$true$arg1$arg1$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$true$arg1$arg1$arg0  = \f$false$bool$f$arg0$true$arg1$arg1$arg0$conj [1:1] ;
  wire[0:0] \f$false$bool$f$arg0$true$arg1$arg1$arg1  = 1'd1 ;
  wire \f$false$bool$f$arg0$true$arg1$arg1  = \f$false$bool$f$arg0$true$arg1$arg1$arg0  == \f$false$bool$f$arg0$true$arg1$arg1$arg1  ;
  wire \f$false$bool$f$arg0$true$arg1  = \f$false$bool$f$arg0$true$arg1$arg0  && \f$false$bool$f$arg0$true$arg1$arg1  ;
  wire \f$false$bool$f$arg0$true  = \f$false$bool$f$arg0$true$arg0  || \f$false$bool$f$arg0$true$arg1  ;
  wire \f$false$bool$f$arg0$false$bool  = 1'd0 ;
  wire[1:0] \f$false$bool$f$arg0$false$true$arg0$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$false$true$arg0$arg0$conj  = \f$false$bool$f$arg0$false$true$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$false$true$arg0$arg0  = \f$false$bool$f$arg0$false$true$arg0$arg0$conj [1:1] ;
  wire[0:0] \f$false$bool$f$arg0$false$true$arg0$arg1  = 1'd0 ;
  wire \f$false$bool$f$arg0$false$true$arg0  = \f$false$bool$f$arg0$false$true$arg0$arg0  > \f$false$bool$f$arg0$false$true$arg0$arg1  ;
  wire \f$false$bool$f$arg0$false$true$arg1  = 1'd0 ;
  wire \f$false$bool$f$arg0$false$true  = \f$false$bool$f$arg0$false$true$arg0  || \f$false$bool$f$arg0$false$true$arg1  ;
  wire \f$false$bool$f$arg0$false$false$bool  = 1'd0 ;
  wire[1:0] \f$false$bool$f$arg0$false$false$true$arg0$arg0$arg0$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$false$false$true$arg0$arg0$arg0$arg0$conj  = \f$false$bool$f$arg0$false$false$true$arg0$arg0$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$false$false$true$arg0$arg0$arg0$arg0  = \f$false$bool$f$arg0$false$false$true$arg0$arg0$arg0$arg0$conj [0:0] ;
  wire[0:0] \f$false$bool$f$arg0$false$false$true$arg0$arg0$arg0$arg1  = 1'd1 ;
  wire \f$false$bool$f$arg0$false$false$true$arg0$arg0$arg0  = \f$false$bool$f$arg0$false$false$true$arg0$arg0$arg0$arg0  == \f$false$bool$f$arg0$false$false$true$arg0$arg0$arg0$arg1  ;
  wire \f$false$bool$f$arg0$false$false$true$arg0$arg0  = !\f$false$bool$f$arg0$false$false$true$arg0$arg0$arg0  ;
  wire[1:0] \f$false$bool$f$arg0$false$false$true$arg0$arg1$arg0$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$false$false$true$arg0$arg1$arg0$arg0$conj  = \f$false$bool$f$arg0$false$false$true$arg0$arg1$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$false$false$true$arg0$arg1$arg0$arg0  = \f$false$bool$f$arg0$false$false$true$arg0$arg1$arg0$arg0$conj [0:0] ;
  wire[0:0] \f$false$bool$f$arg0$false$false$true$arg0$arg1$arg0$arg1  = 1'd1 ;
  wire \f$false$bool$f$arg0$false$false$true$arg0$arg1$arg0  = \f$false$bool$f$arg0$false$false$true$arg0$arg1$arg0$arg0  > \f$false$bool$f$arg0$false$false$true$arg0$arg1$arg0$arg1  ;
  wire \f$false$bool$f$arg0$false$false$true$arg0$arg1  = !\f$false$bool$f$arg0$false$false$true$arg0$arg1$arg0  ;
  wire \f$false$bool$f$arg0$false$false$true$arg0  = \f$false$bool$f$arg0$false$false$true$arg0$arg0  && \f$false$bool$f$arg0$false$false$true$arg0$arg1  ;
  wire \f$false$bool$f$arg0$false$false$true$arg1  = 1'd0 ;
  wire \f$false$bool$f$arg0$false$false$true  = \f$false$bool$f$arg0$false$false$true$arg0  || \f$false$bool$f$arg0$false$false$true$arg1  ;
  wire[1:0] \f$false$bool$f$arg0$false$false$false$arg0$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$false$false$false$arg0$arg0$conj  = \f$false$bool$f$arg0$false$false$false$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$false$false$false$arg0$arg0  = \f$false$bool$f$arg0$false$false$false$arg0$arg0$conj [0:0] ;
  wire[0:0] \f$false$bool$f$arg0$false$false$false$arg0$arg1  = 1'd1 ;
  wire \f$false$bool$f$arg0$false$false$false$arg0  = \f$false$bool$f$arg0$false$false$false$arg0$arg0  > \f$false$bool$f$arg0$false$false$false$arg0$arg1  ;
  wire \f$false$bool$f$arg0$false$false$false$arg1$arg0  = 1'd1 ;
  wire[1:0] \f$false$bool$f$arg0$false$false$false$arg1$arg1$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$false$false$false$arg1$arg1$arg0$conj  = \f$false$bool$f$arg0$false$false$false$arg1$arg1$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$false$false$false$arg1$arg1$arg0  = \f$false$bool$f$arg0$false$false$false$arg1$arg1$arg0$conj [0:0] ;
  wire[0:0] \f$false$bool$f$arg0$false$false$false$arg1$arg1$arg1  = 1'd0 ;
  wire \f$false$bool$f$arg0$false$false$false$arg1$arg1  = \f$false$bool$f$arg0$false$false$false$arg1$arg1$arg0  == \f$false$bool$f$arg0$false$false$false$arg1$arg1$arg1  ;
  wire \f$false$bool$f$arg0$false$false$false$arg1  = \f$false$bool$f$arg0$false$false$false$arg1$arg0  && \f$false$bool$f$arg0$false$false$false$arg1$arg1  ;
  wire \f$false$bool$f$arg0$false$false$false  = \f$false$bool$f$arg0$false$false$false$arg0  || \f$false$bool$f$arg0$false$false$false$arg1  ;
  wire \f$false$bool$f$arg0$false$false  = ( \f$false$bool$f$arg0$false$false$bool  ? \f$false$bool$f$arg0$false$false$true  : \f$false$bool$f$arg0$false$false$false  ) ;
  wire \f$false$bool$f$arg0$false  = ( \f$false$bool$f$arg0$false$bool  ? \f$false$bool$f$arg0$false$true  : \f$false$bool$f$arg0$false$false  ) ;
  wire \f$false$bool$f$arg0  = ( \f$false$bool$f$arg0$bool  ? \f$false$bool$f$arg0$true  : \f$false$bool$f$arg0$false  ) ;
  wire \f$false$bool$f  = !\f$false$bool$f$arg0  ;
  wire \f$false$bool  = \f$false$bool$f  ;
  wire[0:0] \f$false$true$content  = 1'd1 ;
  wire[0:0] \f$false$true  = \f$false$true$content  ;
  wire[0:0] \f$false$false$content  = 1'd0 ;
  wire[0:0] \f$false$false  = \f$false$false$content  ;
  wire[0:0] \f$false  = ( \f$false$bool  ? \f$false$true  : \f$false$false  ) ;
  wire[0:0] \f  = ( \f$bool  ? \f$true  : \f$false  ) ;
  
  assign \o0  = \f  ;
endmodule

module \OFUN_1$RECEPTION_0_1_0_2_Switch2 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , output [1:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[1:0] \f  = \i0$data  ;
  
  assign \o0  = \f  ;
endmodule

module \OFUN_2$RECEPTION_0_1_0_2_Switch2 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , output [1:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[1:0] \f  = \i0$data  ;
  
  assign \o0  = \f  ;
endmodule

module \RECEPTION_1_0_0_2 (
      input \clk , input \rst , input [63:0] \t 
    , input \input$irdy , input [1:0] \input$data , output \input$trdy 
    , output \bus_outs1$irdy , output [1:0] \bus_outs1$data , input \bus_outs1$trdy 
    , output \bus_outs2$irdy , output [1:0] \bus_outs2$data , input \bus_outs2$trdy 
    , output \bus_outs3$irdy , output [1:0] \bus_outs3$data , input \bus_outs3$trdy 
    , output \bus_outs4$irdy , output [0:0] \bus_outs4$data , input \bus_outs4$trdy 
    , input \CreditCounter1$PatientSource1$unbound_irdy 
    , input [0:0] \CreditCounter1$PatientSource1$unbound_data 
    , output \CreditCounter1$PatientSource1$trdy 
    , input \CreditCounter1$Sink1$unbound_trdy 
    , output \CreditCounter1$Sink1$irdy 
    , output [0:0] \CreditCounter1$Sink1$data 
  );
  
  //
  // Channel declarations
  //
  wire \noCONS$irdy  ;
  wire [1:0] \noCONS$data  ;
  wire \noCONS$trdy  ;
  wire \toRCP$irdy  ;
  wire [1:0] \toRCP$data  ;
  wire \toRCP$trdy  ;
  wire \creditBack$irdy  ;
  wire [1:0] \creditBack$data  ;
  wire \creditBack$trdy  ;
  wire \channel1$irdy  ;
  wire [1:0] \channel1$data  ;
  wire \channel1$trdy  ;
  
  //
  // Function Channels
  //
  wire \sfunchan_0_Switch1$data  ;
  wire [1:0] \ofunchan_1_Switch1$data  ;
  wire [1:0] \ofunchan_2_Switch1$data  ;
  wire \sfunchan_0_Switch2$data  ;
  wire [1:0] \ofunchan_1_Switch2$data  ;
  wire [1:0] \ofunchan_2_Switch2$data  ;
  
  //
  // Component and Macro instantiations
  //
  \Fork2  #(
    .DATASIZE(2)
  ) \Fork1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\channel1$irdy )
    , .\i0$data (\channel1$data )
    , .\i0$trdy (\channel1$trdy )
    , .\o0$irdy (\toRCP$irdy )
    , .\o0$data (\toRCP$data )
    , .\o0$trdy (\toRCP$trdy )
    , .\o1$irdy (\creditBack$irdy )
    , .\o1$data (\creditBack$data )
    , .\o1$trdy (\creditBack$trdy )
  );
  
  \Queue  #(
    .NUM_DATA(0),
    .DATASIZE(2),
    .LENGTH(2)
  ) \Queue1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\input$irdy )
    , .\i0$data (\input$data )
    , .\i0$trdy (\input$trdy )
    , .\o0$irdy (\channel1$irdy )
    , .\o0$data (\channel1$data )
    , .\o0$trdy (\channel1$trdy )
  );
  
  \Switch2  #(
    .OUTPUTSIZE0(2),
    .OUTPUTSIZE1(2),
    .INPUTSIZE(2)
  ) \Switch1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\toRCP$irdy )
    , .\i0$data (\toRCP$data )
    , .\i0$trdy (\toRCP$trdy )
    , .\o0$irdy (\bus_outs1$irdy )
    , .\o0$data (\bus_outs1$data )
    , .\o0$trdy (\bus_outs1$trdy )
    , .\o1$irdy (\noCONS$irdy )
    , .\o1$data (\noCONS$data )
    , .\o1$trdy (\noCONS$trdy )
    , .\sel$data (\sfunchan_0_Switch1$data )
    , .\f0$data (\ofunchan_1_Switch1$data )
    , .\f1$data (\ofunchan_2_Switch1$data )
  );
  
  \SFUN_0$RECEPTION_1_0_0_2_Switch1  \sfun_0_Switch1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\toRCP$data )
    , .\o0 (\sfunchan_0_Switch1$data )
  );
  
  \OFUN_1$RECEPTION_1_0_0_2_Switch1  \ofun_1_Switch1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\toRCP$data )
    , .\o0 (\ofunchan_1_Switch1$data )
  );
  
  \OFUN_2$RECEPTION_1_0_0_2_Switch1  \ofun_2_Switch1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\toRCP$data )
    , .\o0 (\ofunchan_2_Switch1$data )
  );
  
  \Switch2  #(
    .OUTPUTSIZE0(2),
    .OUTPUTSIZE1(2),
    .INPUTSIZE(2)
  ) \Switch2  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\noCONS$irdy )
    , .\i0$data (\noCONS$data )
    , .\i0$trdy (\noCONS$trdy )
    , .\o0$irdy (\bus_outs2$irdy )
    , .\o0$data (\bus_outs2$data )
    , .\o0$trdy (\bus_outs2$trdy )
    , .\o1$irdy (\bus_outs3$irdy )
    , .\o1$data (\bus_outs3$data )
    , .\o1$trdy (\bus_outs3$trdy )
    , .\sel$data (\sfunchan_0_Switch2$data )
    , .\f0$data (\ofunchan_1_Switch2$data )
    , .\f1$data (\ofunchan_2_Switch2$data )
  );
  
  \SFUN_0$RECEPTION_1_0_0_2_Switch2  \sfun_0_Switch2  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\noCONS$data )
    , .\o0 (\sfunchan_0_Switch2$data )
  );
  
  \OFUN_1$RECEPTION_1_0_0_2_Switch2  \ofun_1_Switch2  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\noCONS$data )
    , .\o0 (\ofunchan_1_Switch2$data )
  );
  
  \OFUN_2$RECEPTION_1_0_0_2_Switch2  \ofun_2_Switch2  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\noCONS$data )
    , .\o0 (\ofunchan_2_Switch2$data )
  );
  
  \CreditCounter_2  \CreditCounter1  (
      .\clk (\clk ), .\rst (\rst ), .\t (\t )
    , .\i$irdy (\creditBack$irdy )
    , .\i$data (\creditBack$data )
    , .\i$trdy (\creditBack$trdy )
    , .\o$irdy (\bus_outs4$irdy )
    , .\o$data (\bus_outs4$data )
    , .\o$trdy (\bus_outs4$trdy )
    , .\PatientSource1$unbound_irdy (\CreditCounter1$PatientSource1$unbound_irdy )
    , .\PatientSource1$unbound_data (\CreditCounter1$PatientSource1$unbound_data )
    , .\PatientSource1$trdy (\CreditCounter1$PatientSource1$trdy )
    , .\Sink1$unbound_trdy (\CreditCounter1$Sink1$unbound_trdy )
    , .\Sink1$irdy (\CreditCounter1$Sink1$irdy )
    , .\Sink1$data (\CreditCounter1$Sink1$data )
  );
  
endmodule


//
// RECEPTION_1_0_0_2 switch functions
//
module \SFUN_0$RECEPTION_1_0_0_2_Switch1 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , output [0:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[1:0] \f$bool$g0  = \i0$data  ;
  wire[1:0] \f$bool$f$arg0$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$arg0$arg0$conj  = \f$bool$f$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$arg0$arg0  = \f$bool$f$arg0$arg0$conj [1:1] ;
  wire[0:0] \f$bool$f$arg0$arg1  = 1'd1 ;
  wire \f$bool$f$arg0  = \f$bool$f$arg0$arg0  == \f$bool$f$arg0$arg1  ;
  wire[1:0] \f$bool$f$arg1$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$arg1$arg0$conj  = \f$bool$f$arg1$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$arg1$arg0  = \f$bool$f$arg1$arg0$conj [0:0] ;
  wire[0:0] \f$bool$f$arg1$arg1  = 1'd0 ;
  wire \f$bool$f$arg1  = \f$bool$f$arg1$arg0  == \f$bool$f$arg1$arg1  ;
  wire \f$bool$f  = \f$bool$f$arg0  && \f$bool$f$arg1  ;
  wire \f$bool  = \f$bool$f  ;
  wire[0:0] \f$true$content  = 1'd0 ;
  wire[0:0] \f$true  = \f$true$content  ;
  wire[1:0] \f$false$bool$g0  = \i0$data  ;
  wire[1:0] \f$false$bool$f$arg0$arg0$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$arg0$arg0$conj  = \f$false$bool$f$arg0$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$arg0$arg0  = \f$false$bool$f$arg0$arg0$arg0$conj [1:1] ;
  wire[0:0] \f$false$bool$f$arg0$arg0$arg1  = 1'd1 ;
  wire \f$false$bool$f$arg0$arg0  = \f$false$bool$f$arg0$arg0$arg0  == \f$false$bool$f$arg0$arg0$arg1  ;
  wire[1:0] \f$false$bool$f$arg0$arg1$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$arg1$arg0$conj  = \f$false$bool$f$arg0$arg1$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$arg1$arg0  = \f$false$bool$f$arg0$arg1$arg0$conj [0:0] ;
  wire[0:0] \f$false$bool$f$arg0$arg1$arg1  = 1'd0 ;
  wire \f$false$bool$f$arg0$arg1  = \f$false$bool$f$arg0$arg1$arg0  == \f$false$bool$f$arg0$arg1$arg1  ;
  wire \f$false$bool$f$arg0  = \f$false$bool$f$arg0$arg0  && \f$false$bool$f$arg0$arg1  ;
  wire \f$false$bool$f  = !\f$false$bool$f$arg0  ;
  wire \f$false$bool  = \f$false$bool$f  ;
  wire[0:0] \f$false$true$content  = 1'd1 ;
  wire[0:0] \f$false$true  = \f$false$true$content  ;
  wire[0:0] \f$false$false$content  = 1'd0 ;
  wire[0:0] \f$false$false  = \f$false$false$content  ;
  wire[0:0] \f$false  = ( \f$false$bool  ? \f$false$true  : \f$false$false  ) ;
  wire[0:0] \f  = ( \f$bool  ? \f$true  : \f$false  ) ;
  
  assign \o0  = \f  ;
endmodule

module \OFUN_1$RECEPTION_1_0_0_2_Switch1 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , output [1:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[1:0] \f  = \i0$data  ;
  
  assign \o0  = \f  ;
endmodule

module \OFUN_2$RECEPTION_1_0_0_2_Switch1 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , output [1:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[1:0] \f  = \i0$data  ;
  
  assign \o0  = \f  ;
endmodule

module \SFUN_0$RECEPTION_1_0_0_2_Switch2 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , output [0:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[1:0] \f$bool$g0  = \i0$data  ;
  wire \f$bool$f$bool  = 1'd1 ;
  wire[1:0] \f$bool$f$true$arg0$arg0$arg0$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$true$arg0$arg0$arg0$arg0$conj  = \f$bool$f$true$arg0$arg0$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$true$arg0$arg0$arg0$arg0  = \f$bool$f$true$arg0$arg0$arg0$arg0$conj [1:1] ;
  wire[0:0] \f$bool$f$true$arg0$arg0$arg0$arg1  = 1'd1 ;
  wire \f$bool$f$true$arg0$arg0$arg0  = \f$bool$f$true$arg0$arg0$arg0$arg0  == \f$bool$f$true$arg0$arg0$arg0$arg1  ;
  wire \f$bool$f$true$arg0$arg0  = !\f$bool$f$true$arg0$arg0$arg0  ;
  wire[1:0] \f$bool$f$true$arg0$arg1$arg0$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$true$arg0$arg1$arg0$arg0$conj  = \f$bool$f$true$arg0$arg1$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$true$arg0$arg1$arg0$arg0  = \f$bool$f$true$arg0$arg1$arg0$arg0$conj [1:1] ;
  wire[0:0] \f$bool$f$true$arg0$arg1$arg0$arg1  = 1'd1 ;
  wire \f$bool$f$true$arg0$arg1$arg0  = \f$bool$f$true$arg0$arg1$arg0$arg0  > \f$bool$f$true$arg0$arg1$arg0$arg1  ;
  wire \f$bool$f$true$arg0$arg1  = !\f$bool$f$true$arg0$arg1$arg0  ;
  wire \f$bool$f$true$arg0  = \f$bool$f$true$arg0$arg0  && \f$bool$f$true$arg0$arg1  ;
  wire \f$bool$f$true$arg1  = 1'd0 ;
  wire \f$bool$f$true  = \f$bool$f$true$arg0  || \f$bool$f$true$arg1  ;
  wire \f$bool$f$false$bool  = 1'd0 ;
  wire[1:0] \f$bool$f$false$true$arg0$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$false$true$arg0$arg0$conj  = \f$bool$f$false$true$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$false$true$arg0$arg0  = \f$bool$f$false$true$arg0$arg0$conj [1:1] ;
  wire[0:0] \f$bool$f$false$true$arg0$arg1  = 1'd1 ;
  wire \f$bool$f$false$true$arg0  = \f$bool$f$false$true$arg0$arg0  > \f$bool$f$false$true$arg0$arg1  ;
  wire \f$bool$f$false$true$arg1$arg0  = 1'd1 ;
  wire[1:0] \f$bool$f$false$true$arg1$arg1$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$false$true$arg1$arg1$arg0$conj  = \f$bool$f$false$true$arg1$arg1$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$false$true$arg1$arg1$arg0  = \f$bool$f$false$true$arg1$arg1$arg0$conj [1:1] ;
  wire[0:0] \f$bool$f$false$true$arg1$arg1$arg1  = 1'd0 ;
  wire \f$bool$f$false$true$arg1$arg1  = \f$bool$f$false$true$arg1$arg1$arg0  == \f$bool$f$false$true$arg1$arg1$arg1  ;
  wire \f$bool$f$false$true$arg1  = \f$bool$f$false$true$arg1$arg0  && \f$bool$f$false$true$arg1$arg1  ;
  wire \f$bool$f$false$true  = \f$bool$f$false$true$arg0  || \f$bool$f$false$true$arg1  ;
  wire \f$bool$f$false$false$bool  = 1'd0 ;
  wire[1:0] \f$bool$f$false$false$true$arg0$arg0$arg0$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$false$false$true$arg0$arg0$arg0$arg0$conj  = \f$bool$f$false$false$true$arg0$arg0$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$false$false$true$arg0$arg0$arg0$arg0  = \f$bool$f$false$false$true$arg0$arg0$arg0$arg0$conj [0:0] ;
  wire[0:0] \f$bool$f$false$false$true$arg0$arg0$arg0$arg1  = 1'd0 ;
  wire \f$bool$f$false$false$true$arg0$arg0$arg0  = \f$bool$f$false$false$true$arg0$arg0$arg0$arg0  == \f$bool$f$false$false$true$arg0$arg0$arg0$arg1  ;
  wire \f$bool$f$false$false$true$arg0$arg0  = !\f$bool$f$false$false$true$arg0$arg0$arg0  ;
  wire[1:0] \f$bool$f$false$false$true$arg0$arg1$arg0$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$false$false$true$arg0$arg1$arg0$arg0$conj  = \f$bool$f$false$false$true$arg0$arg1$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$false$false$true$arg0$arg1$arg0$arg0  = \f$bool$f$false$false$true$arg0$arg1$arg0$arg0$conj [0:0] ;
  wire[0:0] \f$bool$f$false$false$true$arg0$arg1$arg0$arg1  = 1'd0 ;
  wire \f$bool$f$false$false$true$arg0$arg1$arg0  = \f$bool$f$false$false$true$arg0$arg1$arg0$arg0  > \f$bool$f$false$false$true$arg0$arg1$arg0$arg1  ;
  wire \f$bool$f$false$false$true$arg0$arg1  = !\f$bool$f$false$false$true$arg0$arg1$arg0  ;
  wire \f$bool$f$false$false$true$arg0  = \f$bool$f$false$false$true$arg0$arg0  && \f$bool$f$false$false$true$arg0$arg1  ;
  wire \f$bool$f$false$false$true$arg1$arg0  = 1'd1 ;
  wire[1:0] \f$bool$f$false$false$true$arg1$arg1$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$false$false$true$arg1$arg1$arg0$conj  = \f$bool$f$false$false$true$arg1$arg1$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$false$false$true$arg1$arg1$arg0  = \f$bool$f$false$false$true$arg1$arg1$arg0$conj [0:0] ;
  wire[0:0] \f$bool$f$false$false$true$arg1$arg1$arg1  = 1'd1 ;
  wire \f$bool$f$false$false$true$arg1$arg1  = \f$bool$f$false$false$true$arg1$arg1$arg0  == \f$bool$f$false$false$true$arg1$arg1$arg1  ;
  wire \f$bool$f$false$false$true$arg1  = \f$bool$f$false$false$true$arg1$arg0  && \f$bool$f$false$false$true$arg1$arg1  ;
  wire \f$bool$f$false$false$true  = \f$bool$f$false$false$true$arg0  || \f$bool$f$false$false$true$arg1  ;
  wire[1:0] \f$bool$f$false$false$false$arg0$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$false$false$false$arg0$arg0$conj  = \f$bool$f$false$false$false$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$false$false$false$arg0$arg0  = \f$bool$f$false$false$false$arg0$arg0$conj [0:0] ;
  wire[0:0] \f$bool$f$false$false$false$arg0$arg1  = 1'd0 ;
  wire \f$bool$f$false$false$false$arg0  = \f$bool$f$false$false$false$arg0$arg0  > \f$bool$f$false$false$false$arg0$arg1  ;
  wire \f$bool$f$false$false$false$arg1  = 1'd0 ;
  wire \f$bool$f$false$false$false  = \f$bool$f$false$false$false$arg0  || \f$bool$f$false$false$false$arg1  ;
  wire \f$bool$f$false$false  = ( \f$bool$f$false$false$bool  ? \f$bool$f$false$false$true  : \f$bool$f$false$false$false  ) ;
  wire \f$bool$f$false  = ( \f$bool$f$false$bool  ? \f$bool$f$false$true  : \f$bool$f$false$false  ) ;
  wire \f$bool$f  = ( \f$bool$f$bool  ? \f$bool$f$true  : \f$bool$f$false  ) ;
  wire \f$bool  = \f$bool$f  ;
  wire[0:0] \f$true$content  = 1'd0 ;
  wire[0:0] \f$true  = \f$true$content  ;
  wire[1:0] \f$false$bool$g0  = \i0$data  ;
  wire \f$false$bool$f$arg0$bool  = 1'd1 ;
  wire[1:0] \f$false$bool$f$arg0$true$arg0$arg0$arg0$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$true$arg0$arg0$arg0$arg0$conj  = \f$false$bool$f$arg0$true$arg0$arg0$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$true$arg0$arg0$arg0$arg0  = \f$false$bool$f$arg0$true$arg0$arg0$arg0$arg0$conj [1:1] ;
  wire[0:0] \f$false$bool$f$arg0$true$arg0$arg0$arg0$arg1  = 1'd1 ;
  wire \f$false$bool$f$arg0$true$arg0$arg0$arg0  = \f$false$bool$f$arg0$true$arg0$arg0$arg0$arg0  == \f$false$bool$f$arg0$true$arg0$arg0$arg0$arg1  ;
  wire \f$false$bool$f$arg0$true$arg0$arg0  = !\f$false$bool$f$arg0$true$arg0$arg0$arg0  ;
  wire[1:0] \f$false$bool$f$arg0$true$arg0$arg1$arg0$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$true$arg0$arg1$arg0$arg0$conj  = \f$false$bool$f$arg0$true$arg0$arg1$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$true$arg0$arg1$arg0$arg0  = \f$false$bool$f$arg0$true$arg0$arg1$arg0$arg0$conj [1:1] ;
  wire[0:0] \f$false$bool$f$arg0$true$arg0$arg1$arg0$arg1  = 1'd1 ;
  wire \f$false$bool$f$arg0$true$arg0$arg1$arg0  = \f$false$bool$f$arg0$true$arg0$arg1$arg0$arg0  > \f$false$bool$f$arg0$true$arg0$arg1$arg0$arg1  ;
  wire \f$false$bool$f$arg0$true$arg0$arg1  = !\f$false$bool$f$arg0$true$arg0$arg1$arg0  ;
  wire \f$false$bool$f$arg0$true$arg0  = \f$false$bool$f$arg0$true$arg0$arg0  && \f$false$bool$f$arg0$true$arg0$arg1  ;
  wire \f$false$bool$f$arg0$true$arg1  = 1'd0 ;
  wire \f$false$bool$f$arg0$true  = \f$false$bool$f$arg0$true$arg0  || \f$false$bool$f$arg0$true$arg1  ;
  wire \f$false$bool$f$arg0$false$bool  = 1'd0 ;
  wire[1:0] \f$false$bool$f$arg0$false$true$arg0$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$false$true$arg0$arg0$conj  = \f$false$bool$f$arg0$false$true$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$false$true$arg0$arg0  = \f$false$bool$f$arg0$false$true$arg0$arg0$conj [1:1] ;
  wire[0:0] \f$false$bool$f$arg0$false$true$arg0$arg1  = 1'd1 ;
  wire \f$false$bool$f$arg0$false$true$arg0  = \f$false$bool$f$arg0$false$true$arg0$arg0  > \f$false$bool$f$arg0$false$true$arg0$arg1  ;
  wire \f$false$bool$f$arg0$false$true$arg1$arg0  = 1'd1 ;
  wire[1:0] \f$false$bool$f$arg0$false$true$arg1$arg1$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$false$true$arg1$arg1$arg0$conj  = \f$false$bool$f$arg0$false$true$arg1$arg1$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$false$true$arg1$arg1$arg0  = \f$false$bool$f$arg0$false$true$arg1$arg1$arg0$conj [1:1] ;
  wire[0:0] \f$false$bool$f$arg0$false$true$arg1$arg1$arg1  = 1'd0 ;
  wire \f$false$bool$f$arg0$false$true$arg1$arg1  = \f$false$bool$f$arg0$false$true$arg1$arg1$arg0  == \f$false$bool$f$arg0$false$true$arg1$arg1$arg1  ;
  wire \f$false$bool$f$arg0$false$true$arg1  = \f$false$bool$f$arg0$false$true$arg1$arg0  && \f$false$bool$f$arg0$false$true$arg1$arg1  ;
  wire \f$false$bool$f$arg0$false$true  = \f$false$bool$f$arg0$false$true$arg0  || \f$false$bool$f$arg0$false$true$arg1  ;
  wire \f$false$bool$f$arg0$false$false$bool  = 1'd0 ;
  wire[1:0] \f$false$bool$f$arg0$false$false$true$arg0$arg0$arg0$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$false$false$true$arg0$arg0$arg0$arg0$conj  = \f$false$bool$f$arg0$false$false$true$arg0$arg0$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$false$false$true$arg0$arg0$arg0$arg0  = \f$false$bool$f$arg0$false$false$true$arg0$arg0$arg0$arg0$conj [0:0] ;
  wire[0:0] \f$false$bool$f$arg0$false$false$true$arg0$arg0$arg0$arg1  = 1'd0 ;
  wire \f$false$bool$f$arg0$false$false$true$arg0$arg0$arg0  = \f$false$bool$f$arg0$false$false$true$arg0$arg0$arg0$arg0  == \f$false$bool$f$arg0$false$false$true$arg0$arg0$arg0$arg1  ;
  wire \f$false$bool$f$arg0$false$false$true$arg0$arg0  = !\f$false$bool$f$arg0$false$false$true$arg0$arg0$arg0  ;
  wire[1:0] \f$false$bool$f$arg0$false$false$true$arg0$arg1$arg0$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$false$false$true$arg0$arg1$arg0$arg0$conj  = \f$false$bool$f$arg0$false$false$true$arg0$arg1$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$false$false$true$arg0$arg1$arg0$arg0  = \f$false$bool$f$arg0$false$false$true$arg0$arg1$arg0$arg0$conj [0:0] ;
  wire[0:0] \f$false$bool$f$arg0$false$false$true$arg0$arg1$arg0$arg1  = 1'd0 ;
  wire \f$false$bool$f$arg0$false$false$true$arg0$arg1$arg0  = \f$false$bool$f$arg0$false$false$true$arg0$arg1$arg0$arg0  > \f$false$bool$f$arg0$false$false$true$arg0$arg1$arg0$arg1  ;
  wire \f$false$bool$f$arg0$false$false$true$arg0$arg1  = !\f$false$bool$f$arg0$false$false$true$arg0$arg1$arg0  ;
  wire \f$false$bool$f$arg0$false$false$true$arg0  = \f$false$bool$f$arg0$false$false$true$arg0$arg0  && \f$false$bool$f$arg0$false$false$true$arg0$arg1  ;
  wire \f$false$bool$f$arg0$false$false$true$arg1$arg0  = 1'd1 ;
  wire[1:0] \f$false$bool$f$arg0$false$false$true$arg1$arg1$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$false$false$true$arg1$arg1$arg0$conj  = \f$false$bool$f$arg0$false$false$true$arg1$arg1$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$false$false$true$arg1$arg1$arg0  = \f$false$bool$f$arg0$false$false$true$arg1$arg1$arg0$conj [0:0] ;
  wire[0:0] \f$false$bool$f$arg0$false$false$true$arg1$arg1$arg1  = 1'd1 ;
  wire \f$false$bool$f$arg0$false$false$true$arg1$arg1  = \f$false$bool$f$arg0$false$false$true$arg1$arg1$arg0  == \f$false$bool$f$arg0$false$false$true$arg1$arg1$arg1  ;
  wire \f$false$bool$f$arg0$false$false$true$arg1  = \f$false$bool$f$arg0$false$false$true$arg1$arg0  && \f$false$bool$f$arg0$false$false$true$arg1$arg1  ;
  wire \f$false$bool$f$arg0$false$false$true  = \f$false$bool$f$arg0$false$false$true$arg0  || \f$false$bool$f$arg0$false$false$true$arg1  ;
  wire[1:0] \f$false$bool$f$arg0$false$false$false$arg0$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$false$false$false$arg0$arg0$conj  = \f$false$bool$f$arg0$false$false$false$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$false$false$false$arg0$arg0  = \f$false$bool$f$arg0$false$false$false$arg0$arg0$conj [0:0] ;
  wire[0:0] \f$false$bool$f$arg0$false$false$false$arg0$arg1  = 1'd0 ;
  wire \f$false$bool$f$arg0$false$false$false$arg0  = \f$false$bool$f$arg0$false$false$false$arg0$arg0  > \f$false$bool$f$arg0$false$false$false$arg0$arg1  ;
  wire \f$false$bool$f$arg0$false$false$false$arg1  = 1'd0 ;
  wire \f$false$bool$f$arg0$false$false$false  = \f$false$bool$f$arg0$false$false$false$arg0  || \f$false$bool$f$arg0$false$false$false$arg1  ;
  wire \f$false$bool$f$arg0$false$false  = ( \f$false$bool$f$arg0$false$false$bool  ? \f$false$bool$f$arg0$false$false$true  : \f$false$bool$f$arg0$false$false$false  ) ;
  wire \f$false$bool$f$arg0$false  = ( \f$false$bool$f$arg0$false$bool  ? \f$false$bool$f$arg0$false$true  : \f$false$bool$f$arg0$false$false  ) ;
  wire \f$false$bool$f$arg0  = ( \f$false$bool$f$arg0$bool  ? \f$false$bool$f$arg0$true  : \f$false$bool$f$arg0$false  ) ;
  wire \f$false$bool$f  = !\f$false$bool$f$arg0  ;
  wire \f$false$bool  = \f$false$bool$f  ;
  wire[0:0] \f$false$true$content  = 1'd1 ;
  wire[0:0] \f$false$true  = \f$false$true$content  ;
  wire[0:0] \f$false$false$content  = 1'd0 ;
  wire[0:0] \f$false$false  = \f$false$false$content  ;
  wire[0:0] \f$false  = ( \f$false$bool  ? \f$false$true  : \f$false$false  ) ;
  wire[0:0] \f  = ( \f$bool  ? \f$true  : \f$false  ) ;
  
  assign \o0  = \f  ;
endmodule

module \OFUN_1$RECEPTION_1_0_0_2_Switch2 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , output [1:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[1:0] \f  = \i0$data  ;
  
  assign \o0  = \f  ;
endmodule

module \OFUN_2$RECEPTION_1_0_0_2_Switch2 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , output [1:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[1:0] \f  = \i0$data  ;
  
  assign \o0  = \f  ;
endmodule

module \RECEPTION_1_0_1_2 (
      input \clk , input \rst , input [63:0] \t 
    , input \input$irdy , input [1:0] \input$data , output \input$trdy 
    , output \bus_outs1$irdy , output [1:0] \bus_outs1$data , input \bus_outs1$trdy 
    , output \bus_outs2$irdy , output [1:0] \bus_outs2$data , input \bus_outs2$trdy 
    , output \bus_outs3$irdy , output [1:0] \bus_outs3$data , input \bus_outs3$trdy 
    , output \bus_outs4$irdy , output [0:0] \bus_outs4$data , input \bus_outs4$trdy 
    , input \CreditCounter1$PatientSource1$unbound_irdy 
    , input [0:0] \CreditCounter1$PatientSource1$unbound_data 
    , output \CreditCounter1$PatientSource1$trdy 
    , input \CreditCounter1$Sink1$unbound_trdy 
    , output \CreditCounter1$Sink1$irdy 
    , output [0:0] \CreditCounter1$Sink1$data 
  );
  
  //
  // Channel declarations
  //
  wire \noCONS$irdy  ;
  wire [1:0] \noCONS$data  ;
  wire \noCONS$trdy  ;
  wire \toRCP$irdy  ;
  wire [1:0] \toRCP$data  ;
  wire \toRCP$trdy  ;
  wire \creditBack$irdy  ;
  wire [1:0] \creditBack$data  ;
  wire \creditBack$trdy  ;
  wire \channel1$irdy  ;
  wire [1:0] \channel1$data  ;
  wire \channel1$trdy  ;
  
  //
  // Function Channels
  //
  wire \sfunchan_0_Switch1$data  ;
  wire [1:0] \ofunchan_1_Switch1$data  ;
  wire [1:0] \ofunchan_2_Switch1$data  ;
  wire \sfunchan_0_Switch2$data  ;
  wire [1:0] \ofunchan_1_Switch2$data  ;
  wire [1:0] \ofunchan_2_Switch2$data  ;
  
  //
  // Component and Macro instantiations
  //
  \Fork2  #(
    .DATASIZE(2)
  ) \Fork1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\channel1$irdy )
    , .\i0$data (\channel1$data )
    , .\i0$trdy (\channel1$trdy )
    , .\o0$irdy (\toRCP$irdy )
    , .\o0$data (\toRCP$data )
    , .\o0$trdy (\toRCP$trdy )
    , .\o1$irdy (\creditBack$irdy )
    , .\o1$data (\creditBack$data )
    , .\o1$trdy (\creditBack$trdy )
  );
  
  \Queue  #(
    .NUM_DATA(0),
    .DATASIZE(2),
    .LENGTH(2)
  ) \Queue1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\input$irdy )
    , .\i0$data (\input$data )
    , .\i0$trdy (\input$trdy )
    , .\o0$irdy (\channel1$irdy )
    , .\o0$data (\channel1$data )
    , .\o0$trdy (\channel1$trdy )
  );
  
  \Switch2  #(
    .OUTPUTSIZE0(2),
    .OUTPUTSIZE1(2),
    .INPUTSIZE(2)
  ) \Switch1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\toRCP$irdy )
    , .\i0$data (\toRCP$data )
    , .\i0$trdy (\toRCP$trdy )
    , .\o0$irdy (\bus_outs1$irdy )
    , .\o0$data (\bus_outs1$data )
    , .\o0$trdy (\bus_outs1$trdy )
    , .\o1$irdy (\noCONS$irdy )
    , .\o1$data (\noCONS$data )
    , .\o1$trdy (\noCONS$trdy )
    , .\sel$data (\sfunchan_0_Switch1$data )
    , .\f0$data (\ofunchan_1_Switch1$data )
    , .\f1$data (\ofunchan_2_Switch1$data )
  );
  
  \SFUN_0$RECEPTION_1_0_1_2_Switch1  \sfun_0_Switch1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\toRCP$data )
    , .\o0 (\sfunchan_0_Switch1$data )
  );
  
  \OFUN_1$RECEPTION_1_0_1_2_Switch1  \ofun_1_Switch1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\toRCP$data )
    , .\o0 (\ofunchan_1_Switch1$data )
  );
  
  \OFUN_2$RECEPTION_1_0_1_2_Switch1  \ofun_2_Switch1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\toRCP$data )
    , .\o0 (\ofunchan_2_Switch1$data )
  );
  
  \Switch2  #(
    .OUTPUTSIZE0(2),
    .OUTPUTSIZE1(2),
    .INPUTSIZE(2)
  ) \Switch2  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\noCONS$irdy )
    , .\i0$data (\noCONS$data )
    , .\i0$trdy (\noCONS$trdy )
    , .\o0$irdy (\bus_outs2$irdy )
    , .\o0$data (\bus_outs2$data )
    , .\o0$trdy (\bus_outs2$trdy )
    , .\o1$irdy (\bus_outs3$irdy )
    , .\o1$data (\bus_outs3$data )
    , .\o1$trdy (\bus_outs3$trdy )
    , .\sel$data (\sfunchan_0_Switch2$data )
    , .\f0$data (\ofunchan_1_Switch2$data )
    , .\f1$data (\ofunchan_2_Switch2$data )
  );
  
  \SFUN_0$RECEPTION_1_0_1_2_Switch2  \sfun_0_Switch2  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\noCONS$data )
    , .\o0 (\sfunchan_0_Switch2$data )
  );
  
  \OFUN_1$RECEPTION_1_0_1_2_Switch2  \ofun_1_Switch2  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\noCONS$data )
    , .\o0 (\ofunchan_1_Switch2$data )
  );
  
  \OFUN_2$RECEPTION_1_0_1_2_Switch2  \ofun_2_Switch2  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\noCONS$data )
    , .\o0 (\ofunchan_2_Switch2$data )
  );
  
  \CreditCounter_2  \CreditCounter1  (
      .\clk (\clk ), .\rst (\rst ), .\t (\t )
    , .\i$irdy (\creditBack$irdy )
    , .\i$data (\creditBack$data )
    , .\i$trdy (\creditBack$trdy )
    , .\o$irdy (\bus_outs4$irdy )
    , .\o$data (\bus_outs4$data )
    , .\o$trdy (\bus_outs4$trdy )
    , .\PatientSource1$unbound_irdy (\CreditCounter1$PatientSource1$unbound_irdy )
    , .\PatientSource1$unbound_data (\CreditCounter1$PatientSource1$unbound_data )
    , .\PatientSource1$trdy (\CreditCounter1$PatientSource1$trdy )
    , .\Sink1$unbound_trdy (\CreditCounter1$Sink1$unbound_trdy )
    , .\Sink1$irdy (\CreditCounter1$Sink1$irdy )
    , .\Sink1$data (\CreditCounter1$Sink1$data )
  );
  
endmodule


//
// RECEPTION_1_0_1_2 switch functions
//
module \SFUN_0$RECEPTION_1_0_1_2_Switch1 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , output [0:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[1:0] \f$bool$g0  = \i0$data  ;
  wire[1:0] \f$bool$f$arg0$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$arg0$arg0$conj  = \f$bool$f$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$arg0$arg0  = \f$bool$f$arg0$arg0$conj [1:1] ;
  wire[0:0] \f$bool$f$arg0$arg1  = 1'd1 ;
  wire \f$bool$f$arg0  = \f$bool$f$arg0$arg0  == \f$bool$f$arg0$arg1  ;
  wire[1:0] \f$bool$f$arg1$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$arg1$arg0$conj  = \f$bool$f$arg1$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$arg1$arg0  = \f$bool$f$arg1$arg0$conj [0:0] ;
  wire[0:0] \f$bool$f$arg1$arg1  = 1'd0 ;
  wire \f$bool$f$arg1  = \f$bool$f$arg1$arg0  == \f$bool$f$arg1$arg1  ;
  wire \f$bool$f  = \f$bool$f$arg0  && \f$bool$f$arg1  ;
  wire \f$bool  = \f$bool$f  ;
  wire[0:0] \f$true$content  = 1'd0 ;
  wire[0:0] \f$true  = \f$true$content  ;
  wire[1:0] \f$false$bool$g0  = \i0$data  ;
  wire[1:0] \f$false$bool$f$arg0$arg0$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$arg0$arg0$conj  = \f$false$bool$f$arg0$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$arg0$arg0  = \f$false$bool$f$arg0$arg0$arg0$conj [1:1] ;
  wire[0:0] \f$false$bool$f$arg0$arg0$arg1  = 1'd1 ;
  wire \f$false$bool$f$arg0$arg0  = \f$false$bool$f$arg0$arg0$arg0  == \f$false$bool$f$arg0$arg0$arg1  ;
  wire[1:0] \f$false$bool$f$arg0$arg1$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$arg1$arg0$conj  = \f$false$bool$f$arg0$arg1$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$arg1$arg0  = \f$false$bool$f$arg0$arg1$arg0$conj [0:0] ;
  wire[0:0] \f$false$bool$f$arg0$arg1$arg1  = 1'd0 ;
  wire \f$false$bool$f$arg0$arg1  = \f$false$bool$f$arg0$arg1$arg0  == \f$false$bool$f$arg0$arg1$arg1  ;
  wire \f$false$bool$f$arg0  = \f$false$bool$f$arg0$arg0  && \f$false$bool$f$arg0$arg1  ;
  wire \f$false$bool$f  = !\f$false$bool$f$arg0  ;
  wire \f$false$bool  = \f$false$bool$f  ;
  wire[0:0] \f$false$true$content  = 1'd1 ;
  wire[0:0] \f$false$true  = \f$false$true$content  ;
  wire[0:0] \f$false$false$content  = 1'd0 ;
  wire[0:0] \f$false$false  = \f$false$false$content  ;
  wire[0:0] \f$false  = ( \f$false$bool  ? \f$false$true  : \f$false$false  ) ;
  wire[0:0] \f  = ( \f$bool  ? \f$true  : \f$false  ) ;
  
  assign \o0  = \f  ;
endmodule

module \OFUN_1$RECEPTION_1_0_1_2_Switch1 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , output [1:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[1:0] \f  = \i0$data  ;
  
  assign \o0  = \f  ;
endmodule

module \OFUN_2$RECEPTION_1_0_1_2_Switch1 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , output [1:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[1:0] \f  = \i0$data  ;
  
  assign \o0  = \f  ;
endmodule

module \SFUN_0$RECEPTION_1_0_1_2_Switch2 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , output [0:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[1:0] \f$bool$g0  = \i0$data  ;
  wire \f$bool$f$bool  = 1'd0 ;
  wire[1:0] \f$bool$f$true$arg0$arg0$arg0$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$true$arg0$arg0$arg0$arg0$conj  = \f$bool$f$true$arg0$arg0$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$true$arg0$arg0$arg0$arg0  = \f$bool$f$true$arg0$arg0$arg0$arg0$conj [1:1] ;
  wire[0:0] \f$bool$f$true$arg0$arg0$arg0$arg1  = 1'd1 ;
  wire \f$bool$f$true$arg0$arg0$arg0  = \f$bool$f$true$arg0$arg0$arg0$arg0  == \f$bool$f$true$arg0$arg0$arg0$arg1  ;
  wire \f$bool$f$true$arg0$arg0  = !\f$bool$f$true$arg0$arg0$arg0  ;
  wire[1:0] \f$bool$f$true$arg0$arg1$arg0$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$true$arg0$arg1$arg0$arg0$conj  = \f$bool$f$true$arg0$arg1$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$true$arg0$arg1$arg0$arg0  = \f$bool$f$true$arg0$arg1$arg0$arg0$conj [1:1] ;
  wire[0:0] \f$bool$f$true$arg0$arg1$arg0$arg1  = 1'd1 ;
  wire \f$bool$f$true$arg0$arg1$arg0  = \f$bool$f$true$arg0$arg1$arg0$arg0  > \f$bool$f$true$arg0$arg1$arg0$arg1  ;
  wire \f$bool$f$true$arg0$arg1  = !\f$bool$f$true$arg0$arg1$arg0  ;
  wire \f$bool$f$true$arg0  = \f$bool$f$true$arg0$arg0  && \f$bool$f$true$arg0$arg1  ;
  wire \f$bool$f$true$arg1  = 1'd0 ;
  wire \f$bool$f$true  = \f$bool$f$true$arg0  || \f$bool$f$true$arg1  ;
  wire \f$bool$f$false$bool  = 1'd1 ;
  wire[1:0] \f$bool$f$false$true$arg0$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$false$true$arg0$arg0$conj  = \f$bool$f$false$true$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$false$true$arg0$arg0  = \f$bool$f$false$true$arg0$arg0$conj [1:1] ;
  wire[0:0] \f$bool$f$false$true$arg0$arg1  = 1'd1 ;
  wire \f$bool$f$false$true$arg0  = \f$bool$f$false$true$arg0$arg0  > \f$bool$f$false$true$arg0$arg1  ;
  wire \f$bool$f$false$true$arg1$arg0  = 1'd1 ;
  wire[1:0] \f$bool$f$false$true$arg1$arg1$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$false$true$arg1$arg1$arg0$conj  = \f$bool$f$false$true$arg1$arg1$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$false$true$arg1$arg1$arg0  = \f$bool$f$false$true$arg1$arg1$arg0$conj [1:1] ;
  wire[0:0] \f$bool$f$false$true$arg1$arg1$arg1  = 1'd0 ;
  wire \f$bool$f$false$true$arg1$arg1  = \f$bool$f$false$true$arg1$arg1$arg0  == \f$bool$f$false$true$arg1$arg1$arg1  ;
  wire \f$bool$f$false$true$arg1  = \f$bool$f$false$true$arg1$arg0  && \f$bool$f$false$true$arg1$arg1  ;
  wire \f$bool$f$false$true  = \f$bool$f$false$true$arg0  || \f$bool$f$false$true$arg1  ;
  wire \f$bool$f$false$false$bool  = 1'd0 ;
  wire[1:0] \f$bool$f$false$false$true$arg0$arg0$arg0$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$false$false$true$arg0$arg0$arg0$arg0$conj  = \f$bool$f$false$false$true$arg0$arg0$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$false$false$true$arg0$arg0$arg0$arg0  = \f$bool$f$false$false$true$arg0$arg0$arg0$arg0$conj [0:0] ;
  wire[0:0] \f$bool$f$false$false$true$arg0$arg0$arg0$arg1  = 1'd0 ;
  wire \f$bool$f$false$false$true$arg0$arg0$arg0  = \f$bool$f$false$false$true$arg0$arg0$arg0$arg0  == \f$bool$f$false$false$true$arg0$arg0$arg0$arg1  ;
  wire \f$bool$f$false$false$true$arg0$arg0  = !\f$bool$f$false$false$true$arg0$arg0$arg0  ;
  wire[1:0] \f$bool$f$false$false$true$arg0$arg1$arg0$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$false$false$true$arg0$arg1$arg0$arg0$conj  = \f$bool$f$false$false$true$arg0$arg1$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$false$false$true$arg0$arg1$arg0$arg0  = \f$bool$f$false$false$true$arg0$arg1$arg0$arg0$conj [0:0] ;
  wire[0:0] \f$bool$f$false$false$true$arg0$arg1$arg0$arg1  = 1'd0 ;
  wire \f$bool$f$false$false$true$arg0$arg1$arg0  = \f$bool$f$false$false$true$arg0$arg1$arg0$arg0  > \f$bool$f$false$false$true$arg0$arg1$arg0$arg1  ;
  wire \f$bool$f$false$false$true$arg0$arg1  = !\f$bool$f$false$false$true$arg0$arg1$arg0  ;
  wire \f$bool$f$false$false$true$arg0  = \f$bool$f$false$false$true$arg0$arg0  && \f$bool$f$false$false$true$arg0$arg1  ;
  wire \f$bool$f$false$false$true$arg1$arg0  = 1'd1 ;
  wire[1:0] \f$bool$f$false$false$true$arg1$arg1$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$false$false$true$arg1$arg1$arg0$conj  = \f$bool$f$false$false$true$arg1$arg1$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$false$false$true$arg1$arg1$arg0  = \f$bool$f$false$false$true$arg1$arg1$arg0$conj [0:0] ;
  wire[0:0] \f$bool$f$false$false$true$arg1$arg1$arg1  = 1'd1 ;
  wire \f$bool$f$false$false$true$arg1$arg1  = \f$bool$f$false$false$true$arg1$arg1$arg0  == \f$bool$f$false$false$true$arg1$arg1$arg1  ;
  wire \f$bool$f$false$false$true$arg1  = \f$bool$f$false$false$true$arg1$arg0  && \f$bool$f$false$false$true$arg1$arg1  ;
  wire \f$bool$f$false$false$true  = \f$bool$f$false$false$true$arg0  || \f$bool$f$false$false$true$arg1  ;
  wire[1:0] \f$bool$f$false$false$false$arg0$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$false$false$false$arg0$arg0$conj  = \f$bool$f$false$false$false$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$false$false$false$arg0$arg0  = \f$bool$f$false$false$false$arg0$arg0$conj [0:0] ;
  wire[0:0] \f$bool$f$false$false$false$arg0$arg1  = 1'd0 ;
  wire \f$bool$f$false$false$false$arg0  = \f$bool$f$false$false$false$arg0$arg0  > \f$bool$f$false$false$false$arg0$arg1  ;
  wire \f$bool$f$false$false$false$arg1  = 1'd0 ;
  wire \f$bool$f$false$false$false  = \f$bool$f$false$false$false$arg0  || \f$bool$f$false$false$false$arg1  ;
  wire \f$bool$f$false$false  = ( \f$bool$f$false$false$bool  ? \f$bool$f$false$false$true  : \f$bool$f$false$false$false  ) ;
  wire \f$bool$f$false  = ( \f$bool$f$false$bool  ? \f$bool$f$false$true  : \f$bool$f$false$false  ) ;
  wire \f$bool$f  = ( \f$bool$f$bool  ? \f$bool$f$true  : \f$bool$f$false  ) ;
  wire \f$bool  = \f$bool$f  ;
  wire[0:0] \f$true$content  = 1'd0 ;
  wire[0:0] \f$true  = \f$true$content  ;
  wire[1:0] \f$false$bool$g0  = \i0$data  ;
  wire \f$false$bool$f$arg0$bool  = 1'd0 ;
  wire[1:0] \f$false$bool$f$arg0$true$arg0$arg0$arg0$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$true$arg0$arg0$arg0$arg0$conj  = \f$false$bool$f$arg0$true$arg0$arg0$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$true$arg0$arg0$arg0$arg0  = \f$false$bool$f$arg0$true$arg0$arg0$arg0$arg0$conj [1:1] ;
  wire[0:0] \f$false$bool$f$arg0$true$arg0$arg0$arg0$arg1  = 1'd1 ;
  wire \f$false$bool$f$arg0$true$arg0$arg0$arg0  = \f$false$bool$f$arg0$true$arg0$arg0$arg0$arg0  == \f$false$bool$f$arg0$true$arg0$arg0$arg0$arg1  ;
  wire \f$false$bool$f$arg0$true$arg0$arg0  = !\f$false$bool$f$arg0$true$arg0$arg0$arg0  ;
  wire[1:0] \f$false$bool$f$arg0$true$arg0$arg1$arg0$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$true$arg0$arg1$arg0$arg0$conj  = \f$false$bool$f$arg0$true$arg0$arg1$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$true$arg0$arg1$arg0$arg0  = \f$false$bool$f$arg0$true$arg0$arg1$arg0$arg0$conj [1:1] ;
  wire[0:0] \f$false$bool$f$arg0$true$arg0$arg1$arg0$arg1  = 1'd1 ;
  wire \f$false$bool$f$arg0$true$arg0$arg1$arg0  = \f$false$bool$f$arg0$true$arg0$arg1$arg0$arg0  > \f$false$bool$f$arg0$true$arg0$arg1$arg0$arg1  ;
  wire \f$false$bool$f$arg0$true$arg0$arg1  = !\f$false$bool$f$arg0$true$arg0$arg1$arg0  ;
  wire \f$false$bool$f$arg0$true$arg0  = \f$false$bool$f$arg0$true$arg0$arg0  && \f$false$bool$f$arg0$true$arg0$arg1  ;
  wire \f$false$bool$f$arg0$true$arg1  = 1'd0 ;
  wire \f$false$bool$f$arg0$true  = \f$false$bool$f$arg0$true$arg0  || \f$false$bool$f$arg0$true$arg1  ;
  wire \f$false$bool$f$arg0$false$bool  = 1'd1 ;
  wire[1:0] \f$false$bool$f$arg0$false$true$arg0$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$false$true$arg0$arg0$conj  = \f$false$bool$f$arg0$false$true$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$false$true$arg0$arg0  = \f$false$bool$f$arg0$false$true$arg0$arg0$conj [1:1] ;
  wire[0:0] \f$false$bool$f$arg0$false$true$arg0$arg1  = 1'd1 ;
  wire \f$false$bool$f$arg0$false$true$arg0  = \f$false$bool$f$arg0$false$true$arg0$arg0  > \f$false$bool$f$arg0$false$true$arg0$arg1  ;
  wire \f$false$bool$f$arg0$false$true$arg1$arg0  = 1'd1 ;
  wire[1:0] \f$false$bool$f$arg0$false$true$arg1$arg1$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$false$true$arg1$arg1$arg0$conj  = \f$false$bool$f$arg0$false$true$arg1$arg1$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$false$true$arg1$arg1$arg0  = \f$false$bool$f$arg0$false$true$arg1$arg1$arg0$conj [1:1] ;
  wire[0:0] \f$false$bool$f$arg0$false$true$arg1$arg1$arg1  = 1'd0 ;
  wire \f$false$bool$f$arg0$false$true$arg1$arg1  = \f$false$bool$f$arg0$false$true$arg1$arg1$arg0  == \f$false$bool$f$arg0$false$true$arg1$arg1$arg1  ;
  wire \f$false$bool$f$arg0$false$true$arg1  = \f$false$bool$f$arg0$false$true$arg1$arg0  && \f$false$bool$f$arg0$false$true$arg1$arg1  ;
  wire \f$false$bool$f$arg0$false$true  = \f$false$bool$f$arg0$false$true$arg0  || \f$false$bool$f$arg0$false$true$arg1  ;
  wire \f$false$bool$f$arg0$false$false$bool  = 1'd0 ;
  wire[1:0] \f$false$bool$f$arg0$false$false$true$arg0$arg0$arg0$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$false$false$true$arg0$arg0$arg0$arg0$conj  = \f$false$bool$f$arg0$false$false$true$arg0$arg0$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$false$false$true$arg0$arg0$arg0$arg0  = \f$false$bool$f$arg0$false$false$true$arg0$arg0$arg0$arg0$conj [0:0] ;
  wire[0:0] \f$false$bool$f$arg0$false$false$true$arg0$arg0$arg0$arg1  = 1'd0 ;
  wire \f$false$bool$f$arg0$false$false$true$arg0$arg0$arg0  = \f$false$bool$f$arg0$false$false$true$arg0$arg0$arg0$arg0  == \f$false$bool$f$arg0$false$false$true$arg0$arg0$arg0$arg1  ;
  wire \f$false$bool$f$arg0$false$false$true$arg0$arg0  = !\f$false$bool$f$arg0$false$false$true$arg0$arg0$arg0  ;
  wire[1:0] \f$false$bool$f$arg0$false$false$true$arg0$arg1$arg0$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$false$false$true$arg0$arg1$arg0$arg0$conj  = \f$false$bool$f$arg0$false$false$true$arg0$arg1$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$false$false$true$arg0$arg1$arg0$arg0  = \f$false$bool$f$arg0$false$false$true$arg0$arg1$arg0$arg0$conj [0:0] ;
  wire[0:0] \f$false$bool$f$arg0$false$false$true$arg0$arg1$arg0$arg1  = 1'd0 ;
  wire \f$false$bool$f$arg0$false$false$true$arg0$arg1$arg0  = \f$false$bool$f$arg0$false$false$true$arg0$arg1$arg0$arg0  > \f$false$bool$f$arg0$false$false$true$arg0$arg1$arg0$arg1  ;
  wire \f$false$bool$f$arg0$false$false$true$arg0$arg1  = !\f$false$bool$f$arg0$false$false$true$arg0$arg1$arg0  ;
  wire \f$false$bool$f$arg0$false$false$true$arg0  = \f$false$bool$f$arg0$false$false$true$arg0$arg0  && \f$false$bool$f$arg0$false$false$true$arg0$arg1  ;
  wire \f$false$bool$f$arg0$false$false$true$arg1$arg0  = 1'd1 ;
  wire[1:0] \f$false$bool$f$arg0$false$false$true$arg1$arg1$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$false$false$true$arg1$arg1$arg0$conj  = \f$false$bool$f$arg0$false$false$true$arg1$arg1$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$false$false$true$arg1$arg1$arg0  = \f$false$bool$f$arg0$false$false$true$arg1$arg1$arg0$conj [0:0] ;
  wire[0:0] \f$false$bool$f$arg0$false$false$true$arg1$arg1$arg1  = 1'd1 ;
  wire \f$false$bool$f$arg0$false$false$true$arg1$arg1  = \f$false$bool$f$arg0$false$false$true$arg1$arg1$arg0  == \f$false$bool$f$arg0$false$false$true$arg1$arg1$arg1  ;
  wire \f$false$bool$f$arg0$false$false$true$arg1  = \f$false$bool$f$arg0$false$false$true$arg1$arg0  && \f$false$bool$f$arg0$false$false$true$arg1$arg1  ;
  wire \f$false$bool$f$arg0$false$false$true  = \f$false$bool$f$arg0$false$false$true$arg0  || \f$false$bool$f$arg0$false$false$true$arg1  ;
  wire[1:0] \f$false$bool$f$arg0$false$false$false$arg0$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$false$false$false$arg0$arg0$conj  = \f$false$bool$f$arg0$false$false$false$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$false$false$false$arg0$arg0  = \f$false$bool$f$arg0$false$false$false$arg0$arg0$conj [0:0] ;
  wire[0:0] \f$false$bool$f$arg0$false$false$false$arg0$arg1  = 1'd0 ;
  wire \f$false$bool$f$arg0$false$false$false$arg0  = \f$false$bool$f$arg0$false$false$false$arg0$arg0  > \f$false$bool$f$arg0$false$false$false$arg0$arg1  ;
  wire \f$false$bool$f$arg0$false$false$false$arg1  = 1'd0 ;
  wire \f$false$bool$f$arg0$false$false$false  = \f$false$bool$f$arg0$false$false$false$arg0  || \f$false$bool$f$arg0$false$false$false$arg1  ;
  wire \f$false$bool$f$arg0$false$false  = ( \f$false$bool$f$arg0$false$false$bool  ? \f$false$bool$f$arg0$false$false$true  : \f$false$bool$f$arg0$false$false$false  ) ;
  wire \f$false$bool$f$arg0$false  = ( \f$false$bool$f$arg0$false$bool  ? \f$false$bool$f$arg0$false$true  : \f$false$bool$f$arg0$false$false  ) ;
  wire \f$false$bool$f$arg0  = ( \f$false$bool$f$arg0$bool  ? \f$false$bool$f$arg0$true  : \f$false$bool$f$arg0$false  ) ;
  wire \f$false$bool$f  = !\f$false$bool$f$arg0  ;
  wire \f$false$bool  = \f$false$bool$f  ;
  wire[0:0] \f$false$true$content  = 1'd1 ;
  wire[0:0] \f$false$true  = \f$false$true$content  ;
  wire[0:0] \f$false$false$content  = 1'd0 ;
  wire[0:0] \f$false$false  = \f$false$false$content  ;
  wire[0:0] \f$false  = ( \f$false$bool  ? \f$false$true  : \f$false$false  ) ;
  wire[0:0] \f  = ( \f$bool  ? \f$true  : \f$false  ) ;
  
  assign \o0  = \f  ;
endmodule

module \OFUN_1$RECEPTION_1_0_1_2_Switch2 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , output [1:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[1:0] \f  = \i0$data  ;
  
  assign \o0  = \f  ;
endmodule

module \OFUN_2$RECEPTION_1_0_1_2_Switch2 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , output [1:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[1:0] \f  = \i0$data  ;
  
  assign \o0  = \f  ;
endmodule

module \RECEPTION_0_1_2_2 (
      input \clk , input \rst , input [63:0] \t 
    , input \input$irdy , input [1:0] \input$data , output \input$trdy 
    , output \bus_outs1$irdy , output [1:0] \bus_outs1$data , input \bus_outs1$trdy 
    , output \bus_outs2$irdy , output [1:0] \bus_outs2$data , input \bus_outs2$trdy 
    , output \bus_outs3$irdy , output [1:0] \bus_outs3$data , input \bus_outs3$trdy 
    , output \bus_outs4$irdy , output [0:0] \bus_outs4$data , input \bus_outs4$trdy 
    , input \CreditCounter1$PatientSource1$unbound_irdy 
    , input [0:0] \CreditCounter1$PatientSource1$unbound_data 
    , output \CreditCounter1$PatientSource1$trdy 
    , input \CreditCounter1$Sink1$unbound_trdy 
    , output \CreditCounter1$Sink1$irdy 
    , output [0:0] \CreditCounter1$Sink1$data 
  );
  
  //
  // Channel declarations
  //
  wire \noCONS$irdy  ;
  wire [1:0] \noCONS$data  ;
  wire \noCONS$trdy  ;
  wire \toRCP$irdy  ;
  wire [1:0] \toRCP$data  ;
  wire \toRCP$trdy  ;
  wire \creditBack$irdy  ;
  wire [1:0] \creditBack$data  ;
  wire \creditBack$trdy  ;
  wire \channel1$irdy  ;
  wire [1:0] \channel1$data  ;
  wire \channel1$trdy  ;
  
  //
  // Function Channels
  //
  wire \sfunchan_0_Switch1$data  ;
  wire [1:0] \ofunchan_1_Switch1$data  ;
  wire [1:0] \ofunchan_2_Switch1$data  ;
  wire \sfunchan_0_Switch2$data  ;
  wire [1:0] \ofunchan_1_Switch2$data  ;
  wire [1:0] \ofunchan_2_Switch2$data  ;
  
  //
  // Component and Macro instantiations
  //
  \Fork2  #(
    .DATASIZE(2)
  ) \Fork1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\channel1$irdy )
    , .\i0$data (\channel1$data )
    , .\i0$trdy (\channel1$trdy )
    , .\o0$irdy (\toRCP$irdy )
    , .\o0$data (\toRCP$data )
    , .\o0$trdy (\toRCP$trdy )
    , .\o1$irdy (\creditBack$irdy )
    , .\o1$data (\creditBack$data )
    , .\o1$trdy (\creditBack$trdy )
  );
  
  \Queue  #(
    .NUM_DATA(0),
    .DATASIZE(2),
    .LENGTH(2)
  ) \Queue1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\input$irdy )
    , .\i0$data (\input$data )
    , .\i0$trdy (\input$trdy )
    , .\o0$irdy (\channel1$irdy )
    , .\o0$data (\channel1$data )
    , .\o0$trdy (\channel1$trdy )
  );
  
  \Switch2  #(
    .OUTPUTSIZE0(2),
    .OUTPUTSIZE1(2),
    .INPUTSIZE(2)
  ) \Switch1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\toRCP$irdy )
    , .\i0$data (\toRCP$data )
    , .\i0$trdy (\toRCP$trdy )
    , .\o0$irdy (\bus_outs1$irdy )
    , .\o0$data (\bus_outs1$data )
    , .\o0$trdy (\bus_outs1$trdy )
    , .\o1$irdy (\noCONS$irdy )
    , .\o1$data (\noCONS$data )
    , .\o1$trdy (\noCONS$trdy )
    , .\sel$data (\sfunchan_0_Switch1$data )
    , .\f0$data (\ofunchan_1_Switch1$data )
    , .\f1$data (\ofunchan_2_Switch1$data )
  );
  
  \SFUN_0$RECEPTION_0_1_2_2_Switch1  \sfun_0_Switch1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\toRCP$data )
    , .\o0 (\sfunchan_0_Switch1$data )
  );
  
  \OFUN_1$RECEPTION_0_1_2_2_Switch1  \ofun_1_Switch1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\toRCP$data )
    , .\o0 (\ofunchan_1_Switch1$data )
  );
  
  \OFUN_2$RECEPTION_0_1_2_2_Switch1  \ofun_2_Switch1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\toRCP$data )
    , .\o0 (\ofunchan_2_Switch1$data )
  );
  
  \Switch2  #(
    .OUTPUTSIZE0(2),
    .OUTPUTSIZE1(2),
    .INPUTSIZE(2)
  ) \Switch2  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\noCONS$irdy )
    , .\i0$data (\noCONS$data )
    , .\i0$trdy (\noCONS$trdy )
    , .\o0$irdy (\bus_outs2$irdy )
    , .\o0$data (\bus_outs2$data )
    , .\o0$trdy (\bus_outs2$trdy )
    , .\o1$irdy (\bus_outs3$irdy )
    , .\o1$data (\bus_outs3$data )
    , .\o1$trdy (\bus_outs3$trdy )
    , .\sel$data (\sfunchan_0_Switch2$data )
    , .\f0$data (\ofunchan_1_Switch2$data )
    , .\f1$data (\ofunchan_2_Switch2$data )
  );
  
  \SFUN_0$RECEPTION_0_1_2_2_Switch2  \sfun_0_Switch2  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\noCONS$data )
    , .\o0 (\sfunchan_0_Switch2$data )
  );
  
  \OFUN_1$RECEPTION_0_1_2_2_Switch2  \ofun_1_Switch2  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\noCONS$data )
    , .\o0 (\ofunchan_1_Switch2$data )
  );
  
  \OFUN_2$RECEPTION_0_1_2_2_Switch2  \ofun_2_Switch2  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\noCONS$data )
    , .\o0 (\ofunchan_2_Switch2$data )
  );
  
  \CreditCounter_2  \CreditCounter1  (
      .\clk (\clk ), .\rst (\rst ), .\t (\t )
    , .\i$irdy (\creditBack$irdy )
    , .\i$data (\creditBack$data )
    , .\i$trdy (\creditBack$trdy )
    , .\o$irdy (\bus_outs4$irdy )
    , .\o$data (\bus_outs4$data )
    , .\o$trdy (\bus_outs4$trdy )
    , .\PatientSource1$unbound_irdy (\CreditCounter1$PatientSource1$unbound_irdy )
    , .\PatientSource1$unbound_data (\CreditCounter1$PatientSource1$unbound_data )
    , .\PatientSource1$trdy (\CreditCounter1$PatientSource1$trdy )
    , .\Sink1$unbound_trdy (\CreditCounter1$Sink1$unbound_trdy )
    , .\Sink1$irdy (\CreditCounter1$Sink1$irdy )
    , .\Sink1$data (\CreditCounter1$Sink1$data )
  );
  
endmodule


//
// RECEPTION_0_1_2_2 switch functions
//
module \SFUN_0$RECEPTION_0_1_2_2_Switch1 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , output [0:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[1:0] \f$bool$g0  = \i0$data  ;
  wire[1:0] \f$bool$f$arg0$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$arg0$arg0$conj  = \f$bool$f$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$arg0$arg0  = \f$bool$f$arg0$arg0$conj [1:1] ;
  wire[0:0] \f$bool$f$arg0$arg1  = 1'd0 ;
  wire \f$bool$f$arg0  = \f$bool$f$arg0$arg0  == \f$bool$f$arg0$arg1  ;
  wire[1:0] \f$bool$f$arg1$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$arg1$arg0$conj  = \f$bool$f$arg1$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$arg1$arg0  = \f$bool$f$arg1$arg0$conj [0:0] ;
  wire[0:0] \f$bool$f$arg1$arg1  = 1'd1 ;
  wire \f$bool$f$arg1  = \f$bool$f$arg1$arg0  == \f$bool$f$arg1$arg1  ;
  wire \f$bool$f  = \f$bool$f$arg0  && \f$bool$f$arg1  ;
  wire \f$bool  = \f$bool$f  ;
  wire[0:0] \f$true$content  = 1'd0 ;
  wire[0:0] \f$true  = \f$true$content  ;
  wire[1:0] \f$false$bool$g0  = \i0$data  ;
  wire[1:0] \f$false$bool$f$arg0$arg0$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$arg0$arg0$conj  = \f$false$bool$f$arg0$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$arg0$arg0  = \f$false$bool$f$arg0$arg0$arg0$conj [1:1] ;
  wire[0:0] \f$false$bool$f$arg0$arg0$arg1  = 1'd0 ;
  wire \f$false$bool$f$arg0$arg0  = \f$false$bool$f$arg0$arg0$arg0  == \f$false$bool$f$arg0$arg0$arg1  ;
  wire[1:0] \f$false$bool$f$arg0$arg1$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$arg1$arg0$conj  = \f$false$bool$f$arg0$arg1$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$arg1$arg0  = \f$false$bool$f$arg0$arg1$arg0$conj [0:0] ;
  wire[0:0] \f$false$bool$f$arg0$arg1$arg1  = 1'd1 ;
  wire \f$false$bool$f$arg0$arg1  = \f$false$bool$f$arg0$arg1$arg0  == \f$false$bool$f$arg0$arg1$arg1  ;
  wire \f$false$bool$f$arg0  = \f$false$bool$f$arg0$arg0  && \f$false$bool$f$arg0$arg1  ;
  wire \f$false$bool$f  = !\f$false$bool$f$arg0  ;
  wire \f$false$bool  = \f$false$bool$f  ;
  wire[0:0] \f$false$true$content  = 1'd1 ;
  wire[0:0] \f$false$true  = \f$false$true$content  ;
  wire[0:0] \f$false$false$content  = 1'd0 ;
  wire[0:0] \f$false$false  = \f$false$false$content  ;
  wire[0:0] \f$false  = ( \f$false$bool  ? \f$false$true  : \f$false$false  ) ;
  wire[0:0] \f  = ( \f$bool  ? \f$true  : \f$false  ) ;
  
  assign \o0  = \f  ;
endmodule

module \OFUN_1$RECEPTION_0_1_2_2_Switch1 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , output [1:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[1:0] \f  = \i0$data  ;
  
  assign \o0  = \f  ;
endmodule

module \OFUN_2$RECEPTION_0_1_2_2_Switch1 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , output [1:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[1:0] \f  = \i0$data  ;
  
  assign \o0  = \f  ;
endmodule

module \SFUN_0$RECEPTION_0_1_2_2_Switch2 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , output [0:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[1:0] \f$bool$g0  = \i0$data  ;
  wire \f$bool$f$bool  = 1'd0 ;
  wire[1:0] \f$bool$f$true$arg0$arg0$arg0$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$true$arg0$arg0$arg0$arg0$conj  = \f$bool$f$true$arg0$arg0$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$true$arg0$arg0$arg0$arg0  = \f$bool$f$true$arg0$arg0$arg0$arg0$conj [1:1] ;
  wire[0:0] \f$bool$f$true$arg0$arg0$arg0$arg1  = 1'd0 ;
  wire \f$bool$f$true$arg0$arg0$arg0  = \f$bool$f$true$arg0$arg0$arg0$arg0  == \f$bool$f$true$arg0$arg0$arg0$arg1  ;
  wire \f$bool$f$true$arg0$arg0  = !\f$bool$f$true$arg0$arg0$arg0  ;
  wire[1:0] \f$bool$f$true$arg0$arg1$arg0$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$true$arg0$arg1$arg0$arg0$conj  = \f$bool$f$true$arg0$arg1$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$true$arg0$arg1$arg0$arg0  = \f$bool$f$true$arg0$arg1$arg0$arg0$conj [1:1] ;
  wire[0:0] \f$bool$f$true$arg0$arg1$arg0$arg1  = 1'd0 ;
  wire \f$bool$f$true$arg0$arg1$arg0  = \f$bool$f$true$arg0$arg1$arg0$arg0  > \f$bool$f$true$arg0$arg1$arg0$arg1  ;
  wire \f$bool$f$true$arg0$arg1  = !\f$bool$f$true$arg0$arg1$arg0  ;
  wire \f$bool$f$true$arg0  = \f$bool$f$true$arg0$arg0  && \f$bool$f$true$arg0$arg1  ;
  wire \f$bool$f$true$arg1$arg0  = 1'd1 ;
  wire[1:0] \f$bool$f$true$arg1$arg1$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$true$arg1$arg1$arg0$conj  = \f$bool$f$true$arg1$arg1$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$true$arg1$arg1$arg0  = \f$bool$f$true$arg1$arg1$arg0$conj [1:1] ;
  wire[0:0] \f$bool$f$true$arg1$arg1$arg1  = 1'd1 ;
  wire \f$bool$f$true$arg1$arg1  = \f$bool$f$true$arg1$arg1$arg0  == \f$bool$f$true$arg1$arg1$arg1  ;
  wire \f$bool$f$true$arg1  = \f$bool$f$true$arg1$arg0  && \f$bool$f$true$arg1$arg1  ;
  wire \f$bool$f$true  = \f$bool$f$true$arg0  || \f$bool$f$true$arg1  ;
  wire \f$bool$f$false$bool  = 1'd0 ;
  wire[1:0] \f$bool$f$false$true$arg0$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$false$true$arg0$arg0$conj  = \f$bool$f$false$true$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$false$true$arg0$arg0  = \f$bool$f$false$true$arg0$arg0$conj [1:1] ;
  wire[0:0] \f$bool$f$false$true$arg0$arg1  = 1'd0 ;
  wire \f$bool$f$false$true$arg0  = \f$bool$f$false$true$arg0$arg0  > \f$bool$f$false$true$arg0$arg1  ;
  wire \f$bool$f$false$true$arg1  = 1'd0 ;
  wire \f$bool$f$false$true  = \f$bool$f$false$true$arg0  || \f$bool$f$false$true$arg1  ;
  wire \f$bool$f$false$false$bool  = 1'd1 ;
  wire[1:0] \f$bool$f$false$false$true$arg0$arg0$arg0$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$false$false$true$arg0$arg0$arg0$arg0$conj  = \f$bool$f$false$false$true$arg0$arg0$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$false$false$true$arg0$arg0$arg0$arg0  = \f$bool$f$false$false$true$arg0$arg0$arg0$arg0$conj [0:0] ;
  wire[0:0] \f$bool$f$false$false$true$arg0$arg0$arg0$arg1  = 1'd1 ;
  wire \f$bool$f$false$false$true$arg0$arg0$arg0  = \f$bool$f$false$false$true$arg0$arg0$arg0$arg0  == \f$bool$f$false$false$true$arg0$arg0$arg0$arg1  ;
  wire \f$bool$f$false$false$true$arg0$arg0  = !\f$bool$f$false$false$true$arg0$arg0$arg0  ;
  wire[1:0] \f$bool$f$false$false$true$arg0$arg1$arg0$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$false$false$true$arg0$arg1$arg0$arg0$conj  = \f$bool$f$false$false$true$arg0$arg1$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$false$false$true$arg0$arg1$arg0$arg0  = \f$bool$f$false$false$true$arg0$arg1$arg0$arg0$conj [0:0] ;
  wire[0:0] \f$bool$f$false$false$true$arg0$arg1$arg0$arg1  = 1'd1 ;
  wire \f$bool$f$false$false$true$arg0$arg1$arg0  = \f$bool$f$false$false$true$arg0$arg1$arg0$arg0  > \f$bool$f$false$false$true$arg0$arg1$arg0$arg1  ;
  wire \f$bool$f$false$false$true$arg0$arg1  = !\f$bool$f$false$false$true$arg0$arg1$arg0  ;
  wire \f$bool$f$false$false$true$arg0  = \f$bool$f$false$false$true$arg0$arg0  && \f$bool$f$false$false$true$arg0$arg1  ;
  wire \f$bool$f$false$false$true$arg1  = 1'd0 ;
  wire \f$bool$f$false$false$true  = \f$bool$f$false$false$true$arg0  || \f$bool$f$false$false$true$arg1  ;
  wire[1:0] \f$bool$f$false$false$false$arg0$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$false$false$false$arg0$arg0$conj  = \f$bool$f$false$false$false$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$false$false$false$arg0$arg0  = \f$bool$f$false$false$false$arg0$arg0$conj [0:0] ;
  wire[0:0] \f$bool$f$false$false$false$arg0$arg1  = 1'd1 ;
  wire \f$bool$f$false$false$false$arg0  = \f$bool$f$false$false$false$arg0$arg0  > \f$bool$f$false$false$false$arg0$arg1  ;
  wire \f$bool$f$false$false$false$arg1$arg0  = 1'd1 ;
  wire[1:0] \f$bool$f$false$false$false$arg1$arg1$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$false$false$false$arg1$arg1$arg0$conj  = \f$bool$f$false$false$false$arg1$arg1$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$false$false$false$arg1$arg1$arg0  = \f$bool$f$false$false$false$arg1$arg1$arg0$conj [0:0] ;
  wire[0:0] \f$bool$f$false$false$false$arg1$arg1$arg1  = 1'd0 ;
  wire \f$bool$f$false$false$false$arg1$arg1  = \f$bool$f$false$false$false$arg1$arg1$arg0  == \f$bool$f$false$false$false$arg1$arg1$arg1  ;
  wire \f$bool$f$false$false$false$arg1  = \f$bool$f$false$false$false$arg1$arg0  && \f$bool$f$false$false$false$arg1$arg1  ;
  wire \f$bool$f$false$false$false  = \f$bool$f$false$false$false$arg0  || \f$bool$f$false$false$false$arg1  ;
  wire \f$bool$f$false$false  = ( \f$bool$f$false$false$bool  ? \f$bool$f$false$false$true  : \f$bool$f$false$false$false  ) ;
  wire \f$bool$f$false  = ( \f$bool$f$false$bool  ? \f$bool$f$false$true  : \f$bool$f$false$false  ) ;
  wire \f$bool$f  = ( \f$bool$f$bool  ? \f$bool$f$true  : \f$bool$f$false  ) ;
  wire \f$bool  = \f$bool$f  ;
  wire[0:0] \f$true$content  = 1'd0 ;
  wire[0:0] \f$true  = \f$true$content  ;
  wire[1:0] \f$false$bool$g0  = \i0$data  ;
  wire \f$false$bool$f$arg0$bool  = 1'd0 ;
  wire[1:0] \f$false$bool$f$arg0$true$arg0$arg0$arg0$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$true$arg0$arg0$arg0$arg0$conj  = \f$false$bool$f$arg0$true$arg0$arg0$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$true$arg0$arg0$arg0$arg0  = \f$false$bool$f$arg0$true$arg0$arg0$arg0$arg0$conj [1:1] ;
  wire[0:0] \f$false$bool$f$arg0$true$arg0$arg0$arg0$arg1  = 1'd0 ;
  wire \f$false$bool$f$arg0$true$arg0$arg0$arg0  = \f$false$bool$f$arg0$true$arg0$arg0$arg0$arg0  == \f$false$bool$f$arg0$true$arg0$arg0$arg0$arg1  ;
  wire \f$false$bool$f$arg0$true$arg0$arg0  = !\f$false$bool$f$arg0$true$arg0$arg0$arg0  ;
  wire[1:0] \f$false$bool$f$arg0$true$arg0$arg1$arg0$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$true$arg0$arg1$arg0$arg0$conj  = \f$false$bool$f$arg0$true$arg0$arg1$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$true$arg0$arg1$arg0$arg0  = \f$false$bool$f$arg0$true$arg0$arg1$arg0$arg0$conj [1:1] ;
  wire[0:0] \f$false$bool$f$arg0$true$arg0$arg1$arg0$arg1  = 1'd0 ;
  wire \f$false$bool$f$arg0$true$arg0$arg1$arg0  = \f$false$bool$f$arg0$true$arg0$arg1$arg0$arg0  > \f$false$bool$f$arg0$true$arg0$arg1$arg0$arg1  ;
  wire \f$false$bool$f$arg0$true$arg0$arg1  = !\f$false$bool$f$arg0$true$arg0$arg1$arg0  ;
  wire \f$false$bool$f$arg0$true$arg0  = \f$false$bool$f$arg0$true$arg0$arg0  && \f$false$bool$f$arg0$true$arg0$arg1  ;
  wire \f$false$bool$f$arg0$true$arg1$arg0  = 1'd1 ;
  wire[1:0] \f$false$bool$f$arg0$true$arg1$arg1$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$true$arg1$arg1$arg0$conj  = \f$false$bool$f$arg0$true$arg1$arg1$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$true$arg1$arg1$arg0  = \f$false$bool$f$arg0$true$arg1$arg1$arg0$conj [1:1] ;
  wire[0:0] \f$false$bool$f$arg0$true$arg1$arg1$arg1  = 1'd1 ;
  wire \f$false$bool$f$arg0$true$arg1$arg1  = \f$false$bool$f$arg0$true$arg1$arg1$arg0  == \f$false$bool$f$arg0$true$arg1$arg1$arg1  ;
  wire \f$false$bool$f$arg0$true$arg1  = \f$false$bool$f$arg0$true$arg1$arg0  && \f$false$bool$f$arg0$true$arg1$arg1  ;
  wire \f$false$bool$f$arg0$true  = \f$false$bool$f$arg0$true$arg0  || \f$false$bool$f$arg0$true$arg1  ;
  wire \f$false$bool$f$arg0$false$bool  = 1'd0 ;
  wire[1:0] \f$false$bool$f$arg0$false$true$arg0$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$false$true$arg0$arg0$conj  = \f$false$bool$f$arg0$false$true$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$false$true$arg0$arg0  = \f$false$bool$f$arg0$false$true$arg0$arg0$conj [1:1] ;
  wire[0:0] \f$false$bool$f$arg0$false$true$arg0$arg1  = 1'd0 ;
  wire \f$false$bool$f$arg0$false$true$arg0  = \f$false$bool$f$arg0$false$true$arg0$arg0  > \f$false$bool$f$arg0$false$true$arg0$arg1  ;
  wire \f$false$bool$f$arg0$false$true$arg1  = 1'd0 ;
  wire \f$false$bool$f$arg0$false$true  = \f$false$bool$f$arg0$false$true$arg0  || \f$false$bool$f$arg0$false$true$arg1  ;
  wire \f$false$bool$f$arg0$false$false$bool  = 1'd1 ;
  wire[1:0] \f$false$bool$f$arg0$false$false$true$arg0$arg0$arg0$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$false$false$true$arg0$arg0$arg0$arg0$conj  = \f$false$bool$f$arg0$false$false$true$arg0$arg0$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$false$false$true$arg0$arg0$arg0$arg0  = \f$false$bool$f$arg0$false$false$true$arg0$arg0$arg0$arg0$conj [0:0] ;
  wire[0:0] \f$false$bool$f$arg0$false$false$true$arg0$arg0$arg0$arg1  = 1'd1 ;
  wire \f$false$bool$f$arg0$false$false$true$arg0$arg0$arg0  = \f$false$bool$f$arg0$false$false$true$arg0$arg0$arg0$arg0  == \f$false$bool$f$arg0$false$false$true$arg0$arg0$arg0$arg1  ;
  wire \f$false$bool$f$arg0$false$false$true$arg0$arg0  = !\f$false$bool$f$arg0$false$false$true$arg0$arg0$arg0  ;
  wire[1:0] \f$false$bool$f$arg0$false$false$true$arg0$arg1$arg0$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$false$false$true$arg0$arg1$arg0$arg0$conj  = \f$false$bool$f$arg0$false$false$true$arg0$arg1$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$false$false$true$arg0$arg1$arg0$arg0  = \f$false$bool$f$arg0$false$false$true$arg0$arg1$arg0$arg0$conj [0:0] ;
  wire[0:0] \f$false$bool$f$arg0$false$false$true$arg0$arg1$arg0$arg1  = 1'd1 ;
  wire \f$false$bool$f$arg0$false$false$true$arg0$arg1$arg0  = \f$false$bool$f$arg0$false$false$true$arg0$arg1$arg0$arg0  > \f$false$bool$f$arg0$false$false$true$arg0$arg1$arg0$arg1  ;
  wire \f$false$bool$f$arg0$false$false$true$arg0$arg1  = !\f$false$bool$f$arg0$false$false$true$arg0$arg1$arg0  ;
  wire \f$false$bool$f$arg0$false$false$true$arg0  = \f$false$bool$f$arg0$false$false$true$arg0$arg0  && \f$false$bool$f$arg0$false$false$true$arg0$arg1  ;
  wire \f$false$bool$f$arg0$false$false$true$arg1  = 1'd0 ;
  wire \f$false$bool$f$arg0$false$false$true  = \f$false$bool$f$arg0$false$false$true$arg0  || \f$false$bool$f$arg0$false$false$true$arg1  ;
  wire[1:0] \f$false$bool$f$arg0$false$false$false$arg0$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$false$false$false$arg0$arg0$conj  = \f$false$bool$f$arg0$false$false$false$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$false$false$false$arg0$arg0  = \f$false$bool$f$arg0$false$false$false$arg0$arg0$conj [0:0] ;
  wire[0:0] \f$false$bool$f$arg0$false$false$false$arg0$arg1  = 1'd1 ;
  wire \f$false$bool$f$arg0$false$false$false$arg0  = \f$false$bool$f$arg0$false$false$false$arg0$arg0  > \f$false$bool$f$arg0$false$false$false$arg0$arg1  ;
  wire \f$false$bool$f$arg0$false$false$false$arg1$arg0  = 1'd1 ;
  wire[1:0] \f$false$bool$f$arg0$false$false$false$arg1$arg1$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$false$false$false$arg1$arg1$arg0$conj  = \f$false$bool$f$arg0$false$false$false$arg1$arg1$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$false$false$false$arg1$arg1$arg0  = \f$false$bool$f$arg0$false$false$false$arg1$arg1$arg0$conj [0:0] ;
  wire[0:0] \f$false$bool$f$arg0$false$false$false$arg1$arg1$arg1  = 1'd0 ;
  wire \f$false$bool$f$arg0$false$false$false$arg1$arg1  = \f$false$bool$f$arg0$false$false$false$arg1$arg1$arg0  == \f$false$bool$f$arg0$false$false$false$arg1$arg1$arg1  ;
  wire \f$false$bool$f$arg0$false$false$false$arg1  = \f$false$bool$f$arg0$false$false$false$arg1$arg0  && \f$false$bool$f$arg0$false$false$false$arg1$arg1  ;
  wire \f$false$bool$f$arg0$false$false$false  = \f$false$bool$f$arg0$false$false$false$arg0  || \f$false$bool$f$arg0$false$false$false$arg1  ;
  wire \f$false$bool$f$arg0$false$false  = ( \f$false$bool$f$arg0$false$false$bool  ? \f$false$bool$f$arg0$false$false$true  : \f$false$bool$f$arg0$false$false$false  ) ;
  wire \f$false$bool$f$arg0$false  = ( \f$false$bool$f$arg0$false$bool  ? \f$false$bool$f$arg0$false$true  : \f$false$bool$f$arg0$false$false  ) ;
  wire \f$false$bool$f$arg0  = ( \f$false$bool$f$arg0$bool  ? \f$false$bool$f$arg0$true  : \f$false$bool$f$arg0$false  ) ;
  wire \f$false$bool$f  = !\f$false$bool$f$arg0  ;
  wire \f$false$bool  = \f$false$bool$f  ;
  wire[0:0] \f$false$true$content  = 1'd1 ;
  wire[0:0] \f$false$true  = \f$false$true$content  ;
  wire[0:0] \f$false$false$content  = 1'd0 ;
  wire[0:0] \f$false$false  = \f$false$false$content  ;
  wire[0:0] \f$false  = ( \f$false$bool  ? \f$false$true  : \f$false$false  ) ;
  wire[0:0] \f  = ( \f$bool  ? \f$true  : \f$false  ) ;
  
  assign \o0  = \f  ;
endmodule

module \OFUN_1$RECEPTION_0_1_2_2_Switch2 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , output [1:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[1:0] \f  = \i0$data  ;
  
  assign \o0  = \f  ;
endmodule

module \OFUN_2$RECEPTION_0_1_2_2_Switch2 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , output [1:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[1:0] \f  = \i0$data  ;
  
  assign \o0  = \f  ;
endmodule

module \RECEPTION_0_1_3_2 (
      input \clk , input \rst , input [63:0] \t 
    , input \input$irdy , input [1:0] \input$data , output \input$trdy 
    , output \bus_outs1$irdy , output [1:0] \bus_outs1$data , input \bus_outs1$trdy 
    , output \bus_outs2$irdy , output [1:0] \bus_outs2$data , input \bus_outs2$trdy 
    , output \bus_outs3$irdy , output [1:0] \bus_outs3$data , input \bus_outs3$trdy 
    , output \bus_outs4$irdy , output [0:0] \bus_outs4$data , input \bus_outs4$trdy 
    , input \CreditCounter1$PatientSource1$unbound_irdy 
    , input [0:0] \CreditCounter1$PatientSource1$unbound_data 
    , output \CreditCounter1$PatientSource1$trdy 
    , input \CreditCounter1$Sink1$unbound_trdy 
    , output \CreditCounter1$Sink1$irdy 
    , output [0:0] \CreditCounter1$Sink1$data 
  );
  
  //
  // Channel declarations
  //
  wire \noCONS$irdy  ;
  wire [1:0] \noCONS$data  ;
  wire \noCONS$trdy  ;
  wire \toRCP$irdy  ;
  wire [1:0] \toRCP$data  ;
  wire \toRCP$trdy  ;
  wire \creditBack$irdy  ;
  wire [1:0] \creditBack$data  ;
  wire \creditBack$trdy  ;
  wire \channel1$irdy  ;
  wire [1:0] \channel1$data  ;
  wire \channel1$trdy  ;
  
  //
  // Function Channels
  //
  wire \sfunchan_0_Switch1$data  ;
  wire [1:0] \ofunchan_1_Switch1$data  ;
  wire [1:0] \ofunchan_2_Switch1$data  ;
  wire \sfunchan_0_Switch2$data  ;
  wire [1:0] \ofunchan_1_Switch2$data  ;
  wire [1:0] \ofunchan_2_Switch2$data  ;
  
  //
  // Component and Macro instantiations
  //
  \Fork2  #(
    .DATASIZE(2)
  ) \Fork1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\channel1$irdy )
    , .\i0$data (\channel1$data )
    , .\i0$trdy (\channel1$trdy )
    , .\o0$irdy (\toRCP$irdy )
    , .\o0$data (\toRCP$data )
    , .\o0$trdy (\toRCP$trdy )
    , .\o1$irdy (\creditBack$irdy )
    , .\o1$data (\creditBack$data )
    , .\o1$trdy (\creditBack$trdy )
  );
  
  \Queue  #(
    .NUM_DATA(0),
    .DATASIZE(2),
    .LENGTH(2)
  ) \Queue1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\input$irdy )
    , .\i0$data (\input$data )
    , .\i0$trdy (\input$trdy )
    , .\o0$irdy (\channel1$irdy )
    , .\o0$data (\channel1$data )
    , .\o0$trdy (\channel1$trdy )
  );
  
  \Switch2  #(
    .OUTPUTSIZE0(2),
    .OUTPUTSIZE1(2),
    .INPUTSIZE(2)
  ) \Switch1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\toRCP$irdy )
    , .\i0$data (\toRCP$data )
    , .\i0$trdy (\toRCP$trdy )
    , .\o0$irdy (\bus_outs1$irdy )
    , .\o0$data (\bus_outs1$data )
    , .\o0$trdy (\bus_outs1$trdy )
    , .\o1$irdy (\noCONS$irdy )
    , .\o1$data (\noCONS$data )
    , .\o1$trdy (\noCONS$trdy )
    , .\sel$data (\sfunchan_0_Switch1$data )
    , .\f0$data (\ofunchan_1_Switch1$data )
    , .\f1$data (\ofunchan_2_Switch1$data )
  );
  
  \SFUN_0$RECEPTION_0_1_3_2_Switch1  \sfun_0_Switch1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\toRCP$data )
    , .\o0 (\sfunchan_0_Switch1$data )
  );
  
  \OFUN_1$RECEPTION_0_1_3_2_Switch1  \ofun_1_Switch1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\toRCP$data )
    , .\o0 (\ofunchan_1_Switch1$data )
  );
  
  \OFUN_2$RECEPTION_0_1_3_2_Switch1  \ofun_2_Switch1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\toRCP$data )
    , .\o0 (\ofunchan_2_Switch1$data )
  );
  
  \Switch2  #(
    .OUTPUTSIZE0(2),
    .OUTPUTSIZE1(2),
    .INPUTSIZE(2)
  ) \Switch2  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\noCONS$irdy )
    , .\i0$data (\noCONS$data )
    , .\i0$trdy (\noCONS$trdy )
    , .\o0$irdy (\bus_outs2$irdy )
    , .\o0$data (\bus_outs2$data )
    , .\o0$trdy (\bus_outs2$trdy )
    , .\o1$irdy (\bus_outs3$irdy )
    , .\o1$data (\bus_outs3$data )
    , .\o1$trdy (\bus_outs3$trdy )
    , .\sel$data (\sfunchan_0_Switch2$data )
    , .\f0$data (\ofunchan_1_Switch2$data )
    , .\f1$data (\ofunchan_2_Switch2$data )
  );
  
  \SFUN_0$RECEPTION_0_1_3_2_Switch2  \sfun_0_Switch2  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\noCONS$data )
    , .\o0 (\sfunchan_0_Switch2$data )
  );
  
  \OFUN_1$RECEPTION_0_1_3_2_Switch2  \ofun_1_Switch2  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\noCONS$data )
    , .\o0 (\ofunchan_1_Switch2$data )
  );
  
  \OFUN_2$RECEPTION_0_1_3_2_Switch2  \ofun_2_Switch2  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\noCONS$data )
    , .\o0 (\ofunchan_2_Switch2$data )
  );
  
  \CreditCounter_2  \CreditCounter1  (
      .\clk (\clk ), .\rst (\rst ), .\t (\t )
    , .\i$irdy (\creditBack$irdy )
    , .\i$data (\creditBack$data )
    , .\i$trdy (\creditBack$trdy )
    , .\o$irdy (\bus_outs4$irdy )
    , .\o$data (\bus_outs4$data )
    , .\o$trdy (\bus_outs4$trdy )
    , .\PatientSource1$unbound_irdy (\CreditCounter1$PatientSource1$unbound_irdy )
    , .\PatientSource1$unbound_data (\CreditCounter1$PatientSource1$unbound_data )
    , .\PatientSource1$trdy (\CreditCounter1$PatientSource1$trdy )
    , .\Sink1$unbound_trdy (\CreditCounter1$Sink1$unbound_trdy )
    , .\Sink1$irdy (\CreditCounter1$Sink1$irdy )
    , .\Sink1$data (\CreditCounter1$Sink1$data )
  );
  
endmodule


//
// RECEPTION_0_1_3_2 switch functions
//
module \SFUN_0$RECEPTION_0_1_3_2_Switch1 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , output [0:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[1:0] \f$bool$g0  = \i0$data  ;
  wire[1:0] \f$bool$f$arg0$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$arg0$arg0$conj  = \f$bool$f$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$arg0$arg0  = \f$bool$f$arg0$arg0$conj [1:1] ;
  wire[0:0] \f$bool$f$arg0$arg1  = 1'd0 ;
  wire \f$bool$f$arg0  = \f$bool$f$arg0$arg0  == \f$bool$f$arg0$arg1  ;
  wire[1:0] \f$bool$f$arg1$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$arg1$arg0$conj  = \f$bool$f$arg1$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$arg1$arg0  = \f$bool$f$arg1$arg0$conj [0:0] ;
  wire[0:0] \f$bool$f$arg1$arg1  = 1'd1 ;
  wire \f$bool$f$arg1  = \f$bool$f$arg1$arg0  == \f$bool$f$arg1$arg1  ;
  wire \f$bool$f  = \f$bool$f$arg0  && \f$bool$f$arg1  ;
  wire \f$bool  = \f$bool$f  ;
  wire[0:0] \f$true$content  = 1'd0 ;
  wire[0:0] \f$true  = \f$true$content  ;
  wire[1:0] \f$false$bool$g0  = \i0$data  ;
  wire[1:0] \f$false$bool$f$arg0$arg0$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$arg0$arg0$conj  = \f$false$bool$f$arg0$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$arg0$arg0  = \f$false$bool$f$arg0$arg0$arg0$conj [1:1] ;
  wire[0:0] \f$false$bool$f$arg0$arg0$arg1  = 1'd0 ;
  wire \f$false$bool$f$arg0$arg0  = \f$false$bool$f$arg0$arg0$arg0  == \f$false$bool$f$arg0$arg0$arg1  ;
  wire[1:0] \f$false$bool$f$arg0$arg1$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$arg1$arg0$conj  = \f$false$bool$f$arg0$arg1$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$arg1$arg0  = \f$false$bool$f$arg0$arg1$arg0$conj [0:0] ;
  wire[0:0] \f$false$bool$f$arg0$arg1$arg1  = 1'd1 ;
  wire \f$false$bool$f$arg0$arg1  = \f$false$bool$f$arg0$arg1$arg0  == \f$false$bool$f$arg0$arg1$arg1  ;
  wire \f$false$bool$f$arg0  = \f$false$bool$f$arg0$arg0  && \f$false$bool$f$arg0$arg1  ;
  wire \f$false$bool$f  = !\f$false$bool$f$arg0  ;
  wire \f$false$bool  = \f$false$bool$f  ;
  wire[0:0] \f$false$true$content  = 1'd1 ;
  wire[0:0] \f$false$true  = \f$false$true$content  ;
  wire[0:0] \f$false$false$content  = 1'd0 ;
  wire[0:0] \f$false$false  = \f$false$false$content  ;
  wire[0:0] \f$false  = ( \f$false$bool  ? \f$false$true  : \f$false$false  ) ;
  wire[0:0] \f  = ( \f$bool  ? \f$true  : \f$false  ) ;
  
  assign \o0  = \f  ;
endmodule

module \OFUN_1$RECEPTION_0_1_3_2_Switch1 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , output [1:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[1:0] \f  = \i0$data  ;
  
  assign \o0  = \f  ;
endmodule

module \OFUN_2$RECEPTION_0_1_3_2_Switch1 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , output [1:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[1:0] \f  = \i0$data  ;
  
  assign \o0  = \f  ;
endmodule

module \SFUN_0$RECEPTION_0_1_3_2_Switch2 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , output [0:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[1:0] \f$bool$g0  = \i0$data  ;
  wire \f$bool$f$bool  = 1'd0 ;
  wire[1:0] \f$bool$f$true$arg0$arg0$arg0$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$true$arg0$arg0$arg0$arg0$conj  = \f$bool$f$true$arg0$arg0$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$true$arg0$arg0$arg0$arg0  = \f$bool$f$true$arg0$arg0$arg0$arg0$conj [1:1] ;
  wire[0:0] \f$bool$f$true$arg0$arg0$arg0$arg1  = 1'd0 ;
  wire \f$bool$f$true$arg0$arg0$arg0  = \f$bool$f$true$arg0$arg0$arg0$arg0  == \f$bool$f$true$arg0$arg0$arg0$arg1  ;
  wire \f$bool$f$true$arg0$arg0  = !\f$bool$f$true$arg0$arg0$arg0  ;
  wire[1:0] \f$bool$f$true$arg0$arg1$arg0$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$true$arg0$arg1$arg0$arg0$conj  = \f$bool$f$true$arg0$arg1$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$true$arg0$arg1$arg0$arg0  = \f$bool$f$true$arg0$arg1$arg0$arg0$conj [1:1] ;
  wire[0:0] \f$bool$f$true$arg0$arg1$arg0$arg1  = 1'd0 ;
  wire \f$bool$f$true$arg0$arg1$arg0  = \f$bool$f$true$arg0$arg1$arg0$arg0  > \f$bool$f$true$arg0$arg1$arg0$arg1  ;
  wire \f$bool$f$true$arg0$arg1  = !\f$bool$f$true$arg0$arg1$arg0  ;
  wire \f$bool$f$true$arg0  = \f$bool$f$true$arg0$arg0  && \f$bool$f$true$arg0$arg1  ;
  wire \f$bool$f$true$arg1$arg0  = 1'd1 ;
  wire[1:0] \f$bool$f$true$arg1$arg1$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$true$arg1$arg1$arg0$conj  = \f$bool$f$true$arg1$arg1$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$true$arg1$arg1$arg0  = \f$bool$f$true$arg1$arg1$arg0$conj [1:1] ;
  wire[0:0] \f$bool$f$true$arg1$arg1$arg1  = 1'd1 ;
  wire \f$bool$f$true$arg1$arg1  = \f$bool$f$true$arg1$arg1$arg0  == \f$bool$f$true$arg1$arg1$arg1  ;
  wire \f$bool$f$true$arg1  = \f$bool$f$true$arg1$arg0  && \f$bool$f$true$arg1$arg1  ;
  wire \f$bool$f$true  = \f$bool$f$true$arg0  || \f$bool$f$true$arg1  ;
  wire \f$bool$f$false$bool  = 1'd0 ;
  wire[1:0] \f$bool$f$false$true$arg0$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$false$true$arg0$arg0$conj  = \f$bool$f$false$true$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$false$true$arg0$arg0  = \f$bool$f$false$true$arg0$arg0$conj [1:1] ;
  wire[0:0] \f$bool$f$false$true$arg0$arg1  = 1'd0 ;
  wire \f$bool$f$false$true$arg0  = \f$bool$f$false$true$arg0$arg0  > \f$bool$f$false$true$arg0$arg1  ;
  wire \f$bool$f$false$true$arg1  = 1'd0 ;
  wire \f$bool$f$false$true  = \f$bool$f$false$true$arg0  || \f$bool$f$false$true$arg1  ;
  wire \f$bool$f$false$false$bool  = 1'd0 ;
  wire[1:0] \f$bool$f$false$false$true$arg0$arg0$arg0$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$false$false$true$arg0$arg0$arg0$arg0$conj  = \f$bool$f$false$false$true$arg0$arg0$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$false$false$true$arg0$arg0$arg0$arg0  = \f$bool$f$false$false$true$arg0$arg0$arg0$arg0$conj [0:0] ;
  wire[0:0] \f$bool$f$false$false$true$arg0$arg0$arg0$arg1  = 1'd1 ;
  wire \f$bool$f$false$false$true$arg0$arg0$arg0  = \f$bool$f$false$false$true$arg0$arg0$arg0$arg0  == \f$bool$f$false$false$true$arg0$arg0$arg0$arg1  ;
  wire \f$bool$f$false$false$true$arg0$arg0  = !\f$bool$f$false$false$true$arg0$arg0$arg0  ;
  wire[1:0] \f$bool$f$false$false$true$arg0$arg1$arg0$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$false$false$true$arg0$arg1$arg0$arg0$conj  = \f$bool$f$false$false$true$arg0$arg1$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$false$false$true$arg0$arg1$arg0$arg0  = \f$bool$f$false$false$true$arg0$arg1$arg0$arg0$conj [0:0] ;
  wire[0:0] \f$bool$f$false$false$true$arg0$arg1$arg0$arg1  = 1'd1 ;
  wire \f$bool$f$false$false$true$arg0$arg1$arg0  = \f$bool$f$false$false$true$arg0$arg1$arg0$arg0  > \f$bool$f$false$false$true$arg0$arg1$arg0$arg1  ;
  wire \f$bool$f$false$false$true$arg0$arg1  = !\f$bool$f$false$false$true$arg0$arg1$arg0  ;
  wire \f$bool$f$false$false$true$arg0  = \f$bool$f$false$false$true$arg0$arg0  && \f$bool$f$false$false$true$arg0$arg1  ;
  wire \f$bool$f$false$false$true$arg1  = 1'd0 ;
  wire \f$bool$f$false$false$true  = \f$bool$f$false$false$true$arg0  || \f$bool$f$false$false$true$arg1  ;
  wire[1:0] \f$bool$f$false$false$false$arg0$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$false$false$false$arg0$arg0$conj  = \f$bool$f$false$false$false$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$false$false$false$arg0$arg0  = \f$bool$f$false$false$false$arg0$arg0$conj [0:0] ;
  wire[0:0] \f$bool$f$false$false$false$arg0$arg1  = 1'd1 ;
  wire \f$bool$f$false$false$false$arg0  = \f$bool$f$false$false$false$arg0$arg0  > \f$bool$f$false$false$false$arg0$arg1  ;
  wire \f$bool$f$false$false$false$arg1$arg0  = 1'd1 ;
  wire[1:0] \f$bool$f$false$false$false$arg1$arg1$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$false$false$false$arg1$arg1$arg0$conj  = \f$bool$f$false$false$false$arg1$arg1$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$false$false$false$arg1$arg1$arg0  = \f$bool$f$false$false$false$arg1$arg1$arg0$conj [0:0] ;
  wire[0:0] \f$bool$f$false$false$false$arg1$arg1$arg1  = 1'd0 ;
  wire \f$bool$f$false$false$false$arg1$arg1  = \f$bool$f$false$false$false$arg1$arg1$arg0  == \f$bool$f$false$false$false$arg1$arg1$arg1  ;
  wire \f$bool$f$false$false$false$arg1  = \f$bool$f$false$false$false$arg1$arg0  && \f$bool$f$false$false$false$arg1$arg1  ;
  wire \f$bool$f$false$false$false  = \f$bool$f$false$false$false$arg0  || \f$bool$f$false$false$false$arg1  ;
  wire \f$bool$f$false$false  = ( \f$bool$f$false$false$bool  ? \f$bool$f$false$false$true  : \f$bool$f$false$false$false  ) ;
  wire \f$bool$f$false  = ( \f$bool$f$false$bool  ? \f$bool$f$false$true  : \f$bool$f$false$false  ) ;
  wire \f$bool$f  = ( \f$bool$f$bool  ? \f$bool$f$true  : \f$bool$f$false  ) ;
  wire \f$bool  = \f$bool$f  ;
  wire[0:0] \f$true$content  = 1'd0 ;
  wire[0:0] \f$true  = \f$true$content  ;
  wire[1:0] \f$false$bool$g0  = \i0$data  ;
  wire \f$false$bool$f$arg0$bool  = 1'd0 ;
  wire[1:0] \f$false$bool$f$arg0$true$arg0$arg0$arg0$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$true$arg0$arg0$arg0$arg0$conj  = \f$false$bool$f$arg0$true$arg0$arg0$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$true$arg0$arg0$arg0$arg0  = \f$false$bool$f$arg0$true$arg0$arg0$arg0$arg0$conj [1:1] ;
  wire[0:0] \f$false$bool$f$arg0$true$arg0$arg0$arg0$arg1  = 1'd0 ;
  wire \f$false$bool$f$arg0$true$arg0$arg0$arg0  = \f$false$bool$f$arg0$true$arg0$arg0$arg0$arg0  == \f$false$bool$f$arg0$true$arg0$arg0$arg0$arg1  ;
  wire \f$false$bool$f$arg0$true$arg0$arg0  = !\f$false$bool$f$arg0$true$arg0$arg0$arg0  ;
  wire[1:0] \f$false$bool$f$arg0$true$arg0$arg1$arg0$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$true$arg0$arg1$arg0$arg0$conj  = \f$false$bool$f$arg0$true$arg0$arg1$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$true$arg0$arg1$arg0$arg0  = \f$false$bool$f$arg0$true$arg0$arg1$arg0$arg0$conj [1:1] ;
  wire[0:0] \f$false$bool$f$arg0$true$arg0$arg1$arg0$arg1  = 1'd0 ;
  wire \f$false$bool$f$arg0$true$arg0$arg1$arg0  = \f$false$bool$f$arg0$true$arg0$arg1$arg0$arg0  > \f$false$bool$f$arg0$true$arg0$arg1$arg0$arg1  ;
  wire \f$false$bool$f$arg0$true$arg0$arg1  = !\f$false$bool$f$arg0$true$arg0$arg1$arg0  ;
  wire \f$false$bool$f$arg0$true$arg0  = \f$false$bool$f$arg0$true$arg0$arg0  && \f$false$bool$f$arg0$true$arg0$arg1  ;
  wire \f$false$bool$f$arg0$true$arg1$arg0  = 1'd1 ;
  wire[1:0] \f$false$bool$f$arg0$true$arg1$arg1$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$true$arg1$arg1$arg0$conj  = \f$false$bool$f$arg0$true$arg1$arg1$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$true$arg1$arg1$arg0  = \f$false$bool$f$arg0$true$arg1$arg1$arg0$conj [1:1] ;
  wire[0:0] \f$false$bool$f$arg0$true$arg1$arg1$arg1  = 1'd1 ;
  wire \f$false$bool$f$arg0$true$arg1$arg1  = \f$false$bool$f$arg0$true$arg1$arg1$arg0  == \f$false$bool$f$arg0$true$arg1$arg1$arg1  ;
  wire \f$false$bool$f$arg0$true$arg1  = \f$false$bool$f$arg0$true$arg1$arg0  && \f$false$bool$f$arg0$true$arg1$arg1  ;
  wire \f$false$bool$f$arg0$true  = \f$false$bool$f$arg0$true$arg0  || \f$false$bool$f$arg0$true$arg1  ;
  wire \f$false$bool$f$arg0$false$bool  = 1'd0 ;
  wire[1:0] \f$false$bool$f$arg0$false$true$arg0$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$false$true$arg0$arg0$conj  = \f$false$bool$f$arg0$false$true$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$false$true$arg0$arg0  = \f$false$bool$f$arg0$false$true$arg0$arg0$conj [1:1] ;
  wire[0:0] \f$false$bool$f$arg0$false$true$arg0$arg1  = 1'd0 ;
  wire \f$false$bool$f$arg0$false$true$arg0  = \f$false$bool$f$arg0$false$true$arg0$arg0  > \f$false$bool$f$arg0$false$true$arg0$arg1  ;
  wire \f$false$bool$f$arg0$false$true$arg1  = 1'd0 ;
  wire \f$false$bool$f$arg0$false$true  = \f$false$bool$f$arg0$false$true$arg0  || \f$false$bool$f$arg0$false$true$arg1  ;
  wire \f$false$bool$f$arg0$false$false$bool  = 1'd0 ;
  wire[1:0] \f$false$bool$f$arg0$false$false$true$arg0$arg0$arg0$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$false$false$true$arg0$arg0$arg0$arg0$conj  = \f$false$bool$f$arg0$false$false$true$arg0$arg0$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$false$false$true$arg0$arg0$arg0$arg0  = \f$false$bool$f$arg0$false$false$true$arg0$arg0$arg0$arg0$conj [0:0] ;
  wire[0:0] \f$false$bool$f$arg0$false$false$true$arg0$arg0$arg0$arg1  = 1'd1 ;
  wire \f$false$bool$f$arg0$false$false$true$arg0$arg0$arg0  = \f$false$bool$f$arg0$false$false$true$arg0$arg0$arg0$arg0  == \f$false$bool$f$arg0$false$false$true$arg0$arg0$arg0$arg1  ;
  wire \f$false$bool$f$arg0$false$false$true$arg0$arg0  = !\f$false$bool$f$arg0$false$false$true$arg0$arg0$arg0  ;
  wire[1:0] \f$false$bool$f$arg0$false$false$true$arg0$arg1$arg0$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$false$false$true$arg0$arg1$arg0$arg0$conj  = \f$false$bool$f$arg0$false$false$true$arg0$arg1$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$false$false$true$arg0$arg1$arg0$arg0  = \f$false$bool$f$arg0$false$false$true$arg0$arg1$arg0$arg0$conj [0:0] ;
  wire[0:0] \f$false$bool$f$arg0$false$false$true$arg0$arg1$arg0$arg1  = 1'd1 ;
  wire \f$false$bool$f$arg0$false$false$true$arg0$arg1$arg0  = \f$false$bool$f$arg0$false$false$true$arg0$arg1$arg0$arg0  > \f$false$bool$f$arg0$false$false$true$arg0$arg1$arg0$arg1  ;
  wire \f$false$bool$f$arg0$false$false$true$arg0$arg1  = !\f$false$bool$f$arg0$false$false$true$arg0$arg1$arg0  ;
  wire \f$false$bool$f$arg0$false$false$true$arg0  = \f$false$bool$f$arg0$false$false$true$arg0$arg0  && \f$false$bool$f$arg0$false$false$true$arg0$arg1  ;
  wire \f$false$bool$f$arg0$false$false$true$arg1  = 1'd0 ;
  wire \f$false$bool$f$arg0$false$false$true  = \f$false$bool$f$arg0$false$false$true$arg0  || \f$false$bool$f$arg0$false$false$true$arg1  ;
  wire[1:0] \f$false$bool$f$arg0$false$false$false$arg0$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$false$false$false$arg0$arg0$conj  = \f$false$bool$f$arg0$false$false$false$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$false$false$false$arg0$arg0  = \f$false$bool$f$arg0$false$false$false$arg0$arg0$conj [0:0] ;
  wire[0:0] \f$false$bool$f$arg0$false$false$false$arg0$arg1  = 1'd1 ;
  wire \f$false$bool$f$arg0$false$false$false$arg0  = \f$false$bool$f$arg0$false$false$false$arg0$arg0  > \f$false$bool$f$arg0$false$false$false$arg0$arg1  ;
  wire \f$false$bool$f$arg0$false$false$false$arg1$arg0  = 1'd1 ;
  wire[1:0] \f$false$bool$f$arg0$false$false$false$arg1$arg1$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$false$false$false$arg1$arg1$arg0$conj  = \f$false$bool$f$arg0$false$false$false$arg1$arg1$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$false$false$false$arg1$arg1$arg0  = \f$false$bool$f$arg0$false$false$false$arg1$arg1$arg0$conj [0:0] ;
  wire[0:0] \f$false$bool$f$arg0$false$false$false$arg1$arg1$arg1  = 1'd0 ;
  wire \f$false$bool$f$arg0$false$false$false$arg1$arg1  = \f$false$bool$f$arg0$false$false$false$arg1$arg1$arg0  == \f$false$bool$f$arg0$false$false$false$arg1$arg1$arg1  ;
  wire \f$false$bool$f$arg0$false$false$false$arg1  = \f$false$bool$f$arg0$false$false$false$arg1$arg0  && \f$false$bool$f$arg0$false$false$false$arg1$arg1  ;
  wire \f$false$bool$f$arg0$false$false$false  = \f$false$bool$f$arg0$false$false$false$arg0  || \f$false$bool$f$arg0$false$false$false$arg1  ;
  wire \f$false$bool$f$arg0$false$false  = ( \f$false$bool$f$arg0$false$false$bool  ? \f$false$bool$f$arg0$false$false$true  : \f$false$bool$f$arg0$false$false$false  ) ;
  wire \f$false$bool$f$arg0$false  = ( \f$false$bool$f$arg0$false$bool  ? \f$false$bool$f$arg0$false$true  : \f$false$bool$f$arg0$false$false  ) ;
  wire \f$false$bool$f$arg0  = ( \f$false$bool$f$arg0$bool  ? \f$false$bool$f$arg0$true  : \f$false$bool$f$arg0$false  ) ;
  wire \f$false$bool$f  = !\f$false$bool$f$arg0  ;
  wire \f$false$bool  = \f$false$bool$f  ;
  wire[0:0] \f$false$true$content  = 1'd1 ;
  wire[0:0] \f$false$true  = \f$false$true$content  ;
  wire[0:0] \f$false$false$content  = 1'd0 ;
  wire[0:0] \f$false$false  = \f$false$false$content  ;
  wire[0:0] \f$false  = ( \f$false$bool  ? \f$false$true  : \f$false$false  ) ;
  wire[0:0] \f  = ( \f$bool  ? \f$true  : \f$false  ) ;
  
  assign \o0  = \f  ;
endmodule

module \OFUN_1$RECEPTION_0_1_3_2_Switch2 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , output [1:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[1:0] \f  = \i0$data  ;
  
  assign \o0  = \f  ;
endmodule

module \OFUN_2$RECEPTION_0_1_3_2_Switch2 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , output [1:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[1:0] \f  = \i0$data  ;
  
  assign \o0  = \f  ;
endmodule

module \BBB_0_1_2_2_0_2 (
      input \clk , input \rst , input [63:0] \t 
    , input \bus_ins1$irdy , input [1:0] \bus_ins1$data , output \bus_ins1$trdy 
    , input \bus_ins2$irdy , input [1:0] \bus_ins2$data , output \bus_ins2$trdy 
    , input \bus_ins3$irdy , input [1:0] \bus_ins3$data , output \bus_ins3$trdy 
    , input \bus_ins4$irdy , input [0:0] \bus_ins4$data , output \bus_ins4$trdy 
    , output \bus_outs1$irdy , output [1:0] \bus_outs1$data , input \bus_outs1$trdy 
    , output \bus_outs2$irdy , output [1:0] \bus_outs2$data , input \bus_outs2$trdy 
    , output \bus_outs3$irdy , output [1:0] \bus_outs3$data , input \bus_outs3$trdy 
    , output \bus_outs4$irdy , output [0:0] \bus_outs4$data , input \bus_outs4$trdy 
    , input \Sink1$unbound_trdy 
    , output \Sink1$irdy 
    , output [1:0] \Sink1$data 
    , input \RECEPTION1$CreditCounter1$PatientSource1$unbound_irdy 
    , input [0:0] \RECEPTION1$CreditCounter1$PatientSource1$unbound_data 
    , output \RECEPTION1$CreditCounter1$PatientSource1$trdy 
    , input \RECEPTION1$CreditCounter1$Sink1$unbound_trdy 
    , output \RECEPTION1$CreditCounter1$Sink1$irdy 
    , output [0:0] \RECEPTION1$CreditCounter1$Sink1$data 
  );
  
  //
  // Channel declarations
  //
  wire \toEjection$irdy  ;
  wire [1:0] \toEjection$data  ;
  wire \toEjection$trdy  ;
  wire \toDFIFO$irdy  ;
  wire [1:0] \toDFIFO$data  ;
  wire \toDFIFO$trdy  ;
  wire \bypassLine$irdy  ;
  wire [1:0] \bypassLine$data  ;
  wire \bypassLine$trdy  ;
  wire \goodPkts$irdy  ;
  wire [1:0] \goodPkts$data  ;
  wire \goodPkts$trdy  ;
  wire \badPkts$irdy  ;
  wire [1:0] \badPkts$data  ;
  wire \badPkts$trdy  ;
  wire \channel1$irdy  ;
  wire [1:0] \channel1$data  ;
  wire \channel1$trdy  ;
  wire \channel2$irdy  ;
  wire \channel2$data  ;
  wire \channel2$trdy  ;
  
  //
  // Function Channels
  //
  wire \sfunchan_0_Switch1$data  ;
  wire [1:0] \ofunchan_1_Switch1$data  ;
  wire [1:0] \ofunchan_2_Switch1$data  ;
  
  //
  // Component and Macro instantiations
  //
  \Switch2  #(
    .OUTPUTSIZE0(2),
    .OUTPUTSIZE1(2),
    .INPUTSIZE(2)
  ) \Switch1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\bus_ins1$irdy )
    , .\i0$data (\bus_ins1$data )
    , .\i0$trdy (\bus_ins1$trdy )
    , .\o0$irdy (\goodPkts$irdy )
    , .\o0$data (\goodPkts$data )
    , .\o0$trdy (\goodPkts$trdy )
    , .\o1$irdy (\badPkts$irdy )
    , .\o1$data (\badPkts$data )
    , .\o1$trdy (\badPkts$trdy )
    , .\sel$data (\sfunchan_0_Switch1$data )
    , .\f0$data (\ofunchan_1_Switch1$data )
    , .\f1$data (\ofunchan_2_Switch1$data )
  );
  
  \SFUN_0$BBB_0_1_2_2_0_2_Switch1  \sfun_0_Switch1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\bus_ins1$data )
    , .\o0 (\sfunchan_0_Switch1$data )
  );
  
  \OFUN_1$BBB_0_1_2_2_0_2_Switch1  \ofun_1_Switch1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\bus_ins1$data )
    , .\o0 (\ofunchan_1_Switch1$data )
  );
  
  \OFUN_2$BBB_0_1_2_2_0_2_Switch1  \ofun_2_Switch1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\bus_ins1$data )
    , .\o0 (\ofunchan_2_Switch1$data )
  );
  
  assign \Sink1$irdy  = \badPkts$irdy  ;
  assign \Sink1$data  = \badPkts$data  ;
  \Sink  #(
    .DATASIZE(2)
  ) \Sink1  (
      .\clk (\clk ), .\rst (\rst ), .\t (\t )
    , .\i0$irdy (\badPkts$irdy )
    , .\i0$data (\badPkts$data )
    , .\i0$trdy (\badPkts$trdy )
    , .\unbound_trdy (\Sink1$unbound_trdy )
  );
  
  \CTRLJoin2  #(
    .INPUTSIZE1(1),
    .OUTPUTSIZE(2),
    .INPUTSIZE0(2)
  ) \CtrlJoin1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\channel1$irdy )
    , .\i0$data (\channel1$data )
    , .\i0$trdy (\channel1$trdy )
    , .\i1$irdy (\channel2$irdy )
    , .\i1$data (\channel2$data )
    , .\i1$trdy (\channel2$trdy )
    , .\o0$irdy (\bus_outs2$irdy )
    , .\o0$data (\bus_outs2$data )
    , .\o0$trdy (\bus_outs2$trdy )
  );
  
  \Queue  #(
    .NUM_DATA(0),
    .DATASIZE(1),
    .LENGTH(2)
  ) \Queue1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\bus_ins4$irdy )
    , .\i0$data (\bus_ins4$data )
    , .\i0$trdy (\bus_ins4$trdy )
    , .\o0$irdy (\channel2$irdy )
    , .\o0$data (\channel2$data )
    , .\o0$trdy (\channel2$trdy )
  );
  
  \RECEPTION_0_1_0_2  \RECEPTION1  (
      .\clk (\clk ), .\rst (\rst ), .\t (\t )
    , .\input$irdy (\bus_ins2$irdy )
    , .\input$data (\bus_ins2$data )
    , .\input$trdy (\bus_ins2$trdy )
    , .\bus_outs1$irdy (\bus_outs1$irdy )
    , .\bus_outs1$data (\bus_outs1$data )
    , .\bus_outs1$trdy (\bus_outs1$trdy )
    , .\bus_outs2$irdy (\bypassLine$irdy )
    , .\bus_outs2$data (\bypassLine$data )
    , .\bus_outs2$trdy (\bypassLine$trdy )
    , .\bus_outs3$irdy (\toDFIFO$irdy )
    , .\bus_outs3$data (\toDFIFO$data )
    , .\bus_outs3$trdy (\toDFIFO$trdy )
    , .\bus_outs4$irdy (\bus_outs4$irdy )
    , .\bus_outs4$data (\bus_outs4$data )
    , .\bus_outs4$trdy (\bus_outs4$trdy )
    , .\CreditCounter1$PatientSource1$unbound_irdy (\RECEPTION1$CreditCounter1$PatientSource1$unbound_irdy )
    , .\CreditCounter1$PatientSource1$unbound_data (\RECEPTION1$CreditCounter1$PatientSource1$unbound_data )
    , .\CreditCounter1$PatientSource1$trdy (\RECEPTION1$CreditCounter1$PatientSource1$trdy )
    , .\CreditCounter1$Sink1$unbound_trdy (\RECEPTION1$CreditCounter1$Sink1$unbound_trdy )
    , .\CreditCounter1$Sink1$irdy (\RECEPTION1$CreditCounter1$Sink1$irdy )
    , .\CreditCounter1$Sink1$data (\RECEPTION1$CreditCounter1$Sink1$data )
  );
  
  \DFIFO_2$type0  \DFIFO1  (
      .\clk (\clk ), .\rst (\rst )
    , .\bus_ins1$irdy (\toDFIFO$irdy )
    , .\bus_ins1$data (\toDFIFO$data )
    , .\bus_ins1$trdy (\toDFIFO$trdy )
    , .\bus_ins2$irdy (\bus_ins3$irdy )
    , .\bus_ins2$data (\bus_ins3$data )
    , .\bus_ins2$trdy (\bus_ins3$trdy )
    , .\bus_outs1$irdy (\bus_outs3$irdy )
    , .\bus_outs1$data (\bus_outs3$data )
    , .\bus_outs1$trdy (\bus_outs3$trdy )
    , .\bus_outs2$irdy (\toEjection$irdy )
    , .\bus_outs2$data (\toEjection$data )
    , .\bus_outs2$trdy (\toEjection$trdy )
  );
  
  \EJECTION_2$type5  \EJECTION1  (
      .\clk (\clk ), .\rst (\rst )
    , .\bus_ins1$irdy (\goodPkts$irdy )
    , .\bus_ins1$data (\goodPkts$data )
    , .\bus_ins1$trdy (\goodPkts$trdy )
    , .\bus_ins2$irdy (\bypassLine$irdy )
    , .\bus_ins2$data (\bypassLine$data )
    , .\bus_ins2$trdy (\bypassLine$trdy )
    , .\bus_ins3$irdy (\toEjection$irdy )
    , .\bus_ins3$data (\toEjection$data )
    , .\bus_ins3$trdy (\toEjection$trdy )
    , .\output$irdy (\channel1$irdy )
    , .\output$data (\channel1$data )
    , .\output$trdy (\channel1$trdy )
  );
  
endmodule


//
// BBB_0_1_2_2_0_2 switch functions
//
module \SFUN_0$BBB_0_1_2_2_0_2_Switch1 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , output [0:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[1:0] \f$bool$g0  = \i0$data  ;
  wire[1:0] \f$bool$f$arg0$arg0$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$arg0$arg0$arg0$conj  = \f$bool$f$arg0$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$arg0$arg0$arg0  = \f$bool$f$arg0$arg0$arg0$conj [1:1] ;
  wire[0:0] \f$bool$f$arg0$arg0$arg1  = 1'd0 ;
  wire \f$bool$f$arg0$arg0  = \f$bool$f$arg0$arg0$arg0  == \f$bool$f$arg0$arg0$arg1  ;
  wire \f$bool$f$arg0  = !\f$bool$f$arg0$arg0  ;
  wire[1:0] \f$bool$f$arg1$arg0$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$arg1$arg0$arg0$conj  = \f$bool$f$arg1$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$arg1$arg0$arg0  = \f$bool$f$arg1$arg0$arg0$conj [0:0] ;
  wire[0:0] \f$bool$f$arg1$arg0$arg1  = 1'd1 ;
  wire \f$bool$f$arg1$arg0  = \f$bool$f$arg1$arg0$arg0  == \f$bool$f$arg1$arg0$arg1  ;
  wire \f$bool$f$arg1  = !\f$bool$f$arg1$arg0  ;
  wire \f$bool$f  = \f$bool$f$arg0  && \f$bool$f$arg1  ;
  wire \f$bool  = \f$bool$f  ;
  wire[0:0] \f$true$content  = 1'd0 ;
  wire[0:0] \f$true  = \f$true$content  ;
  wire[1:0] \f$false$bool$g0  = \i0$data  ;
  wire[1:0] \f$false$bool$f$arg0$arg0$arg0$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$arg0$arg0$arg0$conj  = \f$false$bool$f$arg0$arg0$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$arg0$arg0$arg0  = \f$false$bool$f$arg0$arg0$arg0$arg0$conj [1:1] ;
  wire[0:0] \f$false$bool$f$arg0$arg0$arg0$arg1  = 1'd0 ;
  wire \f$false$bool$f$arg0$arg0$arg0  = \f$false$bool$f$arg0$arg0$arg0$arg0  == \f$false$bool$f$arg0$arg0$arg0$arg1  ;
  wire \f$false$bool$f$arg0$arg0  = !\f$false$bool$f$arg0$arg0$arg0  ;
  wire[1:0] \f$false$bool$f$arg0$arg1$arg0$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$arg1$arg0$arg0$conj  = \f$false$bool$f$arg0$arg1$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$arg1$arg0$arg0  = \f$false$bool$f$arg0$arg1$arg0$arg0$conj [0:0] ;
  wire[0:0] \f$false$bool$f$arg0$arg1$arg0$arg1  = 1'd1 ;
  wire \f$false$bool$f$arg0$arg1$arg0  = \f$false$bool$f$arg0$arg1$arg0$arg0  == \f$false$bool$f$arg0$arg1$arg0$arg1  ;
  wire \f$false$bool$f$arg0$arg1  = !\f$false$bool$f$arg0$arg1$arg0  ;
  wire \f$false$bool$f$arg0  = \f$false$bool$f$arg0$arg0  && \f$false$bool$f$arg0$arg1  ;
  wire \f$false$bool$f  = !\f$false$bool$f$arg0  ;
  wire \f$false$bool  = \f$false$bool$f  ;
  wire[0:0] \f$false$true$content  = 1'd1 ;
  wire[0:0] \f$false$true  = \f$false$true$content  ;
  wire[0:0] \f$false$false$content  = 1'd0 ;
  wire[0:0] \f$false$false  = \f$false$false$content  ;
  wire[0:0] \f$false  = ( \f$false$bool  ? \f$false$true  : \f$false$false  ) ;
  wire[0:0] \f  = ( \f$bool  ? \f$true  : \f$false  ) ;
  
  assign \o0  = \f  ;
endmodule

module \OFUN_1$BBB_0_1_2_2_0_2_Switch1 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , output [1:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[1:0] \f  = \i0$data  ;
  
  assign \o0  = \f  ;
endmodule

module \OFUN_2$BBB_0_1_2_2_0_2_Switch1 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , output [1:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[1:0] \f  = \i0$data  ;
  
  assign \o0  = \f  ;
endmodule

module \BBB_1_0_2_2_0_2 (
      input \clk , input \rst , input [63:0] \t 
    , input \bus_ins1$irdy , input [1:0] \bus_ins1$data , output \bus_ins1$trdy 
    , input \bus_ins2$irdy , input [1:0] \bus_ins2$data , output \bus_ins2$trdy 
    , input \bus_ins3$irdy , input [1:0] \bus_ins3$data , output \bus_ins3$trdy 
    , input \bus_ins4$irdy , input [0:0] \bus_ins4$data , output \bus_ins4$trdy 
    , output \bus_outs1$irdy , output [1:0] \bus_outs1$data , input \bus_outs1$trdy 
    , output \bus_outs2$irdy , output [1:0] \bus_outs2$data , input \bus_outs2$trdy 
    , output \bus_outs3$irdy , output [1:0] \bus_outs3$data , input \bus_outs3$trdy 
    , output \bus_outs4$irdy , output [0:0] \bus_outs4$data , input \bus_outs4$trdy 
    , input \Sink1$unbound_trdy 
    , output \Sink1$irdy 
    , output [1:0] \Sink1$data 
    , input \RECEPTION1$CreditCounter1$PatientSource1$unbound_irdy 
    , input [0:0] \RECEPTION1$CreditCounter1$PatientSource1$unbound_data 
    , output \RECEPTION1$CreditCounter1$PatientSource1$trdy 
    , input \RECEPTION1$CreditCounter1$Sink1$unbound_trdy 
    , output \RECEPTION1$CreditCounter1$Sink1$irdy 
    , output [0:0] \RECEPTION1$CreditCounter1$Sink1$data 
  );
  
  //
  // Channel declarations
  //
  wire \toEjection$irdy  ;
  wire [1:0] \toEjection$data  ;
  wire \toEjection$trdy  ;
  wire \toDFIFO$irdy  ;
  wire [1:0] \toDFIFO$data  ;
  wire \toDFIFO$trdy  ;
  wire \bypassLine$irdy  ;
  wire [1:0] \bypassLine$data  ;
  wire \bypassLine$trdy  ;
  wire \goodPkts$irdy  ;
  wire [1:0] \goodPkts$data  ;
  wire \goodPkts$trdy  ;
  wire \badPkts$irdy  ;
  wire [1:0] \badPkts$data  ;
  wire \badPkts$trdy  ;
  wire \channel1$irdy  ;
  wire [1:0] \channel1$data  ;
  wire \channel1$trdy  ;
  wire \channel2$irdy  ;
  wire \channel2$data  ;
  wire \channel2$trdy  ;
  
  //
  // Function Channels
  //
  wire \sfunchan_0_Switch1$data  ;
  wire [1:0] \ofunchan_1_Switch1$data  ;
  wire [1:0] \ofunchan_2_Switch1$data  ;
  
  //
  // Component and Macro instantiations
  //
  \Switch2  #(
    .OUTPUTSIZE0(2),
    .OUTPUTSIZE1(2),
    .INPUTSIZE(2)
  ) \Switch1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\bus_ins1$irdy )
    , .\i0$data (\bus_ins1$data )
    , .\i0$trdy (\bus_ins1$trdy )
    , .\o0$irdy (\goodPkts$irdy )
    , .\o0$data (\goodPkts$data )
    , .\o0$trdy (\goodPkts$trdy )
    , .\o1$irdy (\badPkts$irdy )
    , .\o1$data (\badPkts$data )
    , .\o1$trdy (\badPkts$trdy )
    , .\sel$data (\sfunchan_0_Switch1$data )
    , .\f0$data (\ofunchan_1_Switch1$data )
    , .\f1$data (\ofunchan_2_Switch1$data )
  );
  
  \SFUN_0$BBB_1_0_2_2_0_2_Switch1  \sfun_0_Switch1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\bus_ins1$data )
    , .\o0 (\sfunchan_0_Switch1$data )
  );
  
  \OFUN_1$BBB_1_0_2_2_0_2_Switch1  \ofun_1_Switch1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\bus_ins1$data )
    , .\o0 (\ofunchan_1_Switch1$data )
  );
  
  \OFUN_2$BBB_1_0_2_2_0_2_Switch1  \ofun_2_Switch1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\bus_ins1$data )
    , .\o0 (\ofunchan_2_Switch1$data )
  );
  
  assign \Sink1$irdy  = \badPkts$irdy  ;
  assign \Sink1$data  = \badPkts$data  ;
  \Sink  #(
    .DATASIZE(2)
  ) \Sink1  (
      .\clk (\clk ), .\rst (\rst ), .\t (\t )
    , .\i0$irdy (\badPkts$irdy )
    , .\i0$data (\badPkts$data )
    , .\i0$trdy (\badPkts$trdy )
    , .\unbound_trdy (\Sink1$unbound_trdy )
  );
  
  \CTRLJoin2  #(
    .INPUTSIZE1(1),
    .OUTPUTSIZE(2),
    .INPUTSIZE0(2)
  ) \CtrlJoin1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\channel1$irdy )
    , .\i0$data (\channel1$data )
    , .\i0$trdy (\channel1$trdy )
    , .\i1$irdy (\channel2$irdy )
    , .\i1$data (\channel2$data )
    , .\i1$trdy (\channel2$trdy )
    , .\o0$irdy (\bus_outs2$irdy )
    , .\o0$data (\bus_outs2$data )
    , .\o0$trdy (\bus_outs2$trdy )
  );
  
  \Queue  #(
    .NUM_DATA(0),
    .DATASIZE(1),
    .LENGTH(2)
  ) \Queue1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\bus_ins4$irdy )
    , .\i0$data (\bus_ins4$data )
    , .\i0$trdy (\bus_ins4$trdy )
    , .\o0$irdy (\channel2$irdy )
    , .\o0$data (\channel2$data )
    , .\o0$trdy (\channel2$trdy )
  );
  
  \RECEPTION_1_0_0_2  \RECEPTION1  (
      .\clk (\clk ), .\rst (\rst ), .\t (\t )
    , .\input$irdy (\bus_ins2$irdy )
    , .\input$data (\bus_ins2$data )
    , .\input$trdy (\bus_ins2$trdy )
    , .\bus_outs1$irdy (\bus_outs1$irdy )
    , .\bus_outs1$data (\bus_outs1$data )
    , .\bus_outs1$trdy (\bus_outs1$trdy )
    , .\bus_outs2$irdy (\bypassLine$irdy )
    , .\bus_outs2$data (\bypassLine$data )
    , .\bus_outs2$trdy (\bypassLine$trdy )
    , .\bus_outs3$irdy (\toDFIFO$irdy )
    , .\bus_outs3$data (\toDFIFO$data )
    , .\bus_outs3$trdy (\toDFIFO$trdy )
    , .\bus_outs4$irdy (\bus_outs4$irdy )
    , .\bus_outs4$data (\bus_outs4$data )
    , .\bus_outs4$trdy (\bus_outs4$trdy )
    , .\CreditCounter1$PatientSource1$unbound_irdy (\RECEPTION1$CreditCounter1$PatientSource1$unbound_irdy )
    , .\CreditCounter1$PatientSource1$unbound_data (\RECEPTION1$CreditCounter1$PatientSource1$unbound_data )
    , .\CreditCounter1$PatientSource1$trdy (\RECEPTION1$CreditCounter1$PatientSource1$trdy )
    , .\CreditCounter1$Sink1$unbound_trdy (\RECEPTION1$CreditCounter1$Sink1$unbound_trdy )
    , .\CreditCounter1$Sink1$irdy (\RECEPTION1$CreditCounter1$Sink1$irdy )
    , .\CreditCounter1$Sink1$data (\RECEPTION1$CreditCounter1$Sink1$data )
  );
  
  \DFIFO_2$type3  \DFIFO1  (
      .\clk (\clk ), .\rst (\rst )
    , .\bus_ins1$irdy (\toDFIFO$irdy )
    , .\bus_ins1$data (\toDFIFO$data )
    , .\bus_ins1$trdy (\toDFIFO$trdy )
    , .\bus_ins2$irdy (\bus_ins3$irdy )
    , .\bus_ins2$data (\bus_ins3$data )
    , .\bus_ins2$trdy (\bus_ins3$trdy )
    , .\bus_outs1$irdy (\bus_outs3$irdy )
    , .\bus_outs1$data (\bus_outs3$data )
    , .\bus_outs1$trdy (\bus_outs3$trdy )
    , .\bus_outs2$irdy (\toEjection$irdy )
    , .\bus_outs2$data (\toEjection$data )
    , .\bus_outs2$trdy (\toEjection$trdy )
  );
  
  \EJECTION_2$type2  \EJECTION1  (
      .\clk (\clk ), .\rst (\rst )
    , .\bus_ins1$irdy (\goodPkts$irdy )
    , .\bus_ins1$data (\goodPkts$data )
    , .\bus_ins1$trdy (\goodPkts$trdy )
    , .\bus_ins2$irdy (\bypassLine$irdy )
    , .\bus_ins2$data (\bypassLine$data )
    , .\bus_ins2$trdy (\bypassLine$trdy )
    , .\bus_ins3$irdy (\toEjection$irdy )
    , .\bus_ins3$data (\toEjection$data )
    , .\bus_ins3$trdy (\toEjection$trdy )
    , .\output$irdy (\channel1$irdy )
    , .\output$data (\channel1$data )
    , .\output$trdy (\channel1$trdy )
  );
  
endmodule


//
// BBB_1_0_2_2_0_2 switch functions
//
module \SFUN_0$BBB_1_0_2_2_0_2_Switch1 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , output [0:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[1:0] \f$bool$g0  = \i0$data  ;
  wire[1:0] \f$bool$f$arg0$arg0$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$arg0$arg0$arg0$conj  = \f$bool$f$arg0$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$arg0$arg0$arg0  = \f$bool$f$arg0$arg0$arg0$conj [1:1] ;
  wire[0:0] \f$bool$f$arg0$arg0$arg1  = 1'd1 ;
  wire \f$bool$f$arg0$arg0  = \f$bool$f$arg0$arg0$arg0  == \f$bool$f$arg0$arg0$arg1  ;
  wire \f$bool$f$arg0  = !\f$bool$f$arg0$arg0  ;
  wire[1:0] \f$bool$f$arg1$arg0$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$arg1$arg0$arg0$conj  = \f$bool$f$arg1$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$arg1$arg0$arg0  = \f$bool$f$arg1$arg0$arg0$conj [0:0] ;
  wire[0:0] \f$bool$f$arg1$arg0$arg1  = 1'd0 ;
  wire \f$bool$f$arg1$arg0  = \f$bool$f$arg1$arg0$arg0  == \f$bool$f$arg1$arg0$arg1  ;
  wire \f$bool$f$arg1  = !\f$bool$f$arg1$arg0  ;
  wire \f$bool$f  = \f$bool$f$arg0  && \f$bool$f$arg1  ;
  wire \f$bool  = \f$bool$f  ;
  wire[0:0] \f$true$content  = 1'd0 ;
  wire[0:0] \f$true  = \f$true$content  ;
  wire[1:0] \f$false$bool$g0  = \i0$data  ;
  wire[1:0] \f$false$bool$f$arg0$arg0$arg0$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$arg0$arg0$arg0$conj  = \f$false$bool$f$arg0$arg0$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$arg0$arg0$arg0  = \f$false$bool$f$arg0$arg0$arg0$arg0$conj [1:1] ;
  wire[0:0] \f$false$bool$f$arg0$arg0$arg0$arg1  = 1'd1 ;
  wire \f$false$bool$f$arg0$arg0$arg0  = \f$false$bool$f$arg0$arg0$arg0$arg0  == \f$false$bool$f$arg0$arg0$arg0$arg1  ;
  wire \f$false$bool$f$arg0$arg0  = !\f$false$bool$f$arg0$arg0$arg0  ;
  wire[1:0] \f$false$bool$f$arg0$arg1$arg0$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$arg1$arg0$arg0$conj  = \f$false$bool$f$arg0$arg1$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$arg1$arg0$arg0  = \f$false$bool$f$arg0$arg1$arg0$arg0$conj [0:0] ;
  wire[0:0] \f$false$bool$f$arg0$arg1$arg0$arg1  = 1'd0 ;
  wire \f$false$bool$f$arg0$arg1$arg0  = \f$false$bool$f$arg0$arg1$arg0$arg0  == \f$false$bool$f$arg0$arg1$arg0$arg1  ;
  wire \f$false$bool$f$arg0$arg1  = !\f$false$bool$f$arg0$arg1$arg0  ;
  wire \f$false$bool$f$arg0  = \f$false$bool$f$arg0$arg0  && \f$false$bool$f$arg0$arg1  ;
  wire \f$false$bool$f  = !\f$false$bool$f$arg0  ;
  wire \f$false$bool  = \f$false$bool$f  ;
  wire[0:0] \f$false$true$content  = 1'd1 ;
  wire[0:0] \f$false$true  = \f$false$true$content  ;
  wire[0:0] \f$false$false$content  = 1'd0 ;
  wire[0:0] \f$false$false  = \f$false$false$content  ;
  wire[0:0] \f$false  = ( \f$false$bool  ? \f$false$true  : \f$false$false  ) ;
  wire[0:0] \f  = ( \f$bool  ? \f$true  : \f$false  ) ;
  
  assign \o0  = \f  ;
endmodule

module \OFUN_1$BBB_1_0_2_2_0_2_Switch1 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , output [1:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[1:0] \f  = \i0$data  ;
  
  assign \o0  = \f  ;
endmodule

module \OFUN_2$BBB_1_0_2_2_0_2_Switch1 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , output [1:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[1:0] \f  = \i0$data  ;
  
  assign \o0  = \f  ;
endmodule

module \BBB_1_1_2_2_3_2 (
      input \clk , input \rst , input [63:0] \t 
    , input \bus_ins1$irdy , input [1:0] \bus_ins1$data , output \bus_ins1$trdy 
    , input \bus_ins2$irdy , input [1:0] \bus_ins2$data , output \bus_ins2$trdy 
    , input \bus_ins3$irdy , input [1:0] \bus_ins3$data , output \bus_ins3$trdy 
    , input \bus_ins4$irdy , input [0:0] \bus_ins4$data , output \bus_ins4$trdy 
    , output \bus_outs1$irdy , output [1:0] \bus_outs1$data , input \bus_outs1$trdy 
    , output \bus_outs2$irdy , output [1:0] \bus_outs2$data , input \bus_outs2$trdy 
    , output \bus_outs3$irdy , output [1:0] \bus_outs3$data , input \bus_outs3$trdy 
    , output \bus_outs4$irdy , output [0:0] \bus_outs4$data , input \bus_outs4$trdy 
    , input \Sink1$unbound_trdy 
    , output \Sink1$irdy 
    , output [1:0] \Sink1$data 
    , input \RECEPTION1$CreditCounter1$PatientSource1$unbound_irdy 
    , input [0:0] \RECEPTION1$CreditCounter1$PatientSource1$unbound_data 
    , output \RECEPTION1$CreditCounter1$PatientSource1$trdy 
    , input \RECEPTION1$CreditCounter1$Sink1$unbound_trdy 
    , output \RECEPTION1$CreditCounter1$Sink1$irdy 
    , output [0:0] \RECEPTION1$CreditCounter1$Sink1$data 
  );
  
  //
  // Channel declarations
  //
  wire \toEjection$irdy  ;
  wire [1:0] \toEjection$data  ;
  wire \toEjection$trdy  ;
  wire \toDFIFO$irdy  ;
  wire [1:0] \toDFIFO$data  ;
  wire \toDFIFO$trdy  ;
  wire \bypassLine$irdy  ;
  wire [1:0] \bypassLine$data  ;
  wire \bypassLine$trdy  ;
  wire \goodPkts$irdy  ;
  wire [1:0] \goodPkts$data  ;
  wire \goodPkts$trdy  ;
  wire \badPkts$irdy  ;
  wire [1:0] \badPkts$data  ;
  wire \badPkts$trdy  ;
  wire \channel1$irdy  ;
  wire [1:0] \channel1$data  ;
  wire \channel1$trdy  ;
  wire \channel2$irdy  ;
  wire \channel2$data  ;
  wire \channel2$trdy  ;
  
  //
  // Function Channels
  //
  wire \sfunchan_0_Switch1$data  ;
  wire [1:0] \ofunchan_1_Switch1$data  ;
  wire [1:0] \ofunchan_2_Switch1$data  ;
  
  //
  // Component and Macro instantiations
  //
  \Switch2  #(
    .OUTPUTSIZE0(2),
    .OUTPUTSIZE1(2),
    .INPUTSIZE(2)
  ) \Switch1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\bus_ins1$irdy )
    , .\i0$data (\bus_ins1$data )
    , .\i0$trdy (\bus_ins1$trdy )
    , .\o0$irdy (\goodPkts$irdy )
    , .\o0$data (\goodPkts$data )
    , .\o0$trdy (\goodPkts$trdy )
    , .\o1$irdy (\badPkts$irdy )
    , .\o1$data (\badPkts$data )
    , .\o1$trdy (\badPkts$trdy )
    , .\sel$data (\sfunchan_0_Switch1$data )
    , .\f0$data (\ofunchan_1_Switch1$data )
    , .\f1$data (\ofunchan_2_Switch1$data )
  );
  
  \SFUN_0$BBB_1_1_2_2_3_2_Switch1  \sfun_0_Switch1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\bus_ins1$data )
    , .\o0 (\sfunchan_0_Switch1$data )
  );
  
  \OFUN_1$BBB_1_1_2_2_3_2_Switch1  \ofun_1_Switch1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\bus_ins1$data )
    , .\o0 (\ofunchan_1_Switch1$data )
  );
  
  \OFUN_2$BBB_1_1_2_2_3_2_Switch1  \ofun_2_Switch1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\bus_ins1$data )
    , .\o0 (\ofunchan_2_Switch1$data )
  );
  
  assign \Sink1$irdy  = \badPkts$irdy  ;
  assign \Sink1$data  = \badPkts$data  ;
  \Sink  #(
    .DATASIZE(2)
  ) \Sink1  (
      .\clk (\clk ), .\rst (\rst ), .\t (\t )
    , .\i0$irdy (\badPkts$irdy )
    , .\i0$data (\badPkts$data )
    , .\i0$trdy (\badPkts$trdy )
    , .\unbound_trdy (\Sink1$unbound_trdy )
  );
  
  \CTRLJoin2  #(
    .INPUTSIZE1(1),
    .OUTPUTSIZE(2),
    .INPUTSIZE0(2)
  ) \CtrlJoin1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\channel1$irdy )
    , .\i0$data (\channel1$data )
    , .\i0$trdy (\channel1$trdy )
    , .\i1$irdy (\channel2$irdy )
    , .\i1$data (\channel2$data )
    , .\i1$trdy (\channel2$trdy )
    , .\o0$irdy (\bus_outs2$irdy )
    , .\o0$data (\bus_outs2$data )
    , .\o0$trdy (\bus_outs2$trdy )
  );
  
  \Queue  #(
    .NUM_DATA(0),
    .DATASIZE(1),
    .LENGTH(2)
  ) \Queue1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\bus_ins4$irdy )
    , .\i0$data (\bus_ins4$data )
    , .\i0$trdy (\bus_ins4$trdy )
    , .\o0$irdy (\channel2$irdy )
    , .\o0$data (\channel2$data )
    , .\o0$trdy (\channel2$trdy )
  );
  
  \RECEPTION_1_1_3_2  \RECEPTION1  (
      .\clk (\clk ), .\rst (\rst ), .\t (\t )
    , .\input$irdy (\bus_ins2$irdy )
    , .\input$data (\bus_ins2$data )
    , .\input$trdy (\bus_ins2$trdy )
    , .\bus_outs1$irdy (\bus_outs1$irdy )
    , .\bus_outs1$data (\bus_outs1$data )
    , .\bus_outs1$trdy (\bus_outs1$trdy )
    , .\bus_outs2$irdy (\bypassLine$irdy )
    , .\bus_outs2$data (\bypassLine$data )
    , .\bus_outs2$trdy (\bypassLine$trdy )
    , .\bus_outs3$irdy (\toDFIFO$irdy )
    , .\bus_outs3$data (\toDFIFO$data )
    , .\bus_outs3$trdy (\toDFIFO$trdy )
    , .\bus_outs4$irdy (\bus_outs4$irdy )
    , .\bus_outs4$data (\bus_outs4$data )
    , .\bus_outs4$trdy (\bus_outs4$trdy )
    , .\CreditCounter1$PatientSource1$unbound_irdy (\RECEPTION1$CreditCounter1$PatientSource1$unbound_irdy )
    , .\CreditCounter1$PatientSource1$unbound_data (\RECEPTION1$CreditCounter1$PatientSource1$unbound_data )
    , .\CreditCounter1$PatientSource1$trdy (\RECEPTION1$CreditCounter1$PatientSource1$trdy )
    , .\CreditCounter1$Sink1$unbound_trdy (\RECEPTION1$CreditCounter1$Sink1$unbound_trdy )
    , .\CreditCounter1$Sink1$irdy (\RECEPTION1$CreditCounter1$Sink1$irdy )
    , .\CreditCounter1$Sink1$data (\RECEPTION1$CreditCounter1$Sink1$data )
  );
  
  \DFIFO_2$type2  \DFIFO1  (
      .\clk (\clk ), .\rst (\rst )
    , .\bus_ins1$irdy (\toDFIFO$irdy )
    , .\bus_ins1$data (\toDFIFO$data )
    , .\bus_ins1$trdy (\toDFIFO$trdy )
    , .\bus_ins2$irdy (\bus_ins3$irdy )
    , .\bus_ins2$data (\bus_ins3$data )
    , .\bus_ins2$trdy (\bus_ins3$trdy )
    , .\bus_outs1$irdy (\bus_outs3$irdy )
    , .\bus_outs1$data (\bus_outs3$data )
    , .\bus_outs1$trdy (\bus_outs3$trdy )
    , .\bus_outs2$irdy (\toEjection$irdy )
    , .\bus_outs2$data (\toEjection$data )
    , .\bus_outs2$trdy (\toEjection$trdy )
  );
  
  \EJECTION_2$type1  \EJECTION1  (
      .\clk (\clk ), .\rst (\rst )
    , .\bus_ins1$irdy (\goodPkts$irdy )
    , .\bus_ins1$data (\goodPkts$data )
    , .\bus_ins1$trdy (\goodPkts$trdy )
    , .\bus_ins2$irdy (\bypassLine$irdy )
    , .\bus_ins2$data (\bypassLine$data )
    , .\bus_ins2$trdy (\bypassLine$trdy )
    , .\bus_ins3$irdy (\toEjection$irdy )
    , .\bus_ins3$data (\toEjection$data )
    , .\bus_ins3$trdy (\toEjection$trdy )
    , .\output$irdy (\channel1$irdy )
    , .\output$data (\channel1$data )
    , .\output$trdy (\channel1$trdy )
  );
  
endmodule


//
// BBB_1_1_2_2_3_2 switch functions
//
module \SFUN_0$BBB_1_1_2_2_3_2_Switch1 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , output [0:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[1:0] \f$bool$g0  = \i0$data  ;
  wire[1:0] \f$bool$f$arg0$arg0$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$arg0$arg0$arg0$conj  = \f$bool$f$arg0$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$arg0$arg0$arg0  = \f$bool$f$arg0$arg0$arg0$conj [1:1] ;
  wire[0:0] \f$bool$f$arg0$arg0$arg1  = 1'd1 ;
  wire \f$bool$f$arg0$arg0  = \f$bool$f$arg0$arg0$arg0  == \f$bool$f$arg0$arg0$arg1  ;
  wire \f$bool$f$arg0  = !\f$bool$f$arg0$arg0  ;
  wire[1:0] \f$bool$f$arg1$arg0$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$arg1$arg0$arg0$conj  = \f$bool$f$arg1$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$arg1$arg0$arg0  = \f$bool$f$arg1$arg0$arg0$conj [0:0] ;
  wire[0:0] \f$bool$f$arg1$arg0$arg1  = 1'd1 ;
  wire \f$bool$f$arg1$arg0  = \f$bool$f$arg1$arg0$arg0  == \f$bool$f$arg1$arg0$arg1  ;
  wire \f$bool$f$arg1  = !\f$bool$f$arg1$arg0  ;
  wire \f$bool$f  = \f$bool$f$arg0  && \f$bool$f$arg1  ;
  wire \f$bool  = \f$bool$f  ;
  wire[0:0] \f$true$content  = 1'd0 ;
  wire[0:0] \f$true  = \f$true$content  ;
  wire[1:0] \f$false$bool$g0  = \i0$data  ;
  wire[1:0] \f$false$bool$f$arg0$arg0$arg0$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$arg0$arg0$arg0$conj  = \f$false$bool$f$arg0$arg0$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$arg0$arg0$arg0  = \f$false$bool$f$arg0$arg0$arg0$arg0$conj [1:1] ;
  wire[0:0] \f$false$bool$f$arg0$arg0$arg0$arg1  = 1'd1 ;
  wire \f$false$bool$f$arg0$arg0$arg0  = \f$false$bool$f$arg0$arg0$arg0$arg0  == \f$false$bool$f$arg0$arg0$arg0$arg1  ;
  wire \f$false$bool$f$arg0$arg0  = !\f$false$bool$f$arg0$arg0$arg0  ;
  wire[1:0] \f$false$bool$f$arg0$arg1$arg0$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$arg1$arg0$arg0$conj  = \f$false$bool$f$arg0$arg1$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$arg1$arg0$arg0  = \f$false$bool$f$arg0$arg1$arg0$arg0$conj [0:0] ;
  wire[0:0] \f$false$bool$f$arg0$arg1$arg0$arg1  = 1'd1 ;
  wire \f$false$bool$f$arg0$arg1$arg0  = \f$false$bool$f$arg0$arg1$arg0$arg0  == \f$false$bool$f$arg0$arg1$arg0$arg1  ;
  wire \f$false$bool$f$arg0$arg1  = !\f$false$bool$f$arg0$arg1$arg0  ;
  wire \f$false$bool$f$arg0  = \f$false$bool$f$arg0$arg0  && \f$false$bool$f$arg0$arg1  ;
  wire \f$false$bool$f  = !\f$false$bool$f$arg0  ;
  wire \f$false$bool  = \f$false$bool$f  ;
  wire[0:0] \f$false$true$content  = 1'd1 ;
  wire[0:0] \f$false$true  = \f$false$true$content  ;
  wire[0:0] \f$false$false$content  = 1'd0 ;
  wire[0:0] \f$false$false  = \f$false$false$content  ;
  wire[0:0] \f$false  = ( \f$false$bool  ? \f$false$true  : \f$false$false  ) ;
  wire[0:0] \f  = ( \f$bool  ? \f$true  : \f$false  ) ;
  
  assign \o0  = \f  ;
endmodule

module \OFUN_1$BBB_1_1_2_2_3_2_Switch1 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , output [1:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[1:0] \f  = \i0$data  ;
  
  assign \o0  = \f  ;
endmodule

module \OFUN_2$BBB_1_1_2_2_3_2_Switch1 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , output [1:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[1:0] \f  = \i0$data  ;
  
  assign \o0  = \f  ;
endmodule

module \BBB_0_0_2_2_1_2 (
      input \clk , input \rst , input [63:0] \t 
    , input \bus_ins1$irdy , input [1:0] \bus_ins1$data , output \bus_ins1$trdy 
    , input \bus_ins2$irdy , input [1:0] \bus_ins2$data , output \bus_ins2$trdy 
    , input \bus_ins3$irdy , input [1:0] \bus_ins3$data , output \bus_ins3$trdy 
    , input \bus_ins4$irdy , input [0:0] \bus_ins4$data , output \bus_ins4$trdy 
    , output \bus_outs1$irdy , output [1:0] \bus_outs1$data , input \bus_outs1$trdy 
    , output \bus_outs2$irdy , output [1:0] \bus_outs2$data , input \bus_outs2$trdy 
    , output \bus_outs3$irdy , output [1:0] \bus_outs3$data , input \bus_outs3$trdy 
    , output \bus_outs4$irdy , output [0:0] \bus_outs4$data , input \bus_outs4$trdy 
    , input \Sink1$unbound_trdy 
    , output \Sink1$irdy 
    , output [1:0] \Sink1$data 
    , input \RECEPTION1$CreditCounter1$PatientSource1$unbound_irdy 
    , input [0:0] \RECEPTION1$CreditCounter1$PatientSource1$unbound_data 
    , output \RECEPTION1$CreditCounter1$PatientSource1$trdy 
    , input \RECEPTION1$CreditCounter1$Sink1$unbound_trdy 
    , output \RECEPTION1$CreditCounter1$Sink1$irdy 
    , output [0:0] \RECEPTION1$CreditCounter1$Sink1$data 
  );
  
  //
  // Channel declarations
  //
  wire \toEjection$irdy  ;
  wire [1:0] \toEjection$data  ;
  wire \toEjection$trdy  ;
  wire \toDFIFO$irdy  ;
  wire [1:0] \toDFIFO$data  ;
  wire \toDFIFO$trdy  ;
  wire \bypassLine$irdy  ;
  wire [1:0] \bypassLine$data  ;
  wire \bypassLine$trdy  ;
  wire \goodPkts$irdy  ;
  wire [1:0] \goodPkts$data  ;
  wire \goodPkts$trdy  ;
  wire \badPkts$irdy  ;
  wire [1:0] \badPkts$data  ;
  wire \badPkts$trdy  ;
  wire \channel1$irdy  ;
  wire [1:0] \channel1$data  ;
  wire \channel1$trdy  ;
  wire \channel2$irdy  ;
  wire \channel2$data  ;
  wire \channel2$trdy  ;
  
  //
  // Function Channels
  //
  wire \sfunchan_0_Switch1$data  ;
  wire [1:0] \ofunchan_1_Switch1$data  ;
  wire [1:0] \ofunchan_2_Switch1$data  ;
  
  //
  // Component and Macro instantiations
  //
  \Switch2  #(
    .OUTPUTSIZE0(2),
    .OUTPUTSIZE1(2),
    .INPUTSIZE(2)
  ) \Switch1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\bus_ins1$irdy )
    , .\i0$data (\bus_ins1$data )
    , .\i0$trdy (\bus_ins1$trdy )
    , .\o0$irdy (\goodPkts$irdy )
    , .\o0$data (\goodPkts$data )
    , .\o0$trdy (\goodPkts$trdy )
    , .\o1$irdy (\badPkts$irdy )
    , .\o1$data (\badPkts$data )
    , .\o1$trdy (\badPkts$trdy )
    , .\sel$data (\sfunchan_0_Switch1$data )
    , .\f0$data (\ofunchan_1_Switch1$data )
    , .\f1$data (\ofunchan_2_Switch1$data )
  );
  
  \SFUN_0$BBB_0_0_2_2_1_2_Switch1  \sfun_0_Switch1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\bus_ins1$data )
    , .\o0 (\sfunchan_0_Switch1$data )
  );
  
  \OFUN_1$BBB_0_0_2_2_1_2_Switch1  \ofun_1_Switch1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\bus_ins1$data )
    , .\o0 (\ofunchan_1_Switch1$data )
  );
  
  \OFUN_2$BBB_0_0_2_2_1_2_Switch1  \ofun_2_Switch1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\bus_ins1$data )
    , .\o0 (\ofunchan_2_Switch1$data )
  );
  
  assign \Sink1$irdy  = \badPkts$irdy  ;
  assign \Sink1$data  = \badPkts$data  ;
  \Sink  #(
    .DATASIZE(2)
  ) \Sink1  (
      .\clk (\clk ), .\rst (\rst ), .\t (\t )
    , .\i0$irdy (\badPkts$irdy )
    , .\i0$data (\badPkts$data )
    , .\i0$trdy (\badPkts$trdy )
    , .\unbound_trdy (\Sink1$unbound_trdy )
  );
  
  \CTRLJoin2  #(
    .INPUTSIZE1(1),
    .OUTPUTSIZE(2),
    .INPUTSIZE0(2)
  ) \CtrlJoin1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\channel1$irdy )
    , .\i0$data (\channel1$data )
    , .\i0$trdy (\channel1$trdy )
    , .\i1$irdy (\channel2$irdy )
    , .\i1$data (\channel2$data )
    , .\i1$trdy (\channel2$trdy )
    , .\o0$irdy (\bus_outs2$irdy )
    , .\o0$data (\bus_outs2$data )
    , .\o0$trdy (\bus_outs2$trdy )
  );
  
  \Queue  #(
    .NUM_DATA(0),
    .DATASIZE(1),
    .LENGTH(2)
  ) \Queue1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\bus_ins4$irdy )
    , .\i0$data (\bus_ins4$data )
    , .\i0$trdy (\bus_ins4$trdy )
    , .\o0$irdy (\channel2$irdy )
    , .\o0$data (\channel2$data )
    , .\o0$trdy (\channel2$trdy )
  );
  
  \RECEPTION_0_0_1_2  \RECEPTION1  (
      .\clk (\clk ), .\rst (\rst ), .\t (\t )
    , .\input$irdy (\bus_ins2$irdy )
    , .\input$data (\bus_ins2$data )
    , .\input$trdy (\bus_ins2$trdy )
    , .\bus_outs1$irdy (\bus_outs1$irdy )
    , .\bus_outs1$data (\bus_outs1$data )
    , .\bus_outs1$trdy (\bus_outs1$trdy )
    , .\bus_outs2$irdy (\bypassLine$irdy )
    , .\bus_outs2$data (\bypassLine$data )
    , .\bus_outs2$trdy (\bypassLine$trdy )
    , .\bus_outs3$irdy (\toDFIFO$irdy )
    , .\bus_outs3$data (\toDFIFO$data )
    , .\bus_outs3$trdy (\toDFIFO$trdy )
    , .\bus_outs4$irdy (\bus_outs4$irdy )
    , .\bus_outs4$data (\bus_outs4$data )
    , .\bus_outs4$trdy (\bus_outs4$trdy )
    , .\CreditCounter1$PatientSource1$unbound_irdy (\RECEPTION1$CreditCounter1$PatientSource1$unbound_irdy )
    , .\CreditCounter1$PatientSource1$unbound_data (\RECEPTION1$CreditCounter1$PatientSource1$unbound_data )
    , .\CreditCounter1$PatientSource1$trdy (\RECEPTION1$CreditCounter1$PatientSource1$trdy )
    , .\CreditCounter1$Sink1$unbound_trdy (\RECEPTION1$CreditCounter1$Sink1$unbound_trdy )
    , .\CreditCounter1$Sink1$irdy (\RECEPTION1$CreditCounter1$Sink1$irdy )
    , .\CreditCounter1$Sink1$data (\RECEPTION1$CreditCounter1$Sink1$data )
  );
  
  \DFIFO_2$type0  \DFIFO1  (
      .\clk (\clk ), .\rst (\rst )
    , .\bus_ins1$irdy (\toDFIFO$irdy )
    , .\bus_ins1$data (\toDFIFO$data )
    , .\bus_ins1$trdy (\toDFIFO$trdy )
    , .\bus_ins2$irdy (\bus_ins3$irdy )
    , .\bus_ins2$data (\bus_ins3$data )
    , .\bus_ins2$trdy (\bus_ins3$trdy )
    , .\bus_outs1$irdy (\bus_outs3$irdy )
    , .\bus_outs1$data (\bus_outs3$data )
    , .\bus_outs1$trdy (\bus_outs3$trdy )
    , .\bus_outs2$irdy (\toEjection$irdy )
    , .\bus_outs2$data (\toEjection$data )
    , .\bus_outs2$trdy (\toEjection$trdy )
  );
  
  \EJECTION_2$type7  \EJECTION1  (
      .\clk (\clk ), .\rst (\rst )
    , .\bus_ins1$irdy (\goodPkts$irdy )
    , .\bus_ins1$data (\goodPkts$data )
    , .\bus_ins1$trdy (\goodPkts$trdy )
    , .\bus_ins2$irdy (\bypassLine$irdy )
    , .\bus_ins2$data (\bypassLine$data )
    , .\bus_ins2$trdy (\bypassLine$trdy )
    , .\bus_ins3$irdy (\toEjection$irdy )
    , .\bus_ins3$data (\toEjection$data )
    , .\bus_ins3$trdy (\toEjection$trdy )
    , .\output$irdy (\channel1$irdy )
    , .\output$data (\channel1$data )
    , .\output$trdy (\channel1$trdy )
  );
  
endmodule


//
// BBB_0_0_2_2_1_2 switch functions
//
module \SFUN_0$BBB_0_0_2_2_1_2_Switch1 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , output [0:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[1:0] \f$bool$g0  = \i0$data  ;
  wire[1:0] \f$bool$f$arg0$arg0$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$arg0$arg0$arg0$conj  = \f$bool$f$arg0$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$arg0$arg0$arg0  = \f$bool$f$arg0$arg0$arg0$conj [1:1] ;
  wire[0:0] \f$bool$f$arg0$arg0$arg1  = 1'd0 ;
  wire \f$bool$f$arg0$arg0  = \f$bool$f$arg0$arg0$arg0  == \f$bool$f$arg0$arg0$arg1  ;
  wire \f$bool$f$arg0  = !\f$bool$f$arg0$arg0  ;
  wire[1:0] \f$bool$f$arg1$arg0$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$arg1$arg0$arg0$conj  = \f$bool$f$arg1$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$arg1$arg0$arg0  = \f$bool$f$arg1$arg0$arg0$conj [0:0] ;
  wire[0:0] \f$bool$f$arg1$arg0$arg1  = 1'd0 ;
  wire \f$bool$f$arg1$arg0  = \f$bool$f$arg1$arg0$arg0  == \f$bool$f$arg1$arg0$arg1  ;
  wire \f$bool$f$arg1  = !\f$bool$f$arg1$arg0  ;
  wire \f$bool$f  = \f$bool$f$arg0  && \f$bool$f$arg1  ;
  wire \f$bool  = \f$bool$f  ;
  wire[0:0] \f$true$content  = 1'd0 ;
  wire[0:0] \f$true  = \f$true$content  ;
  wire[1:0] \f$false$bool$g0  = \i0$data  ;
  wire[1:0] \f$false$bool$f$arg0$arg0$arg0$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$arg0$arg0$arg0$conj  = \f$false$bool$f$arg0$arg0$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$arg0$arg0$arg0  = \f$false$bool$f$arg0$arg0$arg0$arg0$conj [1:1] ;
  wire[0:0] \f$false$bool$f$arg0$arg0$arg0$arg1  = 1'd0 ;
  wire \f$false$bool$f$arg0$arg0$arg0  = \f$false$bool$f$arg0$arg0$arg0$arg0  == \f$false$bool$f$arg0$arg0$arg0$arg1  ;
  wire \f$false$bool$f$arg0$arg0  = !\f$false$bool$f$arg0$arg0$arg0  ;
  wire[1:0] \f$false$bool$f$arg0$arg1$arg0$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$arg1$arg0$arg0$conj  = \f$false$bool$f$arg0$arg1$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$arg1$arg0$arg0  = \f$false$bool$f$arg0$arg1$arg0$arg0$conj [0:0] ;
  wire[0:0] \f$false$bool$f$arg0$arg1$arg0$arg1  = 1'd0 ;
  wire \f$false$bool$f$arg0$arg1$arg0  = \f$false$bool$f$arg0$arg1$arg0$arg0  == \f$false$bool$f$arg0$arg1$arg0$arg1  ;
  wire \f$false$bool$f$arg0$arg1  = !\f$false$bool$f$arg0$arg1$arg0  ;
  wire \f$false$bool$f$arg0  = \f$false$bool$f$arg0$arg0  && \f$false$bool$f$arg0$arg1  ;
  wire \f$false$bool$f  = !\f$false$bool$f$arg0  ;
  wire \f$false$bool  = \f$false$bool$f  ;
  wire[0:0] \f$false$true$content  = 1'd1 ;
  wire[0:0] \f$false$true  = \f$false$true$content  ;
  wire[0:0] \f$false$false$content  = 1'd0 ;
  wire[0:0] \f$false$false  = \f$false$false$content  ;
  wire[0:0] \f$false  = ( \f$false$bool  ? \f$false$true  : \f$false$false  ) ;
  wire[0:0] \f  = ( \f$bool  ? \f$true  : \f$false  ) ;
  
  assign \o0  = \f  ;
endmodule

module \OFUN_1$BBB_0_0_2_2_1_2_Switch1 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , output [1:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[1:0] \f  = \i0$data  ;
  
  assign \o0  = \f  ;
endmodule

module \OFUN_2$BBB_0_0_2_2_1_2_Switch1 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , output [1:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[1:0] \f  = \i0$data  ;
  
  assign \o0  = \f  ;
endmodule

module \BBB_0_1_2_2_3_2 (
      input \clk , input \rst , input [63:0] \t 
    , input \bus_ins1$irdy , input [1:0] \bus_ins1$data , output \bus_ins1$trdy 
    , input \bus_ins2$irdy , input [1:0] \bus_ins2$data , output \bus_ins2$trdy 
    , input \bus_ins3$irdy , input [1:0] \bus_ins3$data , output \bus_ins3$trdy 
    , input \bus_ins4$irdy , input [0:0] \bus_ins4$data , output \bus_ins4$trdy 
    , output \bus_outs1$irdy , output [1:0] \bus_outs1$data , input \bus_outs1$trdy 
    , output \bus_outs2$irdy , output [1:0] \bus_outs2$data , input \bus_outs2$trdy 
    , output \bus_outs3$irdy , output [1:0] \bus_outs3$data , input \bus_outs3$trdy 
    , output \bus_outs4$irdy , output [0:0] \bus_outs4$data , input \bus_outs4$trdy 
    , input \Sink1$unbound_trdy 
    , output \Sink1$irdy 
    , output [1:0] \Sink1$data 
    , input \RECEPTION1$CreditCounter1$PatientSource1$unbound_irdy 
    , input [0:0] \RECEPTION1$CreditCounter1$PatientSource1$unbound_data 
    , output \RECEPTION1$CreditCounter1$PatientSource1$trdy 
    , input \RECEPTION1$CreditCounter1$Sink1$unbound_trdy 
    , output \RECEPTION1$CreditCounter1$Sink1$irdy 
    , output [0:0] \RECEPTION1$CreditCounter1$Sink1$data 
  );
  
  //
  // Channel declarations
  //
  wire \toEjection$irdy  ;
  wire [1:0] \toEjection$data  ;
  wire \toEjection$trdy  ;
  wire \toDFIFO$irdy  ;
  wire [1:0] \toDFIFO$data  ;
  wire \toDFIFO$trdy  ;
  wire \bypassLine$irdy  ;
  wire [1:0] \bypassLine$data  ;
  wire \bypassLine$trdy  ;
  wire \goodPkts$irdy  ;
  wire [1:0] \goodPkts$data  ;
  wire \goodPkts$trdy  ;
  wire \badPkts$irdy  ;
  wire [1:0] \badPkts$data  ;
  wire \badPkts$trdy  ;
  wire \channel1$irdy  ;
  wire [1:0] \channel1$data  ;
  wire \channel1$trdy  ;
  wire \channel2$irdy  ;
  wire \channel2$data  ;
  wire \channel2$trdy  ;
  
  //
  // Function Channels
  //
  wire \sfunchan_0_Switch1$data  ;
  wire [1:0] \ofunchan_1_Switch1$data  ;
  wire [1:0] \ofunchan_2_Switch1$data  ;
  
  //
  // Component and Macro instantiations
  //
  \Switch2  #(
    .OUTPUTSIZE0(2),
    .OUTPUTSIZE1(2),
    .INPUTSIZE(2)
  ) \Switch1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\bus_ins1$irdy )
    , .\i0$data (\bus_ins1$data )
    , .\i0$trdy (\bus_ins1$trdy )
    , .\o0$irdy (\goodPkts$irdy )
    , .\o0$data (\goodPkts$data )
    , .\o0$trdy (\goodPkts$trdy )
    , .\o1$irdy (\badPkts$irdy )
    , .\o1$data (\badPkts$data )
    , .\o1$trdy (\badPkts$trdy )
    , .\sel$data (\sfunchan_0_Switch1$data )
    , .\f0$data (\ofunchan_1_Switch1$data )
    , .\f1$data (\ofunchan_2_Switch1$data )
  );
  
  \SFUN_0$BBB_0_1_2_2_3_2_Switch1  \sfun_0_Switch1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\bus_ins1$data )
    , .\o0 (\sfunchan_0_Switch1$data )
  );
  
  \OFUN_1$BBB_0_1_2_2_3_2_Switch1  \ofun_1_Switch1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\bus_ins1$data )
    , .\o0 (\ofunchan_1_Switch1$data )
  );
  
  \OFUN_2$BBB_0_1_2_2_3_2_Switch1  \ofun_2_Switch1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\bus_ins1$data )
    , .\o0 (\ofunchan_2_Switch1$data )
  );
  
  assign \Sink1$irdy  = \badPkts$irdy  ;
  assign \Sink1$data  = \badPkts$data  ;
  \Sink  #(
    .DATASIZE(2)
  ) \Sink1  (
      .\clk (\clk ), .\rst (\rst ), .\t (\t )
    , .\i0$irdy (\badPkts$irdy )
    , .\i0$data (\badPkts$data )
    , .\i0$trdy (\badPkts$trdy )
    , .\unbound_trdy (\Sink1$unbound_trdy )
  );
  
  \CTRLJoin2  #(
    .INPUTSIZE1(1),
    .OUTPUTSIZE(2),
    .INPUTSIZE0(2)
  ) \CtrlJoin1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\channel1$irdy )
    , .\i0$data (\channel1$data )
    , .\i0$trdy (\channel1$trdy )
    , .\i1$irdy (\channel2$irdy )
    , .\i1$data (\channel2$data )
    , .\i1$trdy (\channel2$trdy )
    , .\o0$irdy (\bus_outs2$irdy )
    , .\o0$data (\bus_outs2$data )
    , .\o0$trdy (\bus_outs2$trdy )
  );
  
  \Queue  #(
    .NUM_DATA(0),
    .DATASIZE(1),
    .LENGTH(2)
  ) \Queue1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\bus_ins4$irdy )
    , .\i0$data (\bus_ins4$data )
    , .\i0$trdy (\bus_ins4$trdy )
    , .\o0$irdy (\channel2$irdy )
    , .\o0$data (\channel2$data )
    , .\o0$trdy (\channel2$trdy )
  );
  
  \RECEPTION_0_1_3_2  \RECEPTION1  (
      .\clk (\clk ), .\rst (\rst ), .\t (\t )
    , .\input$irdy (\bus_ins2$irdy )
    , .\input$data (\bus_ins2$data )
    , .\input$trdy (\bus_ins2$trdy )
    , .\bus_outs1$irdy (\bus_outs1$irdy )
    , .\bus_outs1$data (\bus_outs1$data )
    , .\bus_outs1$trdy (\bus_outs1$trdy )
    , .\bus_outs2$irdy (\bypassLine$irdy )
    , .\bus_outs2$data (\bypassLine$data )
    , .\bus_outs2$trdy (\bypassLine$trdy )
    , .\bus_outs3$irdy (\toDFIFO$irdy )
    , .\bus_outs3$data (\toDFIFO$data )
    , .\bus_outs3$trdy (\toDFIFO$trdy )
    , .\bus_outs4$irdy (\bus_outs4$irdy )
    , .\bus_outs4$data (\bus_outs4$data )
    , .\bus_outs4$trdy (\bus_outs4$trdy )
    , .\CreditCounter1$PatientSource1$unbound_irdy (\RECEPTION1$CreditCounter1$PatientSource1$unbound_irdy )
    , .\CreditCounter1$PatientSource1$unbound_data (\RECEPTION1$CreditCounter1$PatientSource1$unbound_data )
    , .\CreditCounter1$PatientSource1$trdy (\RECEPTION1$CreditCounter1$PatientSource1$trdy )
    , .\CreditCounter1$Sink1$unbound_trdy (\RECEPTION1$CreditCounter1$Sink1$unbound_trdy )
    , .\CreditCounter1$Sink1$irdy (\RECEPTION1$CreditCounter1$Sink1$irdy )
    , .\CreditCounter1$Sink1$data (\RECEPTION1$CreditCounter1$Sink1$data )
  );
  
  \DFIFO_2$type2  \DFIFO1  (
      .\clk (\clk ), .\rst (\rst )
    , .\bus_ins1$irdy (\toDFIFO$irdy )
    , .\bus_ins1$data (\toDFIFO$data )
    , .\bus_ins1$trdy (\toDFIFO$trdy )
    , .\bus_ins2$irdy (\bus_ins3$irdy )
    , .\bus_ins2$data (\bus_ins3$data )
    , .\bus_ins2$trdy (\bus_ins3$trdy )
    , .\bus_outs1$irdy (\bus_outs3$irdy )
    , .\bus_outs1$data (\bus_outs3$data )
    , .\bus_outs1$trdy (\bus_outs3$trdy )
    , .\bus_outs2$irdy (\toEjection$irdy )
    , .\bus_outs2$data (\toEjection$data )
    , .\bus_outs2$trdy (\toEjection$trdy )
  );
  
  \EJECTION_2$type4  \EJECTION1  (
      .\clk (\clk ), .\rst (\rst )
    , .\bus_ins1$irdy (\goodPkts$irdy )
    , .\bus_ins1$data (\goodPkts$data )
    , .\bus_ins1$trdy (\goodPkts$trdy )
    , .\bus_ins2$irdy (\bypassLine$irdy )
    , .\bus_ins2$data (\bypassLine$data )
    , .\bus_ins2$trdy (\bypassLine$trdy )
    , .\bus_ins3$irdy (\toEjection$irdy )
    , .\bus_ins3$data (\toEjection$data )
    , .\bus_ins3$trdy (\toEjection$trdy )
    , .\output$irdy (\channel1$irdy )
    , .\output$data (\channel1$data )
    , .\output$trdy (\channel1$trdy )
  );
  
endmodule


//
// BBB_0_1_2_2_3_2 switch functions
//
module \SFUN_0$BBB_0_1_2_2_3_2_Switch1 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , output [0:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[1:0] \f$bool$g0  = \i0$data  ;
  wire[1:0] \f$bool$f$arg0$arg0$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$arg0$arg0$arg0$conj  = \f$bool$f$arg0$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$arg0$arg0$arg0  = \f$bool$f$arg0$arg0$arg0$conj [1:1] ;
  wire[0:0] \f$bool$f$arg0$arg0$arg1  = 1'd0 ;
  wire \f$bool$f$arg0$arg0  = \f$bool$f$arg0$arg0$arg0  == \f$bool$f$arg0$arg0$arg1  ;
  wire \f$bool$f$arg0  = !\f$bool$f$arg0$arg0  ;
  wire[1:0] \f$bool$f$arg1$arg0$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$arg1$arg0$arg0$conj  = \f$bool$f$arg1$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$arg1$arg0$arg0  = \f$bool$f$arg1$arg0$arg0$conj [0:0] ;
  wire[0:0] \f$bool$f$arg1$arg0$arg1  = 1'd1 ;
  wire \f$bool$f$arg1$arg0  = \f$bool$f$arg1$arg0$arg0  == \f$bool$f$arg1$arg0$arg1  ;
  wire \f$bool$f$arg1  = !\f$bool$f$arg1$arg0  ;
  wire \f$bool$f  = \f$bool$f$arg0  && \f$bool$f$arg1  ;
  wire \f$bool  = \f$bool$f  ;
  wire[0:0] \f$true$content  = 1'd0 ;
  wire[0:0] \f$true  = \f$true$content  ;
  wire[1:0] \f$false$bool$g0  = \i0$data  ;
  wire[1:0] \f$false$bool$f$arg0$arg0$arg0$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$arg0$arg0$arg0$conj  = \f$false$bool$f$arg0$arg0$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$arg0$arg0$arg0  = \f$false$bool$f$arg0$arg0$arg0$arg0$conj [1:1] ;
  wire[0:0] \f$false$bool$f$arg0$arg0$arg0$arg1  = 1'd0 ;
  wire \f$false$bool$f$arg0$arg0$arg0  = \f$false$bool$f$arg0$arg0$arg0$arg0  == \f$false$bool$f$arg0$arg0$arg0$arg1  ;
  wire \f$false$bool$f$arg0$arg0  = !\f$false$bool$f$arg0$arg0$arg0  ;
  wire[1:0] \f$false$bool$f$arg0$arg1$arg0$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$arg1$arg0$arg0$conj  = \f$false$bool$f$arg0$arg1$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$arg1$arg0$arg0  = \f$false$bool$f$arg0$arg1$arg0$arg0$conj [0:0] ;
  wire[0:0] \f$false$bool$f$arg0$arg1$arg0$arg1  = 1'd1 ;
  wire \f$false$bool$f$arg0$arg1$arg0  = \f$false$bool$f$arg0$arg1$arg0$arg0  == \f$false$bool$f$arg0$arg1$arg0$arg1  ;
  wire \f$false$bool$f$arg0$arg1  = !\f$false$bool$f$arg0$arg1$arg0  ;
  wire \f$false$bool$f$arg0  = \f$false$bool$f$arg0$arg0  && \f$false$bool$f$arg0$arg1  ;
  wire \f$false$bool$f  = !\f$false$bool$f$arg0  ;
  wire \f$false$bool  = \f$false$bool$f  ;
  wire[0:0] \f$false$true$content  = 1'd1 ;
  wire[0:0] \f$false$true  = \f$false$true$content  ;
  wire[0:0] \f$false$false$content  = 1'd0 ;
  wire[0:0] \f$false$false  = \f$false$false$content  ;
  wire[0:0] \f$false  = ( \f$false$bool  ? \f$false$true  : \f$false$false  ) ;
  wire[0:0] \f  = ( \f$bool  ? \f$true  : \f$false  ) ;
  
  assign \o0  = \f  ;
endmodule

module \OFUN_1$BBB_0_1_2_2_3_2_Switch1 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , output [1:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[1:0] \f  = \i0$data  ;
  
  assign \o0  = \f  ;
endmodule

module \OFUN_2$BBB_0_1_2_2_3_2_Switch1 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , output [1:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[1:0] \f  = \i0$data  ;
  
  assign \o0  = \f  ;
endmodule

module \BBB_1_0_2_2_3_2 (
      input \clk , input \rst , input [63:0] \t 
    , input \bus_ins1$irdy , input [1:0] \bus_ins1$data , output \bus_ins1$trdy 
    , input \bus_ins2$irdy , input [1:0] \bus_ins2$data , output \bus_ins2$trdy 
    , input \bus_ins3$irdy , input [1:0] \bus_ins3$data , output \bus_ins3$trdy 
    , input \bus_ins4$irdy , input [0:0] \bus_ins4$data , output \bus_ins4$trdy 
    , output \bus_outs1$irdy , output [1:0] \bus_outs1$data , input \bus_outs1$trdy 
    , output \bus_outs2$irdy , output [1:0] \bus_outs2$data , input \bus_outs2$trdy 
    , output \bus_outs3$irdy , output [1:0] \bus_outs3$data , input \bus_outs3$trdy 
    , output \bus_outs4$irdy , output [0:0] \bus_outs4$data , input \bus_outs4$trdy 
    , input \Sink1$unbound_trdy 
    , output \Sink1$irdy 
    , output [1:0] \Sink1$data 
    , input \RECEPTION1$CreditCounter1$PatientSource1$unbound_irdy 
    , input [0:0] \RECEPTION1$CreditCounter1$PatientSource1$unbound_data 
    , output \RECEPTION1$CreditCounter1$PatientSource1$trdy 
    , input \RECEPTION1$CreditCounter1$Sink1$unbound_trdy 
    , output \RECEPTION1$CreditCounter1$Sink1$irdy 
    , output [0:0] \RECEPTION1$CreditCounter1$Sink1$data 
  );
  
  //
  // Channel declarations
  //
  wire \toEjection$irdy  ;
  wire [1:0] \toEjection$data  ;
  wire \toEjection$trdy  ;
  wire \toDFIFO$irdy  ;
  wire [1:0] \toDFIFO$data  ;
  wire \toDFIFO$trdy  ;
  wire \bypassLine$irdy  ;
  wire [1:0] \bypassLine$data  ;
  wire \bypassLine$trdy  ;
  wire \goodPkts$irdy  ;
  wire [1:0] \goodPkts$data  ;
  wire \goodPkts$trdy  ;
  wire \badPkts$irdy  ;
  wire [1:0] \badPkts$data  ;
  wire \badPkts$trdy  ;
  wire \channel1$irdy  ;
  wire [1:0] \channel1$data  ;
  wire \channel1$trdy  ;
  wire \channel2$irdy  ;
  wire \channel2$data  ;
  wire \channel2$trdy  ;
  
  //
  // Function Channels
  //
  wire \sfunchan_0_Switch1$data  ;
  wire [1:0] \ofunchan_1_Switch1$data  ;
  wire [1:0] \ofunchan_2_Switch1$data  ;
  
  //
  // Component and Macro instantiations
  //
  \Switch2  #(
    .OUTPUTSIZE0(2),
    .OUTPUTSIZE1(2),
    .INPUTSIZE(2)
  ) \Switch1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\bus_ins1$irdy )
    , .\i0$data (\bus_ins1$data )
    , .\i0$trdy (\bus_ins1$trdy )
    , .\o0$irdy (\goodPkts$irdy )
    , .\o0$data (\goodPkts$data )
    , .\o0$trdy (\goodPkts$trdy )
    , .\o1$irdy (\badPkts$irdy )
    , .\o1$data (\badPkts$data )
    , .\o1$trdy (\badPkts$trdy )
    , .\sel$data (\sfunchan_0_Switch1$data )
    , .\f0$data (\ofunchan_1_Switch1$data )
    , .\f1$data (\ofunchan_2_Switch1$data )
  );
  
  \SFUN_0$BBB_1_0_2_2_3_2_Switch1  \sfun_0_Switch1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\bus_ins1$data )
    , .\o0 (\sfunchan_0_Switch1$data )
  );
  
  \OFUN_1$BBB_1_0_2_2_3_2_Switch1  \ofun_1_Switch1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\bus_ins1$data )
    , .\o0 (\ofunchan_1_Switch1$data )
  );
  
  \OFUN_2$BBB_1_0_2_2_3_2_Switch1  \ofun_2_Switch1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\bus_ins1$data )
    , .\o0 (\ofunchan_2_Switch1$data )
  );
  
  assign \Sink1$irdy  = \badPkts$irdy  ;
  assign \Sink1$data  = \badPkts$data  ;
  \Sink  #(
    .DATASIZE(2)
  ) \Sink1  (
      .\clk (\clk ), .\rst (\rst ), .\t (\t )
    , .\i0$irdy (\badPkts$irdy )
    , .\i0$data (\badPkts$data )
    , .\i0$trdy (\badPkts$trdy )
    , .\unbound_trdy (\Sink1$unbound_trdy )
  );
  
  \CTRLJoin2  #(
    .INPUTSIZE1(1),
    .OUTPUTSIZE(2),
    .INPUTSIZE0(2)
  ) \CtrlJoin1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\channel1$irdy )
    , .\i0$data (\channel1$data )
    , .\i0$trdy (\channel1$trdy )
    , .\i1$irdy (\channel2$irdy )
    , .\i1$data (\channel2$data )
    , .\i1$trdy (\channel2$trdy )
    , .\o0$irdy (\bus_outs2$irdy )
    , .\o0$data (\bus_outs2$data )
    , .\o0$trdy (\bus_outs2$trdy )
  );
  
  \Queue  #(
    .NUM_DATA(0),
    .DATASIZE(1),
    .LENGTH(2)
  ) \Queue1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\bus_ins4$irdy )
    , .\i0$data (\bus_ins4$data )
    , .\i0$trdy (\bus_ins4$trdy )
    , .\o0$irdy (\channel2$irdy )
    , .\o0$data (\channel2$data )
    , .\o0$trdy (\channel2$trdy )
  );
  
  \RECEPTION_1_0_3_2  \RECEPTION1  (
      .\clk (\clk ), .\rst (\rst ), .\t (\t )
    , .\input$irdy (\bus_ins2$irdy )
    , .\input$data (\bus_ins2$data )
    , .\input$trdy (\bus_ins2$trdy )
    , .\bus_outs1$irdy (\bus_outs1$irdy )
    , .\bus_outs1$data (\bus_outs1$data )
    , .\bus_outs1$trdy (\bus_outs1$trdy )
    , .\bus_outs2$irdy (\bypassLine$irdy )
    , .\bus_outs2$data (\bypassLine$data )
    , .\bus_outs2$trdy (\bypassLine$trdy )
    , .\bus_outs3$irdy (\toDFIFO$irdy )
    , .\bus_outs3$data (\toDFIFO$data )
    , .\bus_outs3$trdy (\toDFIFO$trdy )
    , .\bus_outs4$irdy (\bus_outs4$irdy )
    , .\bus_outs4$data (\bus_outs4$data )
    , .\bus_outs4$trdy (\bus_outs4$trdy )
    , .\CreditCounter1$PatientSource1$unbound_irdy (\RECEPTION1$CreditCounter1$PatientSource1$unbound_irdy )
    , .\CreditCounter1$PatientSource1$unbound_data (\RECEPTION1$CreditCounter1$PatientSource1$unbound_data )
    , .\CreditCounter1$PatientSource1$trdy (\RECEPTION1$CreditCounter1$PatientSource1$trdy )
    , .\CreditCounter1$Sink1$unbound_trdy (\RECEPTION1$CreditCounter1$Sink1$unbound_trdy )
    , .\CreditCounter1$Sink1$irdy (\RECEPTION1$CreditCounter1$Sink1$irdy )
    , .\CreditCounter1$Sink1$data (\RECEPTION1$CreditCounter1$Sink1$data )
  );
  
  \DFIFO_2$type1  \DFIFO1  (
      .\clk (\clk ), .\rst (\rst )
    , .\bus_ins1$irdy (\toDFIFO$irdy )
    , .\bus_ins1$data (\toDFIFO$data )
    , .\bus_ins1$trdy (\toDFIFO$trdy )
    , .\bus_ins2$irdy (\bus_ins3$irdy )
    , .\bus_ins2$data (\bus_ins3$data )
    , .\bus_ins2$trdy (\bus_ins3$trdy )
    , .\bus_outs1$irdy (\bus_outs3$irdy )
    , .\bus_outs1$data (\bus_outs3$data )
    , .\bus_outs1$trdy (\bus_outs3$trdy )
    , .\bus_outs2$irdy (\toEjection$irdy )
    , .\bus_outs2$data (\toEjection$data )
    , .\bus_outs2$trdy (\toEjection$trdy )
  );
  
  \EJECTION_2$type3  \EJECTION1  (
      .\clk (\clk ), .\rst (\rst )
    , .\bus_ins1$irdy (\goodPkts$irdy )
    , .\bus_ins1$data (\goodPkts$data )
    , .\bus_ins1$trdy (\goodPkts$trdy )
    , .\bus_ins2$irdy (\bypassLine$irdy )
    , .\bus_ins2$data (\bypassLine$data )
    , .\bus_ins2$trdy (\bypassLine$trdy )
    , .\bus_ins3$irdy (\toEjection$irdy )
    , .\bus_ins3$data (\toEjection$data )
    , .\bus_ins3$trdy (\toEjection$trdy )
    , .\output$irdy (\channel1$irdy )
    , .\output$data (\channel1$data )
    , .\output$trdy (\channel1$trdy )
  );
  
endmodule


//
// BBB_1_0_2_2_3_2 switch functions
//
module \SFUN_0$BBB_1_0_2_2_3_2_Switch1 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , output [0:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[1:0] \f$bool$g0  = \i0$data  ;
  wire[1:0] \f$bool$f$arg0$arg0$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$arg0$arg0$arg0$conj  = \f$bool$f$arg0$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$arg0$arg0$arg0  = \f$bool$f$arg0$arg0$arg0$conj [1:1] ;
  wire[0:0] \f$bool$f$arg0$arg0$arg1  = 1'd1 ;
  wire \f$bool$f$arg0$arg0  = \f$bool$f$arg0$arg0$arg0  == \f$bool$f$arg0$arg0$arg1  ;
  wire \f$bool$f$arg0  = !\f$bool$f$arg0$arg0  ;
  wire[1:0] \f$bool$f$arg1$arg0$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$arg1$arg0$arg0$conj  = \f$bool$f$arg1$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$arg1$arg0$arg0  = \f$bool$f$arg1$arg0$arg0$conj [0:0] ;
  wire[0:0] \f$bool$f$arg1$arg0$arg1  = 1'd0 ;
  wire \f$bool$f$arg1$arg0  = \f$bool$f$arg1$arg0$arg0  == \f$bool$f$arg1$arg0$arg1  ;
  wire \f$bool$f$arg1  = !\f$bool$f$arg1$arg0  ;
  wire \f$bool$f  = \f$bool$f$arg0  && \f$bool$f$arg1  ;
  wire \f$bool  = \f$bool$f  ;
  wire[0:0] \f$true$content  = 1'd0 ;
  wire[0:0] \f$true  = \f$true$content  ;
  wire[1:0] \f$false$bool$g0  = \i0$data  ;
  wire[1:0] \f$false$bool$f$arg0$arg0$arg0$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$arg0$arg0$arg0$conj  = \f$false$bool$f$arg0$arg0$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$arg0$arg0$arg0  = \f$false$bool$f$arg0$arg0$arg0$arg0$conj [1:1] ;
  wire[0:0] \f$false$bool$f$arg0$arg0$arg0$arg1  = 1'd1 ;
  wire \f$false$bool$f$arg0$arg0$arg0  = \f$false$bool$f$arg0$arg0$arg0$arg0  == \f$false$bool$f$arg0$arg0$arg0$arg1  ;
  wire \f$false$bool$f$arg0$arg0  = !\f$false$bool$f$arg0$arg0$arg0  ;
  wire[1:0] \f$false$bool$f$arg0$arg1$arg0$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$arg1$arg0$arg0$conj  = \f$false$bool$f$arg0$arg1$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$arg1$arg0$arg0  = \f$false$bool$f$arg0$arg1$arg0$arg0$conj [0:0] ;
  wire[0:0] \f$false$bool$f$arg0$arg1$arg0$arg1  = 1'd0 ;
  wire \f$false$bool$f$arg0$arg1$arg0  = \f$false$bool$f$arg0$arg1$arg0$arg0  == \f$false$bool$f$arg0$arg1$arg0$arg1  ;
  wire \f$false$bool$f$arg0$arg1  = !\f$false$bool$f$arg0$arg1$arg0  ;
  wire \f$false$bool$f$arg0  = \f$false$bool$f$arg0$arg0  && \f$false$bool$f$arg0$arg1  ;
  wire \f$false$bool$f  = !\f$false$bool$f$arg0  ;
  wire \f$false$bool  = \f$false$bool$f  ;
  wire[0:0] \f$false$true$content  = 1'd1 ;
  wire[0:0] \f$false$true  = \f$false$true$content  ;
  wire[0:0] \f$false$false$content  = 1'd0 ;
  wire[0:0] \f$false$false  = \f$false$false$content  ;
  wire[0:0] \f$false  = ( \f$false$bool  ? \f$false$true  : \f$false$false  ) ;
  wire[0:0] \f  = ( \f$bool  ? \f$true  : \f$false  ) ;
  
  assign \o0  = \f  ;
endmodule

module \OFUN_1$BBB_1_0_2_2_3_2_Switch1 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , output [1:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[1:0] \f  = \i0$data  ;
  
  assign \o0  = \f  ;
endmodule

module \OFUN_2$BBB_1_0_2_2_3_2_Switch1 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , output [1:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[1:0] \f  = \i0$data  ;
  
  assign \o0  = \f  ;
endmodule

module \BBB_1_0_2_2_2_2 (
      input \clk , input \rst , input [63:0] \t 
    , input \bus_ins1$irdy , input [1:0] \bus_ins1$data , output \bus_ins1$trdy 
    , input \bus_ins2$irdy , input [1:0] \bus_ins2$data , output \bus_ins2$trdy 
    , input \bus_ins3$irdy , input [1:0] \bus_ins3$data , output \bus_ins3$trdy 
    , input \bus_ins4$irdy , input [0:0] \bus_ins4$data , output \bus_ins4$trdy 
    , output \bus_outs1$irdy , output [1:0] \bus_outs1$data , input \bus_outs1$trdy 
    , output \bus_outs2$irdy , output [1:0] \bus_outs2$data , input \bus_outs2$trdy 
    , output \bus_outs3$irdy , output [1:0] \bus_outs3$data , input \bus_outs3$trdy 
    , output \bus_outs4$irdy , output [0:0] \bus_outs4$data , input \bus_outs4$trdy 
    , input \Sink1$unbound_trdy 
    , output \Sink1$irdy 
    , output [1:0] \Sink1$data 
    , input \RECEPTION1$CreditCounter1$PatientSource1$unbound_irdy 
    , input [0:0] \RECEPTION1$CreditCounter1$PatientSource1$unbound_data 
    , output \RECEPTION1$CreditCounter1$PatientSource1$trdy 
    , input \RECEPTION1$CreditCounter1$Sink1$unbound_trdy 
    , output \RECEPTION1$CreditCounter1$Sink1$irdy 
    , output [0:0] \RECEPTION1$CreditCounter1$Sink1$data 
  );
  
  //
  // Channel declarations
  //
  wire \toEjection$irdy  ;
  wire [1:0] \toEjection$data  ;
  wire \toEjection$trdy  ;
  wire \toDFIFO$irdy  ;
  wire [1:0] \toDFIFO$data  ;
  wire \toDFIFO$trdy  ;
  wire \bypassLine$irdy  ;
  wire [1:0] \bypassLine$data  ;
  wire \bypassLine$trdy  ;
  wire \goodPkts$irdy  ;
  wire [1:0] \goodPkts$data  ;
  wire \goodPkts$trdy  ;
  wire \badPkts$irdy  ;
  wire [1:0] \badPkts$data  ;
  wire \badPkts$trdy  ;
  wire \channel1$irdy  ;
  wire [1:0] \channel1$data  ;
  wire \channel1$trdy  ;
  wire \channel2$irdy  ;
  wire \channel2$data  ;
  wire \channel2$trdy  ;
  
  //
  // Function Channels
  //
  wire \sfunchan_0_Switch1$data  ;
  wire [1:0] \ofunchan_1_Switch1$data  ;
  wire [1:0] \ofunchan_2_Switch1$data  ;
  
  //
  // Component and Macro instantiations
  //
  \Switch2  #(
    .OUTPUTSIZE0(2),
    .OUTPUTSIZE1(2),
    .INPUTSIZE(2)
  ) \Switch1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\bus_ins1$irdy )
    , .\i0$data (\bus_ins1$data )
    , .\i0$trdy (\bus_ins1$trdy )
    , .\o0$irdy (\goodPkts$irdy )
    , .\o0$data (\goodPkts$data )
    , .\o0$trdy (\goodPkts$trdy )
    , .\o1$irdy (\badPkts$irdy )
    , .\o1$data (\badPkts$data )
    , .\o1$trdy (\badPkts$trdy )
    , .\sel$data (\sfunchan_0_Switch1$data )
    , .\f0$data (\ofunchan_1_Switch1$data )
    , .\f1$data (\ofunchan_2_Switch1$data )
  );
  
  \SFUN_0$BBB_1_0_2_2_2_2_Switch1  \sfun_0_Switch1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\bus_ins1$data )
    , .\o0 (\sfunchan_0_Switch1$data )
  );
  
  \OFUN_1$BBB_1_0_2_2_2_2_Switch1  \ofun_1_Switch1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\bus_ins1$data )
    , .\o0 (\ofunchan_1_Switch1$data )
  );
  
  \OFUN_2$BBB_1_0_2_2_2_2_Switch1  \ofun_2_Switch1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\bus_ins1$data )
    , .\o0 (\ofunchan_2_Switch1$data )
  );
  
  assign \Sink1$irdy  = \badPkts$irdy  ;
  assign \Sink1$data  = \badPkts$data  ;
  \Sink  #(
    .DATASIZE(2)
  ) \Sink1  (
      .\clk (\clk ), .\rst (\rst ), .\t (\t )
    , .\i0$irdy (\badPkts$irdy )
    , .\i0$data (\badPkts$data )
    , .\i0$trdy (\badPkts$trdy )
    , .\unbound_trdy (\Sink1$unbound_trdy )
  );
  
  \CTRLJoin2  #(
    .INPUTSIZE1(1),
    .OUTPUTSIZE(2),
    .INPUTSIZE0(2)
  ) \CtrlJoin1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\channel1$irdy )
    , .\i0$data (\channel1$data )
    , .\i0$trdy (\channel1$trdy )
    , .\i1$irdy (\channel2$irdy )
    , .\i1$data (\channel2$data )
    , .\i1$trdy (\channel2$trdy )
    , .\o0$irdy (\bus_outs2$irdy )
    , .\o0$data (\bus_outs2$data )
    , .\o0$trdy (\bus_outs2$trdy )
  );
  
  \Queue  #(
    .NUM_DATA(0),
    .DATASIZE(1),
    .LENGTH(2)
  ) \Queue1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\bus_ins4$irdy )
    , .\i0$data (\bus_ins4$data )
    , .\i0$trdy (\bus_ins4$trdy )
    , .\o0$irdy (\channel2$irdy )
    , .\o0$data (\channel2$data )
    , .\o0$trdy (\channel2$trdy )
  );
  
  \RECEPTION_1_0_2_2  \RECEPTION1  (
      .\clk (\clk ), .\rst (\rst ), .\t (\t )
    , .\input$irdy (\bus_ins2$irdy )
    , .\input$data (\bus_ins2$data )
    , .\input$trdy (\bus_ins2$trdy )
    , .\bus_outs1$irdy (\bus_outs1$irdy )
    , .\bus_outs1$data (\bus_outs1$data )
    , .\bus_outs1$trdy (\bus_outs1$trdy )
    , .\bus_outs2$irdy (\bypassLine$irdy )
    , .\bus_outs2$data (\bypassLine$data )
    , .\bus_outs2$trdy (\bypassLine$trdy )
    , .\bus_outs3$irdy (\toDFIFO$irdy )
    , .\bus_outs3$data (\toDFIFO$data )
    , .\bus_outs3$trdy (\toDFIFO$trdy )
    , .\bus_outs4$irdy (\bus_outs4$irdy )
    , .\bus_outs4$data (\bus_outs4$data )
    , .\bus_outs4$trdy (\bus_outs4$trdy )
    , .\CreditCounter1$PatientSource1$unbound_irdy (\RECEPTION1$CreditCounter1$PatientSource1$unbound_irdy )
    , .\CreditCounter1$PatientSource1$unbound_data (\RECEPTION1$CreditCounter1$PatientSource1$unbound_data )
    , .\CreditCounter1$PatientSource1$trdy (\RECEPTION1$CreditCounter1$PatientSource1$trdy )
    , .\CreditCounter1$Sink1$unbound_trdy (\RECEPTION1$CreditCounter1$Sink1$unbound_trdy )
    , .\CreditCounter1$Sink1$irdy (\RECEPTION1$CreditCounter1$Sink1$irdy )
    , .\CreditCounter1$Sink1$data (\RECEPTION1$CreditCounter1$Sink1$data )
  );
  
  \DFIFO_2$type1  \DFIFO1  (
      .\clk (\clk ), .\rst (\rst )
    , .\bus_ins1$irdy (\toDFIFO$irdy )
    , .\bus_ins1$data (\toDFIFO$data )
    , .\bus_ins1$trdy (\toDFIFO$trdy )
    , .\bus_ins2$irdy (\bus_ins3$irdy )
    , .\bus_ins2$data (\bus_ins3$data )
    , .\bus_ins2$trdy (\bus_ins3$trdy )
    , .\bus_outs1$irdy (\bus_outs3$irdy )
    , .\bus_outs1$data (\bus_outs3$data )
    , .\bus_outs1$trdy (\bus_outs3$trdy )
    , .\bus_outs2$irdy (\toEjection$irdy )
    , .\bus_outs2$data (\toEjection$data )
    , .\bus_outs2$trdy (\toEjection$trdy )
  );
  
  \EJECTION_2$type3  \EJECTION1  (
      .\clk (\clk ), .\rst (\rst )
    , .\bus_ins1$irdy (\goodPkts$irdy )
    , .\bus_ins1$data (\goodPkts$data )
    , .\bus_ins1$trdy (\goodPkts$trdy )
    , .\bus_ins2$irdy (\bypassLine$irdy )
    , .\bus_ins2$data (\bypassLine$data )
    , .\bus_ins2$trdy (\bypassLine$trdy )
    , .\bus_ins3$irdy (\toEjection$irdy )
    , .\bus_ins3$data (\toEjection$data )
    , .\bus_ins3$trdy (\toEjection$trdy )
    , .\output$irdy (\channel1$irdy )
    , .\output$data (\channel1$data )
    , .\output$trdy (\channel1$trdy )
  );
  
endmodule


//
// BBB_1_0_2_2_2_2 switch functions
//
module \SFUN_0$BBB_1_0_2_2_2_2_Switch1 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , output [0:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[1:0] \f$bool$g0  = \i0$data  ;
  wire[1:0] \f$bool$f$arg0$arg0$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$arg0$arg0$arg0$conj  = \f$bool$f$arg0$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$arg0$arg0$arg0  = \f$bool$f$arg0$arg0$arg0$conj [1:1] ;
  wire[0:0] \f$bool$f$arg0$arg0$arg1  = 1'd1 ;
  wire \f$bool$f$arg0$arg0  = \f$bool$f$arg0$arg0$arg0  == \f$bool$f$arg0$arg0$arg1  ;
  wire \f$bool$f$arg0  = !\f$bool$f$arg0$arg0  ;
  wire[1:0] \f$bool$f$arg1$arg0$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$arg1$arg0$arg0$conj  = \f$bool$f$arg1$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$arg1$arg0$arg0  = \f$bool$f$arg1$arg0$arg0$conj [0:0] ;
  wire[0:0] \f$bool$f$arg1$arg0$arg1  = 1'd0 ;
  wire \f$bool$f$arg1$arg0  = \f$bool$f$arg1$arg0$arg0  == \f$bool$f$arg1$arg0$arg1  ;
  wire \f$bool$f$arg1  = !\f$bool$f$arg1$arg0  ;
  wire \f$bool$f  = \f$bool$f$arg0  && \f$bool$f$arg1  ;
  wire \f$bool  = \f$bool$f  ;
  wire[0:0] \f$true$content  = 1'd0 ;
  wire[0:0] \f$true  = \f$true$content  ;
  wire[1:0] \f$false$bool$g0  = \i0$data  ;
  wire[1:0] \f$false$bool$f$arg0$arg0$arg0$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$arg0$arg0$arg0$conj  = \f$false$bool$f$arg0$arg0$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$arg0$arg0$arg0  = \f$false$bool$f$arg0$arg0$arg0$arg0$conj [1:1] ;
  wire[0:0] \f$false$bool$f$arg0$arg0$arg0$arg1  = 1'd1 ;
  wire \f$false$bool$f$arg0$arg0$arg0  = \f$false$bool$f$arg0$arg0$arg0$arg0  == \f$false$bool$f$arg0$arg0$arg0$arg1  ;
  wire \f$false$bool$f$arg0$arg0  = !\f$false$bool$f$arg0$arg0$arg0  ;
  wire[1:0] \f$false$bool$f$arg0$arg1$arg0$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$arg1$arg0$arg0$conj  = \f$false$bool$f$arg0$arg1$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$arg1$arg0$arg0  = \f$false$bool$f$arg0$arg1$arg0$arg0$conj [0:0] ;
  wire[0:0] \f$false$bool$f$arg0$arg1$arg0$arg1  = 1'd0 ;
  wire \f$false$bool$f$arg0$arg1$arg0  = \f$false$bool$f$arg0$arg1$arg0$arg0  == \f$false$bool$f$arg0$arg1$arg0$arg1  ;
  wire \f$false$bool$f$arg0$arg1  = !\f$false$bool$f$arg0$arg1$arg0  ;
  wire \f$false$bool$f$arg0  = \f$false$bool$f$arg0$arg0  && \f$false$bool$f$arg0$arg1  ;
  wire \f$false$bool$f  = !\f$false$bool$f$arg0  ;
  wire \f$false$bool  = \f$false$bool$f  ;
  wire[0:0] \f$false$true$content  = 1'd1 ;
  wire[0:0] \f$false$true  = \f$false$true$content  ;
  wire[0:0] \f$false$false$content  = 1'd0 ;
  wire[0:0] \f$false$false  = \f$false$false$content  ;
  wire[0:0] \f$false  = ( \f$false$bool  ? \f$false$true  : \f$false$false  ) ;
  wire[0:0] \f  = ( \f$bool  ? \f$true  : \f$false  ) ;
  
  assign \o0  = \f  ;
endmodule

module \OFUN_1$BBB_1_0_2_2_2_2_Switch1 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , output [1:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[1:0] \f  = \i0$data  ;
  
  assign \o0  = \f  ;
endmodule

module \OFUN_2$BBB_1_0_2_2_2_2_Switch1 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , output [1:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[1:0] \f  = \i0$data  ;
  
  assign \o0  = \f  ;
endmodule

module \BBB_0_0_2_2_2_2 (
      input \clk , input \rst , input [63:0] \t 
    , input \bus_ins1$irdy , input [1:0] \bus_ins1$data , output \bus_ins1$trdy 
    , input \bus_ins2$irdy , input [1:0] \bus_ins2$data , output \bus_ins2$trdy 
    , input \bus_ins3$irdy , input [1:0] \bus_ins3$data , output \bus_ins3$trdy 
    , input \bus_ins4$irdy , input [0:0] \bus_ins4$data , output \bus_ins4$trdy 
    , output \bus_outs1$irdy , output [1:0] \bus_outs1$data , input \bus_outs1$trdy 
    , output \bus_outs2$irdy , output [1:0] \bus_outs2$data , input \bus_outs2$trdy 
    , output \bus_outs3$irdy , output [1:0] \bus_outs3$data , input \bus_outs3$trdy 
    , output \bus_outs4$irdy , output [0:0] \bus_outs4$data , input \bus_outs4$trdy 
    , input \Sink1$unbound_trdy 
    , output \Sink1$irdy 
    , output [1:0] \Sink1$data 
    , input \RECEPTION1$CreditCounter1$PatientSource1$unbound_irdy 
    , input [0:0] \RECEPTION1$CreditCounter1$PatientSource1$unbound_data 
    , output \RECEPTION1$CreditCounter1$PatientSource1$trdy 
    , input \RECEPTION1$CreditCounter1$Sink1$unbound_trdy 
    , output \RECEPTION1$CreditCounter1$Sink1$irdy 
    , output [0:0] \RECEPTION1$CreditCounter1$Sink1$data 
  );
  
  //
  // Channel declarations
  //
  wire \toEjection$irdy  ;
  wire [1:0] \toEjection$data  ;
  wire \toEjection$trdy  ;
  wire \toDFIFO$irdy  ;
  wire [1:0] \toDFIFO$data  ;
  wire \toDFIFO$trdy  ;
  wire \bypassLine$irdy  ;
  wire [1:0] \bypassLine$data  ;
  wire \bypassLine$trdy  ;
  wire \goodPkts$irdy  ;
  wire [1:0] \goodPkts$data  ;
  wire \goodPkts$trdy  ;
  wire \badPkts$irdy  ;
  wire [1:0] \badPkts$data  ;
  wire \badPkts$trdy  ;
  wire \channel1$irdy  ;
  wire [1:0] \channel1$data  ;
  wire \channel1$trdy  ;
  wire \channel2$irdy  ;
  wire \channel2$data  ;
  wire \channel2$trdy  ;
  
  //
  // Function Channels
  //
  wire \sfunchan_0_Switch1$data  ;
  wire [1:0] \ofunchan_1_Switch1$data  ;
  wire [1:0] \ofunchan_2_Switch1$data  ;
  
  //
  // Component and Macro instantiations
  //
  \Switch2  #(
    .OUTPUTSIZE0(2),
    .OUTPUTSIZE1(2),
    .INPUTSIZE(2)
  ) \Switch1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\bus_ins1$irdy )
    , .\i0$data (\bus_ins1$data )
    , .\i0$trdy (\bus_ins1$trdy )
    , .\o0$irdy (\goodPkts$irdy )
    , .\o0$data (\goodPkts$data )
    , .\o0$trdy (\goodPkts$trdy )
    , .\o1$irdy (\badPkts$irdy )
    , .\o1$data (\badPkts$data )
    , .\o1$trdy (\badPkts$trdy )
    , .\sel$data (\sfunchan_0_Switch1$data )
    , .\f0$data (\ofunchan_1_Switch1$data )
    , .\f1$data (\ofunchan_2_Switch1$data )
  );
  
  \SFUN_0$BBB_0_0_2_2_2_2_Switch1  \sfun_0_Switch1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\bus_ins1$data )
    , .\o0 (\sfunchan_0_Switch1$data )
  );
  
  \OFUN_1$BBB_0_0_2_2_2_2_Switch1  \ofun_1_Switch1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\bus_ins1$data )
    , .\o0 (\ofunchan_1_Switch1$data )
  );
  
  \OFUN_2$BBB_0_0_2_2_2_2_Switch1  \ofun_2_Switch1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\bus_ins1$data )
    , .\o0 (\ofunchan_2_Switch1$data )
  );
  
  assign \Sink1$irdy  = \badPkts$irdy  ;
  assign \Sink1$data  = \badPkts$data  ;
  \Sink  #(
    .DATASIZE(2)
  ) \Sink1  (
      .\clk (\clk ), .\rst (\rst ), .\t (\t )
    , .\i0$irdy (\badPkts$irdy )
    , .\i0$data (\badPkts$data )
    , .\i0$trdy (\badPkts$trdy )
    , .\unbound_trdy (\Sink1$unbound_trdy )
  );
  
  \CTRLJoin2  #(
    .INPUTSIZE1(1),
    .OUTPUTSIZE(2),
    .INPUTSIZE0(2)
  ) \CtrlJoin1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\channel1$irdy )
    , .\i0$data (\channel1$data )
    , .\i0$trdy (\channel1$trdy )
    , .\i1$irdy (\channel2$irdy )
    , .\i1$data (\channel2$data )
    , .\i1$trdy (\channel2$trdy )
    , .\o0$irdy (\bus_outs2$irdy )
    , .\o0$data (\bus_outs2$data )
    , .\o0$trdy (\bus_outs2$trdy )
  );
  
  \Queue  #(
    .NUM_DATA(0),
    .DATASIZE(1),
    .LENGTH(2)
  ) \Queue1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\bus_ins4$irdy )
    , .\i0$data (\bus_ins4$data )
    , .\i0$trdy (\bus_ins4$trdy )
    , .\o0$irdy (\channel2$irdy )
    , .\o0$data (\channel2$data )
    , .\o0$trdy (\channel2$trdy )
  );
  
  \RECEPTION_0_0_2_2  \RECEPTION1  (
      .\clk (\clk ), .\rst (\rst ), .\t (\t )
    , .\input$irdy (\bus_ins2$irdy )
    , .\input$data (\bus_ins2$data )
    , .\input$trdy (\bus_ins2$trdy )
    , .\bus_outs1$irdy (\bus_outs1$irdy )
    , .\bus_outs1$data (\bus_outs1$data )
    , .\bus_outs1$trdy (\bus_outs1$trdy )
    , .\bus_outs2$irdy (\bypassLine$irdy )
    , .\bus_outs2$data (\bypassLine$data )
    , .\bus_outs2$trdy (\bypassLine$trdy )
    , .\bus_outs3$irdy (\toDFIFO$irdy )
    , .\bus_outs3$data (\toDFIFO$data )
    , .\bus_outs3$trdy (\toDFIFO$trdy )
    , .\bus_outs4$irdy (\bus_outs4$irdy )
    , .\bus_outs4$data (\bus_outs4$data )
    , .\bus_outs4$trdy (\bus_outs4$trdy )
    , .\CreditCounter1$PatientSource1$unbound_irdy (\RECEPTION1$CreditCounter1$PatientSource1$unbound_irdy )
    , .\CreditCounter1$PatientSource1$unbound_data (\RECEPTION1$CreditCounter1$PatientSource1$unbound_data )
    , .\CreditCounter1$PatientSource1$trdy (\RECEPTION1$CreditCounter1$PatientSource1$trdy )
    , .\CreditCounter1$Sink1$unbound_trdy (\RECEPTION1$CreditCounter1$Sink1$unbound_trdy )
    , .\CreditCounter1$Sink1$irdy (\RECEPTION1$CreditCounter1$Sink1$irdy )
    , .\CreditCounter1$Sink1$data (\RECEPTION1$CreditCounter1$Sink1$data )
  );
  
  \DFIFO_2$type1  \DFIFO1  (
      .\clk (\clk ), .\rst (\rst )
    , .\bus_ins1$irdy (\toDFIFO$irdy )
    , .\bus_ins1$data (\toDFIFO$data )
    , .\bus_ins1$trdy (\toDFIFO$trdy )
    , .\bus_ins2$irdy (\bus_ins3$irdy )
    , .\bus_ins2$data (\bus_ins3$data )
    , .\bus_ins2$trdy (\bus_ins3$trdy )
    , .\bus_outs1$irdy (\bus_outs3$irdy )
    , .\bus_outs1$data (\bus_outs3$data )
    , .\bus_outs1$trdy (\bus_outs3$trdy )
    , .\bus_outs2$irdy (\toEjection$irdy )
    , .\bus_outs2$data (\toEjection$data )
    , .\bus_outs2$trdy (\toEjection$trdy )
  );
  
  \EJECTION_2$type6  \EJECTION1  (
      .\clk (\clk ), .\rst (\rst )
    , .\bus_ins1$irdy (\goodPkts$irdy )
    , .\bus_ins1$data (\goodPkts$data )
    , .\bus_ins1$trdy (\goodPkts$trdy )
    , .\bus_ins2$irdy (\bypassLine$irdy )
    , .\bus_ins2$data (\bypassLine$data )
    , .\bus_ins2$trdy (\bypassLine$trdy )
    , .\bus_ins3$irdy (\toEjection$irdy )
    , .\bus_ins3$data (\toEjection$data )
    , .\bus_ins3$trdy (\toEjection$trdy )
    , .\output$irdy (\channel1$irdy )
    , .\output$data (\channel1$data )
    , .\output$trdy (\channel1$trdy )
  );
  
endmodule


//
// BBB_0_0_2_2_2_2 switch functions
//
module \SFUN_0$BBB_0_0_2_2_2_2_Switch1 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , output [0:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[1:0] \f$bool$g0  = \i0$data  ;
  wire[1:0] \f$bool$f$arg0$arg0$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$arg0$arg0$arg0$conj  = \f$bool$f$arg0$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$arg0$arg0$arg0  = \f$bool$f$arg0$arg0$arg0$conj [1:1] ;
  wire[0:0] \f$bool$f$arg0$arg0$arg1  = 1'd0 ;
  wire \f$bool$f$arg0$arg0  = \f$bool$f$arg0$arg0$arg0  == \f$bool$f$arg0$arg0$arg1  ;
  wire \f$bool$f$arg0  = !\f$bool$f$arg0$arg0  ;
  wire[1:0] \f$bool$f$arg1$arg0$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$arg1$arg0$arg0$conj  = \f$bool$f$arg1$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$arg1$arg0$arg0  = \f$bool$f$arg1$arg0$arg0$conj [0:0] ;
  wire[0:0] \f$bool$f$arg1$arg0$arg1  = 1'd0 ;
  wire \f$bool$f$arg1$arg0  = \f$bool$f$arg1$arg0$arg0  == \f$bool$f$arg1$arg0$arg1  ;
  wire \f$bool$f$arg1  = !\f$bool$f$arg1$arg0  ;
  wire \f$bool$f  = \f$bool$f$arg0  && \f$bool$f$arg1  ;
  wire \f$bool  = \f$bool$f  ;
  wire[0:0] \f$true$content  = 1'd0 ;
  wire[0:0] \f$true  = \f$true$content  ;
  wire[1:0] \f$false$bool$g0  = \i0$data  ;
  wire[1:0] \f$false$bool$f$arg0$arg0$arg0$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$arg0$arg0$arg0$conj  = \f$false$bool$f$arg0$arg0$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$arg0$arg0$arg0  = \f$false$bool$f$arg0$arg0$arg0$arg0$conj [1:1] ;
  wire[0:0] \f$false$bool$f$arg0$arg0$arg0$arg1  = 1'd0 ;
  wire \f$false$bool$f$arg0$arg0$arg0  = \f$false$bool$f$arg0$arg0$arg0$arg0  == \f$false$bool$f$arg0$arg0$arg0$arg1  ;
  wire \f$false$bool$f$arg0$arg0  = !\f$false$bool$f$arg0$arg0$arg0  ;
  wire[1:0] \f$false$bool$f$arg0$arg1$arg0$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$arg1$arg0$arg0$conj  = \f$false$bool$f$arg0$arg1$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$arg1$arg0$arg0  = \f$false$bool$f$arg0$arg1$arg0$arg0$conj [0:0] ;
  wire[0:0] \f$false$bool$f$arg0$arg1$arg0$arg1  = 1'd0 ;
  wire \f$false$bool$f$arg0$arg1$arg0  = \f$false$bool$f$arg0$arg1$arg0$arg0  == \f$false$bool$f$arg0$arg1$arg0$arg1  ;
  wire \f$false$bool$f$arg0$arg1  = !\f$false$bool$f$arg0$arg1$arg0  ;
  wire \f$false$bool$f$arg0  = \f$false$bool$f$arg0$arg0  && \f$false$bool$f$arg0$arg1  ;
  wire \f$false$bool$f  = !\f$false$bool$f$arg0  ;
  wire \f$false$bool  = \f$false$bool$f  ;
  wire[0:0] \f$false$true$content  = 1'd1 ;
  wire[0:0] \f$false$true  = \f$false$true$content  ;
  wire[0:0] \f$false$false$content  = 1'd0 ;
  wire[0:0] \f$false$false  = \f$false$false$content  ;
  wire[0:0] \f$false  = ( \f$false$bool  ? \f$false$true  : \f$false$false  ) ;
  wire[0:0] \f  = ( \f$bool  ? \f$true  : \f$false  ) ;
  
  assign \o0  = \f  ;
endmodule

module \OFUN_1$BBB_0_0_2_2_2_2_Switch1 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , output [1:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[1:0] \f  = \i0$data  ;
  
  assign \o0  = \f  ;
endmodule

module \OFUN_2$BBB_0_0_2_2_2_2_Switch1 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , output [1:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[1:0] \f  = \i0$data  ;
  
  assign \o0  = \f  ;
endmodule

module \BBB_0_0_2_2_3_2 (
      input \clk , input \rst , input [63:0] \t 
    , input \bus_ins1$irdy , input [1:0] \bus_ins1$data , output \bus_ins1$trdy 
    , input \bus_ins2$irdy , input [1:0] \bus_ins2$data , output \bus_ins2$trdy 
    , input \bus_ins3$irdy , input [1:0] \bus_ins3$data , output \bus_ins3$trdy 
    , input \bus_ins4$irdy , input [0:0] \bus_ins4$data , output \bus_ins4$trdy 
    , output \bus_outs1$irdy , output [1:0] \bus_outs1$data , input \bus_outs1$trdy 
    , output \bus_outs2$irdy , output [1:0] \bus_outs2$data , input \bus_outs2$trdy 
    , output \bus_outs3$irdy , output [1:0] \bus_outs3$data , input \bus_outs3$trdy 
    , output \bus_outs4$irdy , output [0:0] \bus_outs4$data , input \bus_outs4$trdy 
    , input \Sink1$unbound_trdy 
    , output \Sink1$irdy 
    , output [1:0] \Sink1$data 
    , input \RECEPTION1$CreditCounter1$PatientSource1$unbound_irdy 
    , input [0:0] \RECEPTION1$CreditCounter1$PatientSource1$unbound_data 
    , output \RECEPTION1$CreditCounter1$PatientSource1$trdy 
    , input \RECEPTION1$CreditCounter1$Sink1$unbound_trdy 
    , output \RECEPTION1$CreditCounter1$Sink1$irdy 
    , output [0:0] \RECEPTION1$CreditCounter1$Sink1$data 
  );
  
  //
  // Channel declarations
  //
  wire \toEjection$irdy  ;
  wire [1:0] \toEjection$data  ;
  wire \toEjection$trdy  ;
  wire \toDFIFO$irdy  ;
  wire [1:0] \toDFIFO$data  ;
  wire \toDFIFO$trdy  ;
  wire \bypassLine$irdy  ;
  wire [1:0] \bypassLine$data  ;
  wire \bypassLine$trdy  ;
  wire \goodPkts$irdy  ;
  wire [1:0] \goodPkts$data  ;
  wire \goodPkts$trdy  ;
  wire \badPkts$irdy  ;
  wire [1:0] \badPkts$data  ;
  wire \badPkts$trdy  ;
  wire \channel1$irdy  ;
  wire [1:0] \channel1$data  ;
  wire \channel1$trdy  ;
  wire \channel2$irdy  ;
  wire \channel2$data  ;
  wire \channel2$trdy  ;
  
  //
  // Function Channels
  //
  wire \sfunchan_0_Switch1$data  ;
  wire [1:0] \ofunchan_1_Switch1$data  ;
  wire [1:0] \ofunchan_2_Switch1$data  ;
  
  //
  // Component and Macro instantiations
  //
  \Switch2  #(
    .OUTPUTSIZE0(2),
    .OUTPUTSIZE1(2),
    .INPUTSIZE(2)
  ) \Switch1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\bus_ins1$irdy )
    , .\i0$data (\bus_ins1$data )
    , .\i0$trdy (\bus_ins1$trdy )
    , .\o0$irdy (\goodPkts$irdy )
    , .\o0$data (\goodPkts$data )
    , .\o0$trdy (\goodPkts$trdy )
    , .\o1$irdy (\badPkts$irdy )
    , .\o1$data (\badPkts$data )
    , .\o1$trdy (\badPkts$trdy )
    , .\sel$data (\sfunchan_0_Switch1$data )
    , .\f0$data (\ofunchan_1_Switch1$data )
    , .\f1$data (\ofunchan_2_Switch1$data )
  );
  
  \SFUN_0$BBB_0_0_2_2_3_2_Switch1  \sfun_0_Switch1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\bus_ins1$data )
    , .\o0 (\sfunchan_0_Switch1$data )
  );
  
  \OFUN_1$BBB_0_0_2_2_3_2_Switch1  \ofun_1_Switch1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\bus_ins1$data )
    , .\o0 (\ofunchan_1_Switch1$data )
  );
  
  \OFUN_2$BBB_0_0_2_2_3_2_Switch1  \ofun_2_Switch1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\bus_ins1$data )
    , .\o0 (\ofunchan_2_Switch1$data )
  );
  
  assign \Sink1$irdy  = \badPkts$irdy  ;
  assign \Sink1$data  = \badPkts$data  ;
  \Sink  #(
    .DATASIZE(2)
  ) \Sink1  (
      .\clk (\clk ), .\rst (\rst ), .\t (\t )
    , .\i0$irdy (\badPkts$irdy )
    , .\i0$data (\badPkts$data )
    , .\i0$trdy (\badPkts$trdy )
    , .\unbound_trdy (\Sink1$unbound_trdy )
  );
  
  \CTRLJoin2  #(
    .INPUTSIZE1(1),
    .OUTPUTSIZE(2),
    .INPUTSIZE0(2)
  ) \CtrlJoin1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\channel1$irdy )
    , .\i0$data (\channel1$data )
    , .\i0$trdy (\channel1$trdy )
    , .\i1$irdy (\channel2$irdy )
    , .\i1$data (\channel2$data )
    , .\i1$trdy (\channel2$trdy )
    , .\o0$irdy (\bus_outs2$irdy )
    , .\o0$data (\bus_outs2$data )
    , .\o0$trdy (\bus_outs2$trdy )
  );
  
  \Queue  #(
    .NUM_DATA(0),
    .DATASIZE(1),
    .LENGTH(2)
  ) \Queue1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\bus_ins4$irdy )
    , .\i0$data (\bus_ins4$data )
    , .\i0$trdy (\bus_ins4$trdy )
    , .\o0$irdy (\channel2$irdy )
    , .\o0$data (\channel2$data )
    , .\o0$trdy (\channel2$trdy )
  );
  
  \RECEPTION_0_0_3_2  \RECEPTION1  (
      .\clk (\clk ), .\rst (\rst ), .\t (\t )
    , .\input$irdy (\bus_ins2$irdy )
    , .\input$data (\bus_ins2$data )
    , .\input$trdy (\bus_ins2$trdy )
    , .\bus_outs1$irdy (\bus_outs1$irdy )
    , .\bus_outs1$data (\bus_outs1$data )
    , .\bus_outs1$trdy (\bus_outs1$trdy )
    , .\bus_outs2$irdy (\bypassLine$irdy )
    , .\bus_outs2$data (\bypassLine$data )
    , .\bus_outs2$trdy (\bypassLine$trdy )
    , .\bus_outs3$irdy (\toDFIFO$irdy )
    , .\bus_outs3$data (\toDFIFO$data )
    , .\bus_outs3$trdy (\toDFIFO$trdy )
    , .\bus_outs4$irdy (\bus_outs4$irdy )
    , .\bus_outs4$data (\bus_outs4$data )
    , .\bus_outs4$trdy (\bus_outs4$trdy )
    , .\CreditCounter1$PatientSource1$unbound_irdy (\RECEPTION1$CreditCounter1$PatientSource1$unbound_irdy )
    , .\CreditCounter1$PatientSource1$unbound_data (\RECEPTION1$CreditCounter1$PatientSource1$unbound_data )
    , .\CreditCounter1$PatientSource1$trdy (\RECEPTION1$CreditCounter1$PatientSource1$trdy )
    , .\CreditCounter1$Sink1$unbound_trdy (\RECEPTION1$CreditCounter1$Sink1$unbound_trdy )
    , .\CreditCounter1$Sink1$irdy (\RECEPTION1$CreditCounter1$Sink1$irdy )
    , .\CreditCounter1$Sink1$data (\RECEPTION1$CreditCounter1$Sink1$data )
  );
  
  \DFIFO_2$type1  \DFIFO1  (
      .\clk (\clk ), .\rst (\rst )
    , .\bus_ins1$irdy (\toDFIFO$irdy )
    , .\bus_ins1$data (\toDFIFO$data )
    , .\bus_ins1$trdy (\toDFIFO$trdy )
    , .\bus_ins2$irdy (\bus_ins3$irdy )
    , .\bus_ins2$data (\bus_ins3$data )
    , .\bus_ins2$trdy (\bus_ins3$trdy )
    , .\bus_outs1$irdy (\bus_outs3$irdy )
    , .\bus_outs1$data (\bus_outs3$data )
    , .\bus_outs1$trdy (\bus_outs3$trdy )
    , .\bus_outs2$irdy (\toEjection$irdy )
    , .\bus_outs2$data (\toEjection$data )
    , .\bus_outs2$trdy (\toEjection$trdy )
  );
  
  \EJECTION_2$type6  \EJECTION1  (
      .\clk (\clk ), .\rst (\rst )
    , .\bus_ins1$irdy (\goodPkts$irdy )
    , .\bus_ins1$data (\goodPkts$data )
    , .\bus_ins1$trdy (\goodPkts$trdy )
    , .\bus_ins2$irdy (\bypassLine$irdy )
    , .\bus_ins2$data (\bypassLine$data )
    , .\bus_ins2$trdy (\bypassLine$trdy )
    , .\bus_ins3$irdy (\toEjection$irdy )
    , .\bus_ins3$data (\toEjection$data )
    , .\bus_ins3$trdy (\toEjection$trdy )
    , .\output$irdy (\channel1$irdy )
    , .\output$data (\channel1$data )
    , .\output$trdy (\channel1$trdy )
  );
  
endmodule


//
// BBB_0_0_2_2_3_2 switch functions
//
module \SFUN_0$BBB_0_0_2_2_3_2_Switch1 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , output [0:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[1:0] \f$bool$g0  = \i0$data  ;
  wire[1:0] \f$bool$f$arg0$arg0$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$arg0$arg0$arg0$conj  = \f$bool$f$arg0$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$arg0$arg0$arg0  = \f$bool$f$arg0$arg0$arg0$conj [1:1] ;
  wire[0:0] \f$bool$f$arg0$arg0$arg1  = 1'd0 ;
  wire \f$bool$f$arg0$arg0  = \f$bool$f$arg0$arg0$arg0  == \f$bool$f$arg0$arg0$arg1  ;
  wire \f$bool$f$arg0  = !\f$bool$f$arg0$arg0  ;
  wire[1:0] \f$bool$f$arg1$arg0$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$arg1$arg0$arg0$conj  = \f$bool$f$arg1$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$arg1$arg0$arg0  = \f$bool$f$arg1$arg0$arg0$conj [0:0] ;
  wire[0:0] \f$bool$f$arg1$arg0$arg1  = 1'd0 ;
  wire \f$bool$f$arg1$arg0  = \f$bool$f$arg1$arg0$arg0  == \f$bool$f$arg1$arg0$arg1  ;
  wire \f$bool$f$arg1  = !\f$bool$f$arg1$arg0  ;
  wire \f$bool$f  = \f$bool$f$arg0  && \f$bool$f$arg1  ;
  wire \f$bool  = \f$bool$f  ;
  wire[0:0] \f$true$content  = 1'd0 ;
  wire[0:0] \f$true  = \f$true$content  ;
  wire[1:0] \f$false$bool$g0  = \i0$data  ;
  wire[1:0] \f$false$bool$f$arg0$arg0$arg0$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$arg0$arg0$arg0$conj  = \f$false$bool$f$arg0$arg0$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$arg0$arg0$arg0  = \f$false$bool$f$arg0$arg0$arg0$arg0$conj [1:1] ;
  wire[0:0] \f$false$bool$f$arg0$arg0$arg0$arg1  = 1'd0 ;
  wire \f$false$bool$f$arg0$arg0$arg0  = \f$false$bool$f$arg0$arg0$arg0$arg0  == \f$false$bool$f$arg0$arg0$arg0$arg1  ;
  wire \f$false$bool$f$arg0$arg0  = !\f$false$bool$f$arg0$arg0$arg0  ;
  wire[1:0] \f$false$bool$f$arg0$arg1$arg0$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$arg1$arg0$arg0$conj  = \f$false$bool$f$arg0$arg1$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$arg1$arg0$arg0  = \f$false$bool$f$arg0$arg1$arg0$arg0$conj [0:0] ;
  wire[0:0] \f$false$bool$f$arg0$arg1$arg0$arg1  = 1'd0 ;
  wire \f$false$bool$f$arg0$arg1$arg0  = \f$false$bool$f$arg0$arg1$arg0$arg0  == \f$false$bool$f$arg0$arg1$arg0$arg1  ;
  wire \f$false$bool$f$arg0$arg1  = !\f$false$bool$f$arg0$arg1$arg0  ;
  wire \f$false$bool$f$arg0  = \f$false$bool$f$arg0$arg0  && \f$false$bool$f$arg0$arg1  ;
  wire \f$false$bool$f  = !\f$false$bool$f$arg0  ;
  wire \f$false$bool  = \f$false$bool$f  ;
  wire[0:0] \f$false$true$content  = 1'd1 ;
  wire[0:0] \f$false$true  = \f$false$true$content  ;
  wire[0:0] \f$false$false$content  = 1'd0 ;
  wire[0:0] \f$false$false  = \f$false$false$content  ;
  wire[0:0] \f$false  = ( \f$false$bool  ? \f$false$true  : \f$false$false  ) ;
  wire[0:0] \f  = ( \f$bool  ? \f$true  : \f$false  ) ;
  
  assign \o0  = \f  ;
endmodule

module \OFUN_1$BBB_0_0_2_2_3_2_Switch1 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , output [1:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[1:0] \f  = \i0$data  ;
  
  assign \o0  = \f  ;
endmodule

module \OFUN_2$BBB_0_0_2_2_3_2_Switch1 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , output [1:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[1:0] \f  = \i0$data  ;
  
  assign \o0  = \f  ;
endmodule

module \BBB_1_1_2_2_0_2 (
      input \clk , input \rst , input [63:0] \t 
    , input \bus_ins1$irdy , input [1:0] \bus_ins1$data , output \bus_ins1$trdy 
    , input \bus_ins2$irdy , input [1:0] \bus_ins2$data , output \bus_ins2$trdy 
    , input \bus_ins3$irdy , input [1:0] \bus_ins3$data , output \bus_ins3$trdy 
    , input \bus_ins4$irdy , input [0:0] \bus_ins4$data , output \bus_ins4$trdy 
    , output \bus_outs1$irdy , output [1:0] \bus_outs1$data , input \bus_outs1$trdy 
    , output \bus_outs2$irdy , output [1:0] \bus_outs2$data , input \bus_outs2$trdy 
    , output \bus_outs3$irdy , output [1:0] \bus_outs3$data , input \bus_outs3$trdy 
    , output \bus_outs4$irdy , output [0:0] \bus_outs4$data , input \bus_outs4$trdy 
    , input \Sink1$unbound_trdy 
    , output \Sink1$irdy 
    , output [1:0] \Sink1$data 
    , input \RECEPTION1$CreditCounter1$PatientSource1$unbound_irdy 
    , input [0:0] \RECEPTION1$CreditCounter1$PatientSource1$unbound_data 
    , output \RECEPTION1$CreditCounter1$PatientSource1$trdy 
    , input \RECEPTION1$CreditCounter1$Sink1$unbound_trdy 
    , output \RECEPTION1$CreditCounter1$Sink1$irdy 
    , output [0:0] \RECEPTION1$CreditCounter1$Sink1$data 
  );
  
  //
  // Channel declarations
  //
  wire \toEjection$irdy  ;
  wire [1:0] \toEjection$data  ;
  wire \toEjection$trdy  ;
  wire \toDFIFO$irdy  ;
  wire [1:0] \toDFIFO$data  ;
  wire \toDFIFO$trdy  ;
  wire \bypassLine$irdy  ;
  wire [1:0] \bypassLine$data  ;
  wire \bypassLine$trdy  ;
  wire \goodPkts$irdy  ;
  wire [1:0] \goodPkts$data  ;
  wire \goodPkts$trdy  ;
  wire \badPkts$irdy  ;
  wire [1:0] \badPkts$data  ;
  wire \badPkts$trdy  ;
  wire \channel1$irdy  ;
  wire [1:0] \channel1$data  ;
  wire \channel1$trdy  ;
  wire \channel2$irdy  ;
  wire \channel2$data  ;
  wire \channel2$trdy  ;
  
  //
  // Function Channels
  //
  wire \sfunchan_0_Switch1$data  ;
  wire [1:0] \ofunchan_1_Switch1$data  ;
  wire [1:0] \ofunchan_2_Switch1$data  ;
  
  //
  // Component and Macro instantiations
  //
  \Switch2  #(
    .OUTPUTSIZE0(2),
    .OUTPUTSIZE1(2),
    .INPUTSIZE(2)
  ) \Switch1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\bus_ins1$irdy )
    , .\i0$data (\bus_ins1$data )
    , .\i0$trdy (\bus_ins1$trdy )
    , .\o0$irdy (\goodPkts$irdy )
    , .\o0$data (\goodPkts$data )
    , .\o0$trdy (\goodPkts$trdy )
    , .\o1$irdy (\badPkts$irdy )
    , .\o1$data (\badPkts$data )
    , .\o1$trdy (\badPkts$trdy )
    , .\sel$data (\sfunchan_0_Switch1$data )
    , .\f0$data (\ofunchan_1_Switch1$data )
    , .\f1$data (\ofunchan_2_Switch1$data )
  );
  
  \SFUN_0$BBB_1_1_2_2_0_2_Switch1  \sfun_0_Switch1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\bus_ins1$data )
    , .\o0 (\sfunchan_0_Switch1$data )
  );
  
  \OFUN_1$BBB_1_1_2_2_0_2_Switch1  \ofun_1_Switch1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\bus_ins1$data )
    , .\o0 (\ofunchan_1_Switch1$data )
  );
  
  \OFUN_2$BBB_1_1_2_2_0_2_Switch1  \ofun_2_Switch1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\bus_ins1$data )
    , .\o0 (\ofunchan_2_Switch1$data )
  );
  
  assign \Sink1$irdy  = \badPkts$irdy  ;
  assign \Sink1$data  = \badPkts$data  ;
  \Sink  #(
    .DATASIZE(2)
  ) \Sink1  (
      .\clk (\clk ), .\rst (\rst ), .\t (\t )
    , .\i0$irdy (\badPkts$irdy )
    , .\i0$data (\badPkts$data )
    , .\i0$trdy (\badPkts$trdy )
    , .\unbound_trdy (\Sink1$unbound_trdy )
  );
  
  \CTRLJoin2  #(
    .INPUTSIZE1(1),
    .OUTPUTSIZE(2),
    .INPUTSIZE0(2)
  ) \CtrlJoin1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\channel1$irdy )
    , .\i0$data (\channel1$data )
    , .\i0$trdy (\channel1$trdy )
    , .\i1$irdy (\channel2$irdy )
    , .\i1$data (\channel2$data )
    , .\i1$trdy (\channel2$trdy )
    , .\o0$irdy (\bus_outs2$irdy )
    , .\o0$data (\bus_outs2$data )
    , .\o0$trdy (\bus_outs2$trdy )
  );
  
  \Queue  #(
    .NUM_DATA(0),
    .DATASIZE(1),
    .LENGTH(2)
  ) \Queue1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\bus_ins4$irdy )
    , .\i0$data (\bus_ins4$data )
    , .\i0$trdy (\bus_ins4$trdy )
    , .\o0$irdy (\channel2$irdy )
    , .\o0$data (\channel2$data )
    , .\o0$trdy (\channel2$trdy )
  );
  
  \RECEPTION_1_1_0_2  \RECEPTION1  (
      .\clk (\clk ), .\rst (\rst ), .\t (\t )
    , .\input$irdy (\bus_ins2$irdy )
    , .\input$data (\bus_ins2$data )
    , .\input$trdy (\bus_ins2$trdy )
    , .\bus_outs1$irdy (\bus_outs1$irdy )
    , .\bus_outs1$data (\bus_outs1$data )
    , .\bus_outs1$trdy (\bus_outs1$trdy )
    , .\bus_outs2$irdy (\bypassLine$irdy )
    , .\bus_outs2$data (\bypassLine$data )
    , .\bus_outs2$trdy (\bypassLine$trdy )
    , .\bus_outs3$irdy (\toDFIFO$irdy )
    , .\bus_outs3$data (\toDFIFO$data )
    , .\bus_outs3$trdy (\toDFIFO$trdy )
    , .\bus_outs4$irdy (\bus_outs4$irdy )
    , .\bus_outs4$data (\bus_outs4$data )
    , .\bus_outs4$trdy (\bus_outs4$trdy )
    , .\CreditCounter1$PatientSource1$unbound_irdy (\RECEPTION1$CreditCounter1$PatientSource1$unbound_irdy )
    , .\CreditCounter1$PatientSource1$unbound_data (\RECEPTION1$CreditCounter1$PatientSource1$unbound_data )
    , .\CreditCounter1$PatientSource1$trdy (\RECEPTION1$CreditCounter1$PatientSource1$trdy )
    , .\CreditCounter1$Sink1$unbound_trdy (\RECEPTION1$CreditCounter1$Sink1$unbound_trdy )
    , .\CreditCounter1$Sink1$irdy (\RECEPTION1$CreditCounter1$Sink1$irdy )
    , .\CreditCounter1$Sink1$data (\RECEPTION1$CreditCounter1$Sink1$data )
  );
  
  \DFIFO_2$type3  \DFIFO1  (
      .\clk (\clk ), .\rst (\rst )
    , .\bus_ins1$irdy (\toDFIFO$irdy )
    , .\bus_ins1$data (\toDFIFO$data )
    , .\bus_ins1$trdy (\toDFIFO$trdy )
    , .\bus_ins2$irdy (\bus_ins3$irdy )
    , .\bus_ins2$data (\bus_ins3$data )
    , .\bus_ins2$trdy (\bus_ins3$trdy )
    , .\bus_outs1$irdy (\bus_outs3$irdy )
    , .\bus_outs1$data (\bus_outs3$data )
    , .\bus_outs1$trdy (\bus_outs3$trdy )
    , .\bus_outs2$irdy (\toEjection$irdy )
    , .\bus_outs2$data (\toEjection$data )
    , .\bus_outs2$trdy (\toEjection$trdy )
  );
  
  \EJECTION_2$type0  \EJECTION1  (
      .\clk (\clk ), .\rst (\rst )
    , .\bus_ins1$irdy (\goodPkts$irdy )
    , .\bus_ins1$data (\goodPkts$data )
    , .\bus_ins1$trdy (\goodPkts$trdy )
    , .\bus_ins2$irdy (\bypassLine$irdy )
    , .\bus_ins2$data (\bypassLine$data )
    , .\bus_ins2$trdy (\bypassLine$trdy )
    , .\bus_ins3$irdy (\toEjection$irdy )
    , .\bus_ins3$data (\toEjection$data )
    , .\bus_ins3$trdy (\toEjection$trdy )
    , .\output$irdy (\channel1$irdy )
    , .\output$data (\channel1$data )
    , .\output$trdy (\channel1$trdy )
  );
  
endmodule


//
// BBB_1_1_2_2_0_2 switch functions
//
module \SFUN_0$BBB_1_1_2_2_0_2_Switch1 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , output [0:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[1:0] \f$bool$g0  = \i0$data  ;
  wire[1:0] \f$bool$f$arg0$arg0$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$arg0$arg0$arg0$conj  = \f$bool$f$arg0$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$arg0$arg0$arg0  = \f$bool$f$arg0$arg0$arg0$conj [1:1] ;
  wire[0:0] \f$bool$f$arg0$arg0$arg1  = 1'd1 ;
  wire \f$bool$f$arg0$arg0  = \f$bool$f$arg0$arg0$arg0  == \f$bool$f$arg0$arg0$arg1  ;
  wire \f$bool$f$arg0  = !\f$bool$f$arg0$arg0  ;
  wire[1:0] \f$bool$f$arg1$arg0$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$arg1$arg0$arg0$conj  = \f$bool$f$arg1$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$arg1$arg0$arg0  = \f$bool$f$arg1$arg0$arg0$conj [0:0] ;
  wire[0:0] \f$bool$f$arg1$arg0$arg1  = 1'd1 ;
  wire \f$bool$f$arg1$arg0  = \f$bool$f$arg1$arg0$arg0  == \f$bool$f$arg1$arg0$arg1  ;
  wire \f$bool$f$arg1  = !\f$bool$f$arg1$arg0  ;
  wire \f$bool$f  = \f$bool$f$arg0  && \f$bool$f$arg1  ;
  wire \f$bool  = \f$bool$f  ;
  wire[0:0] \f$true$content  = 1'd0 ;
  wire[0:0] \f$true  = \f$true$content  ;
  wire[1:0] \f$false$bool$g0  = \i0$data  ;
  wire[1:0] \f$false$bool$f$arg0$arg0$arg0$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$arg0$arg0$arg0$conj  = \f$false$bool$f$arg0$arg0$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$arg0$arg0$arg0  = \f$false$bool$f$arg0$arg0$arg0$arg0$conj [1:1] ;
  wire[0:0] \f$false$bool$f$arg0$arg0$arg0$arg1  = 1'd1 ;
  wire \f$false$bool$f$arg0$arg0$arg0  = \f$false$bool$f$arg0$arg0$arg0$arg0  == \f$false$bool$f$arg0$arg0$arg0$arg1  ;
  wire \f$false$bool$f$arg0$arg0  = !\f$false$bool$f$arg0$arg0$arg0  ;
  wire[1:0] \f$false$bool$f$arg0$arg1$arg0$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$arg1$arg0$arg0$conj  = \f$false$bool$f$arg0$arg1$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$arg1$arg0$arg0  = \f$false$bool$f$arg0$arg1$arg0$arg0$conj [0:0] ;
  wire[0:0] \f$false$bool$f$arg0$arg1$arg0$arg1  = 1'd1 ;
  wire \f$false$bool$f$arg0$arg1$arg0  = \f$false$bool$f$arg0$arg1$arg0$arg0  == \f$false$bool$f$arg0$arg1$arg0$arg1  ;
  wire \f$false$bool$f$arg0$arg1  = !\f$false$bool$f$arg0$arg1$arg0  ;
  wire \f$false$bool$f$arg0  = \f$false$bool$f$arg0$arg0  && \f$false$bool$f$arg0$arg1  ;
  wire \f$false$bool$f  = !\f$false$bool$f$arg0  ;
  wire \f$false$bool  = \f$false$bool$f  ;
  wire[0:0] \f$false$true$content  = 1'd1 ;
  wire[0:0] \f$false$true  = \f$false$true$content  ;
  wire[0:0] \f$false$false$content  = 1'd0 ;
  wire[0:0] \f$false$false  = \f$false$false$content  ;
  wire[0:0] \f$false  = ( \f$false$bool  ? \f$false$true  : \f$false$false  ) ;
  wire[0:0] \f  = ( \f$bool  ? \f$true  : \f$false  ) ;
  
  assign \o0  = \f  ;
endmodule

module \OFUN_1$BBB_1_1_2_2_0_2_Switch1 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , output [1:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[1:0] \f  = \i0$data  ;
  
  assign \o0  = \f  ;
endmodule

module \OFUN_2$BBB_1_1_2_2_0_2_Switch1 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , output [1:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[1:0] \f  = \i0$data  ;
  
  assign \o0  = \f  ;
endmodule

module \BBB_1_1_2_2_1_2 (
      input \clk , input \rst , input [63:0] \t 
    , input \bus_ins1$irdy , input [1:0] \bus_ins1$data , output \bus_ins1$trdy 
    , input \bus_ins2$irdy , input [1:0] \bus_ins2$data , output \bus_ins2$trdy 
    , input \bus_ins3$irdy , input [1:0] \bus_ins3$data , output \bus_ins3$trdy 
    , input \bus_ins4$irdy , input [0:0] \bus_ins4$data , output \bus_ins4$trdy 
    , output \bus_outs1$irdy , output [1:0] \bus_outs1$data , input \bus_outs1$trdy 
    , output \bus_outs2$irdy , output [1:0] \bus_outs2$data , input \bus_outs2$trdy 
    , output \bus_outs3$irdy , output [1:0] \bus_outs3$data , input \bus_outs3$trdy 
    , output \bus_outs4$irdy , output [0:0] \bus_outs4$data , input \bus_outs4$trdy 
    , input \Sink1$unbound_trdy 
    , output \Sink1$irdy 
    , output [1:0] \Sink1$data 
    , input \RECEPTION1$CreditCounter1$PatientSource1$unbound_irdy 
    , input [0:0] \RECEPTION1$CreditCounter1$PatientSource1$unbound_data 
    , output \RECEPTION1$CreditCounter1$PatientSource1$trdy 
    , input \RECEPTION1$CreditCounter1$Sink1$unbound_trdy 
    , output \RECEPTION1$CreditCounter1$Sink1$irdy 
    , output [0:0] \RECEPTION1$CreditCounter1$Sink1$data 
  );
  
  //
  // Channel declarations
  //
  wire \toEjection$irdy  ;
  wire [1:0] \toEjection$data  ;
  wire \toEjection$trdy  ;
  wire \toDFIFO$irdy  ;
  wire [1:0] \toDFIFO$data  ;
  wire \toDFIFO$trdy  ;
  wire \bypassLine$irdy  ;
  wire [1:0] \bypassLine$data  ;
  wire \bypassLine$trdy  ;
  wire \goodPkts$irdy  ;
  wire [1:0] \goodPkts$data  ;
  wire \goodPkts$trdy  ;
  wire \badPkts$irdy  ;
  wire [1:0] \badPkts$data  ;
  wire \badPkts$trdy  ;
  wire \channel1$irdy  ;
  wire [1:0] \channel1$data  ;
  wire \channel1$trdy  ;
  wire \channel2$irdy  ;
  wire \channel2$data  ;
  wire \channel2$trdy  ;
  
  //
  // Function Channels
  //
  wire \sfunchan_0_Switch1$data  ;
  wire [1:0] \ofunchan_1_Switch1$data  ;
  wire [1:0] \ofunchan_2_Switch1$data  ;
  
  //
  // Component and Macro instantiations
  //
  \Switch2  #(
    .OUTPUTSIZE0(2),
    .OUTPUTSIZE1(2),
    .INPUTSIZE(2)
  ) \Switch1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\bus_ins1$irdy )
    , .\i0$data (\bus_ins1$data )
    , .\i0$trdy (\bus_ins1$trdy )
    , .\o0$irdy (\goodPkts$irdy )
    , .\o0$data (\goodPkts$data )
    , .\o0$trdy (\goodPkts$trdy )
    , .\o1$irdy (\badPkts$irdy )
    , .\o1$data (\badPkts$data )
    , .\o1$trdy (\badPkts$trdy )
    , .\sel$data (\sfunchan_0_Switch1$data )
    , .\f0$data (\ofunchan_1_Switch1$data )
    , .\f1$data (\ofunchan_2_Switch1$data )
  );
  
  \SFUN_0$BBB_1_1_2_2_1_2_Switch1  \sfun_0_Switch1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\bus_ins1$data )
    , .\o0 (\sfunchan_0_Switch1$data )
  );
  
  \OFUN_1$BBB_1_1_2_2_1_2_Switch1  \ofun_1_Switch1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\bus_ins1$data )
    , .\o0 (\ofunchan_1_Switch1$data )
  );
  
  \OFUN_2$BBB_1_1_2_2_1_2_Switch1  \ofun_2_Switch1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\bus_ins1$data )
    , .\o0 (\ofunchan_2_Switch1$data )
  );
  
  assign \Sink1$irdy  = \badPkts$irdy  ;
  assign \Sink1$data  = \badPkts$data  ;
  \Sink  #(
    .DATASIZE(2)
  ) \Sink1  (
      .\clk (\clk ), .\rst (\rst ), .\t (\t )
    , .\i0$irdy (\badPkts$irdy )
    , .\i0$data (\badPkts$data )
    , .\i0$trdy (\badPkts$trdy )
    , .\unbound_trdy (\Sink1$unbound_trdy )
  );
  
  \CTRLJoin2  #(
    .INPUTSIZE1(1),
    .OUTPUTSIZE(2),
    .INPUTSIZE0(2)
  ) \CtrlJoin1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\channel1$irdy )
    , .\i0$data (\channel1$data )
    , .\i0$trdy (\channel1$trdy )
    , .\i1$irdy (\channel2$irdy )
    , .\i1$data (\channel2$data )
    , .\i1$trdy (\channel2$trdy )
    , .\o0$irdy (\bus_outs2$irdy )
    , .\o0$data (\bus_outs2$data )
    , .\o0$trdy (\bus_outs2$trdy )
  );
  
  \Queue  #(
    .NUM_DATA(0),
    .DATASIZE(1),
    .LENGTH(2)
  ) \Queue1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\bus_ins4$irdy )
    , .\i0$data (\bus_ins4$data )
    , .\i0$trdy (\bus_ins4$trdy )
    , .\o0$irdy (\channel2$irdy )
    , .\o0$data (\channel2$data )
    , .\o0$trdy (\channel2$trdy )
  );
  
  \RECEPTION_1_1_1_2  \RECEPTION1  (
      .\clk (\clk ), .\rst (\rst ), .\t (\t )
    , .\input$irdy (\bus_ins2$irdy )
    , .\input$data (\bus_ins2$data )
    , .\input$trdy (\bus_ins2$trdy )
    , .\bus_outs1$irdy (\bus_outs1$irdy )
    , .\bus_outs1$data (\bus_outs1$data )
    , .\bus_outs1$trdy (\bus_outs1$trdy )
    , .\bus_outs2$irdy (\bypassLine$irdy )
    , .\bus_outs2$data (\bypassLine$data )
    , .\bus_outs2$trdy (\bypassLine$trdy )
    , .\bus_outs3$irdy (\toDFIFO$irdy )
    , .\bus_outs3$data (\toDFIFO$data )
    , .\bus_outs3$trdy (\toDFIFO$trdy )
    , .\bus_outs4$irdy (\bus_outs4$irdy )
    , .\bus_outs4$data (\bus_outs4$data )
    , .\bus_outs4$trdy (\bus_outs4$trdy )
    , .\CreditCounter1$PatientSource1$unbound_irdy (\RECEPTION1$CreditCounter1$PatientSource1$unbound_irdy )
    , .\CreditCounter1$PatientSource1$unbound_data (\RECEPTION1$CreditCounter1$PatientSource1$unbound_data )
    , .\CreditCounter1$PatientSource1$trdy (\RECEPTION1$CreditCounter1$PatientSource1$trdy )
    , .\CreditCounter1$Sink1$unbound_trdy (\RECEPTION1$CreditCounter1$Sink1$unbound_trdy )
    , .\CreditCounter1$Sink1$irdy (\RECEPTION1$CreditCounter1$Sink1$irdy )
    , .\CreditCounter1$Sink1$data (\RECEPTION1$CreditCounter1$Sink1$data )
  );
  
  \DFIFO_2$type3  \DFIFO1  (
      .\clk (\clk ), .\rst (\rst )
    , .\bus_ins1$irdy (\toDFIFO$irdy )
    , .\bus_ins1$data (\toDFIFO$data )
    , .\bus_ins1$trdy (\toDFIFO$trdy )
    , .\bus_ins2$irdy (\bus_ins3$irdy )
    , .\bus_ins2$data (\bus_ins3$data )
    , .\bus_ins2$trdy (\bus_ins3$trdy )
    , .\bus_outs1$irdy (\bus_outs3$irdy )
    , .\bus_outs1$data (\bus_outs3$data )
    , .\bus_outs1$trdy (\bus_outs3$trdy )
    , .\bus_outs2$irdy (\toEjection$irdy )
    , .\bus_outs2$data (\toEjection$data )
    , .\bus_outs2$trdy (\toEjection$trdy )
  );
  
  \EJECTION_2$type0  \EJECTION1  (
      .\clk (\clk ), .\rst (\rst )
    , .\bus_ins1$irdy (\goodPkts$irdy )
    , .\bus_ins1$data (\goodPkts$data )
    , .\bus_ins1$trdy (\goodPkts$trdy )
    , .\bus_ins2$irdy (\bypassLine$irdy )
    , .\bus_ins2$data (\bypassLine$data )
    , .\bus_ins2$trdy (\bypassLine$trdy )
    , .\bus_ins3$irdy (\toEjection$irdy )
    , .\bus_ins3$data (\toEjection$data )
    , .\bus_ins3$trdy (\toEjection$trdy )
    , .\output$irdy (\channel1$irdy )
    , .\output$data (\channel1$data )
    , .\output$trdy (\channel1$trdy )
  );
  
endmodule


//
// BBB_1_1_2_2_1_2 switch functions
//
module \SFUN_0$BBB_1_1_2_2_1_2_Switch1 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , output [0:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[1:0] \f$bool$g0  = \i0$data  ;
  wire[1:0] \f$bool$f$arg0$arg0$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$arg0$arg0$arg0$conj  = \f$bool$f$arg0$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$arg0$arg0$arg0  = \f$bool$f$arg0$arg0$arg0$conj [1:1] ;
  wire[0:0] \f$bool$f$arg0$arg0$arg1  = 1'd1 ;
  wire \f$bool$f$arg0$arg0  = \f$bool$f$arg0$arg0$arg0  == \f$bool$f$arg0$arg0$arg1  ;
  wire \f$bool$f$arg0  = !\f$bool$f$arg0$arg0  ;
  wire[1:0] \f$bool$f$arg1$arg0$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$arg1$arg0$arg0$conj  = \f$bool$f$arg1$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$arg1$arg0$arg0  = \f$bool$f$arg1$arg0$arg0$conj [0:0] ;
  wire[0:0] \f$bool$f$arg1$arg0$arg1  = 1'd1 ;
  wire \f$bool$f$arg1$arg0  = \f$bool$f$arg1$arg0$arg0  == \f$bool$f$arg1$arg0$arg1  ;
  wire \f$bool$f$arg1  = !\f$bool$f$arg1$arg0  ;
  wire \f$bool$f  = \f$bool$f$arg0  && \f$bool$f$arg1  ;
  wire \f$bool  = \f$bool$f  ;
  wire[0:0] \f$true$content  = 1'd0 ;
  wire[0:0] \f$true  = \f$true$content  ;
  wire[1:0] \f$false$bool$g0  = \i0$data  ;
  wire[1:0] \f$false$bool$f$arg0$arg0$arg0$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$arg0$arg0$arg0$conj  = \f$false$bool$f$arg0$arg0$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$arg0$arg0$arg0  = \f$false$bool$f$arg0$arg0$arg0$arg0$conj [1:1] ;
  wire[0:0] \f$false$bool$f$arg0$arg0$arg0$arg1  = 1'd1 ;
  wire \f$false$bool$f$arg0$arg0$arg0  = \f$false$bool$f$arg0$arg0$arg0$arg0  == \f$false$bool$f$arg0$arg0$arg0$arg1  ;
  wire \f$false$bool$f$arg0$arg0  = !\f$false$bool$f$arg0$arg0$arg0  ;
  wire[1:0] \f$false$bool$f$arg0$arg1$arg0$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$arg1$arg0$arg0$conj  = \f$false$bool$f$arg0$arg1$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$arg1$arg0$arg0  = \f$false$bool$f$arg0$arg1$arg0$arg0$conj [0:0] ;
  wire[0:0] \f$false$bool$f$arg0$arg1$arg0$arg1  = 1'd1 ;
  wire \f$false$bool$f$arg0$arg1$arg0  = \f$false$bool$f$arg0$arg1$arg0$arg0  == \f$false$bool$f$arg0$arg1$arg0$arg1  ;
  wire \f$false$bool$f$arg0$arg1  = !\f$false$bool$f$arg0$arg1$arg0  ;
  wire \f$false$bool$f$arg0  = \f$false$bool$f$arg0$arg0  && \f$false$bool$f$arg0$arg1  ;
  wire \f$false$bool$f  = !\f$false$bool$f$arg0  ;
  wire \f$false$bool  = \f$false$bool$f  ;
  wire[0:0] \f$false$true$content  = 1'd1 ;
  wire[0:0] \f$false$true  = \f$false$true$content  ;
  wire[0:0] \f$false$false$content  = 1'd0 ;
  wire[0:0] \f$false$false  = \f$false$false$content  ;
  wire[0:0] \f$false  = ( \f$false$bool  ? \f$false$true  : \f$false$false  ) ;
  wire[0:0] \f  = ( \f$bool  ? \f$true  : \f$false  ) ;
  
  assign \o0  = \f  ;
endmodule

module \OFUN_1$BBB_1_1_2_2_1_2_Switch1 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , output [1:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[1:0] \f  = \i0$data  ;
  
  assign \o0  = \f  ;
endmodule

module \OFUN_2$BBB_1_1_2_2_1_2_Switch1 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , output [1:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[1:0] \f  = \i0$data  ;
  
  assign \o0  = \f  ;
endmodule

module \BBB_0_1_2_2_2_2 (
      input \clk , input \rst , input [63:0] \t 
    , input \bus_ins1$irdy , input [1:0] \bus_ins1$data , output \bus_ins1$trdy 
    , input \bus_ins2$irdy , input [1:0] \bus_ins2$data , output \bus_ins2$trdy 
    , input \bus_ins3$irdy , input [1:0] \bus_ins3$data , output \bus_ins3$trdy 
    , input \bus_ins4$irdy , input [0:0] \bus_ins4$data , output \bus_ins4$trdy 
    , output \bus_outs1$irdy , output [1:0] \bus_outs1$data , input \bus_outs1$trdy 
    , output \bus_outs2$irdy , output [1:0] \bus_outs2$data , input \bus_outs2$trdy 
    , output \bus_outs3$irdy , output [1:0] \bus_outs3$data , input \bus_outs3$trdy 
    , output \bus_outs4$irdy , output [0:0] \bus_outs4$data , input \bus_outs4$trdy 
    , input \Sink1$unbound_trdy 
    , output \Sink1$irdy 
    , output [1:0] \Sink1$data 
    , input \RECEPTION1$CreditCounter1$PatientSource1$unbound_irdy 
    , input [0:0] \RECEPTION1$CreditCounter1$PatientSource1$unbound_data 
    , output \RECEPTION1$CreditCounter1$PatientSource1$trdy 
    , input \RECEPTION1$CreditCounter1$Sink1$unbound_trdy 
    , output \RECEPTION1$CreditCounter1$Sink1$irdy 
    , output [0:0] \RECEPTION1$CreditCounter1$Sink1$data 
  );
  
  //
  // Channel declarations
  //
  wire \toEjection$irdy  ;
  wire [1:0] \toEjection$data  ;
  wire \toEjection$trdy  ;
  wire \toDFIFO$irdy  ;
  wire [1:0] \toDFIFO$data  ;
  wire \toDFIFO$trdy  ;
  wire \bypassLine$irdy  ;
  wire [1:0] \bypassLine$data  ;
  wire \bypassLine$trdy  ;
  wire \goodPkts$irdy  ;
  wire [1:0] \goodPkts$data  ;
  wire \goodPkts$trdy  ;
  wire \badPkts$irdy  ;
  wire [1:0] \badPkts$data  ;
  wire \badPkts$trdy  ;
  wire \channel1$irdy  ;
  wire [1:0] \channel1$data  ;
  wire \channel1$trdy  ;
  wire \channel2$irdy  ;
  wire \channel2$data  ;
  wire \channel2$trdy  ;
  
  //
  // Function Channels
  //
  wire \sfunchan_0_Switch1$data  ;
  wire [1:0] \ofunchan_1_Switch1$data  ;
  wire [1:0] \ofunchan_2_Switch1$data  ;
  
  //
  // Component and Macro instantiations
  //
  \Switch2  #(
    .OUTPUTSIZE0(2),
    .OUTPUTSIZE1(2),
    .INPUTSIZE(2)
  ) \Switch1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\bus_ins1$irdy )
    , .\i0$data (\bus_ins1$data )
    , .\i0$trdy (\bus_ins1$trdy )
    , .\o0$irdy (\goodPkts$irdy )
    , .\o0$data (\goodPkts$data )
    , .\o0$trdy (\goodPkts$trdy )
    , .\o1$irdy (\badPkts$irdy )
    , .\o1$data (\badPkts$data )
    , .\o1$trdy (\badPkts$trdy )
    , .\sel$data (\sfunchan_0_Switch1$data )
    , .\f0$data (\ofunchan_1_Switch1$data )
    , .\f1$data (\ofunchan_2_Switch1$data )
  );
  
  \SFUN_0$BBB_0_1_2_2_2_2_Switch1  \sfun_0_Switch1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\bus_ins1$data )
    , .\o0 (\sfunchan_0_Switch1$data )
  );
  
  \OFUN_1$BBB_0_1_2_2_2_2_Switch1  \ofun_1_Switch1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\bus_ins1$data )
    , .\o0 (\ofunchan_1_Switch1$data )
  );
  
  \OFUN_2$BBB_0_1_2_2_2_2_Switch1  \ofun_2_Switch1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\bus_ins1$data )
    , .\o0 (\ofunchan_2_Switch1$data )
  );
  
  assign \Sink1$irdy  = \badPkts$irdy  ;
  assign \Sink1$data  = \badPkts$data  ;
  \Sink  #(
    .DATASIZE(2)
  ) \Sink1  (
      .\clk (\clk ), .\rst (\rst ), .\t (\t )
    , .\i0$irdy (\badPkts$irdy )
    , .\i0$data (\badPkts$data )
    , .\i0$trdy (\badPkts$trdy )
    , .\unbound_trdy (\Sink1$unbound_trdy )
  );
  
  \CTRLJoin2  #(
    .INPUTSIZE1(1),
    .OUTPUTSIZE(2),
    .INPUTSIZE0(2)
  ) \CtrlJoin1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\channel1$irdy )
    , .\i0$data (\channel1$data )
    , .\i0$trdy (\channel1$trdy )
    , .\i1$irdy (\channel2$irdy )
    , .\i1$data (\channel2$data )
    , .\i1$trdy (\channel2$trdy )
    , .\o0$irdy (\bus_outs2$irdy )
    , .\o0$data (\bus_outs2$data )
    , .\o0$trdy (\bus_outs2$trdy )
  );
  
  \Queue  #(
    .NUM_DATA(0),
    .DATASIZE(1),
    .LENGTH(2)
  ) \Queue1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\bus_ins4$irdy )
    , .\i0$data (\bus_ins4$data )
    , .\i0$trdy (\bus_ins4$trdy )
    , .\o0$irdy (\channel2$irdy )
    , .\o0$data (\channel2$data )
    , .\o0$trdy (\channel2$trdy )
  );
  
  \RECEPTION_0_1_2_2  \RECEPTION1  (
      .\clk (\clk ), .\rst (\rst ), .\t (\t )
    , .\input$irdy (\bus_ins2$irdy )
    , .\input$data (\bus_ins2$data )
    , .\input$trdy (\bus_ins2$trdy )
    , .\bus_outs1$irdy (\bus_outs1$irdy )
    , .\bus_outs1$data (\bus_outs1$data )
    , .\bus_outs1$trdy (\bus_outs1$trdy )
    , .\bus_outs2$irdy (\bypassLine$irdy )
    , .\bus_outs2$data (\bypassLine$data )
    , .\bus_outs2$trdy (\bypassLine$trdy )
    , .\bus_outs3$irdy (\toDFIFO$irdy )
    , .\bus_outs3$data (\toDFIFO$data )
    , .\bus_outs3$trdy (\toDFIFO$trdy )
    , .\bus_outs4$irdy (\bus_outs4$irdy )
    , .\bus_outs4$data (\bus_outs4$data )
    , .\bus_outs4$trdy (\bus_outs4$trdy )
    , .\CreditCounter1$PatientSource1$unbound_irdy (\RECEPTION1$CreditCounter1$PatientSource1$unbound_irdy )
    , .\CreditCounter1$PatientSource1$unbound_data (\RECEPTION1$CreditCounter1$PatientSource1$unbound_data )
    , .\CreditCounter1$PatientSource1$trdy (\RECEPTION1$CreditCounter1$PatientSource1$trdy )
    , .\CreditCounter1$Sink1$unbound_trdy (\RECEPTION1$CreditCounter1$Sink1$unbound_trdy )
    , .\CreditCounter1$Sink1$irdy (\RECEPTION1$CreditCounter1$Sink1$irdy )
    , .\CreditCounter1$Sink1$data (\RECEPTION1$CreditCounter1$Sink1$data )
  );
  
  \DFIFO_2$type2  \DFIFO1  (
      .\clk (\clk ), .\rst (\rst )
    , .\bus_ins1$irdy (\toDFIFO$irdy )
    , .\bus_ins1$data (\toDFIFO$data )
    , .\bus_ins1$trdy (\toDFIFO$trdy )
    , .\bus_ins2$irdy (\bus_ins3$irdy )
    , .\bus_ins2$data (\bus_ins3$data )
    , .\bus_ins2$trdy (\bus_ins3$trdy )
    , .\bus_outs1$irdy (\bus_outs3$irdy )
    , .\bus_outs1$data (\bus_outs3$data )
    , .\bus_outs1$trdy (\bus_outs3$trdy )
    , .\bus_outs2$irdy (\toEjection$irdy )
    , .\bus_outs2$data (\toEjection$data )
    , .\bus_outs2$trdy (\toEjection$trdy )
  );
  
  \EJECTION_2$type4  \EJECTION1  (
      .\clk (\clk ), .\rst (\rst )
    , .\bus_ins1$irdy (\goodPkts$irdy )
    , .\bus_ins1$data (\goodPkts$data )
    , .\bus_ins1$trdy (\goodPkts$trdy )
    , .\bus_ins2$irdy (\bypassLine$irdy )
    , .\bus_ins2$data (\bypassLine$data )
    , .\bus_ins2$trdy (\bypassLine$trdy )
    , .\bus_ins3$irdy (\toEjection$irdy )
    , .\bus_ins3$data (\toEjection$data )
    , .\bus_ins3$trdy (\toEjection$trdy )
    , .\output$irdy (\channel1$irdy )
    , .\output$data (\channel1$data )
    , .\output$trdy (\channel1$trdy )
  );
  
endmodule


//
// BBB_0_1_2_2_2_2 switch functions
//
module \SFUN_0$BBB_0_1_2_2_2_2_Switch1 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , output [0:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[1:0] \f$bool$g0  = \i0$data  ;
  wire[1:0] \f$bool$f$arg0$arg0$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$arg0$arg0$arg0$conj  = \f$bool$f$arg0$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$arg0$arg0$arg0  = \f$bool$f$arg0$arg0$arg0$conj [1:1] ;
  wire[0:0] \f$bool$f$arg0$arg0$arg1  = 1'd0 ;
  wire \f$bool$f$arg0$arg0  = \f$bool$f$arg0$arg0$arg0  == \f$bool$f$arg0$arg0$arg1  ;
  wire \f$bool$f$arg0  = !\f$bool$f$arg0$arg0  ;
  wire[1:0] \f$bool$f$arg1$arg0$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$arg1$arg0$arg0$conj  = \f$bool$f$arg1$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$arg1$arg0$arg0  = \f$bool$f$arg1$arg0$arg0$conj [0:0] ;
  wire[0:0] \f$bool$f$arg1$arg0$arg1  = 1'd1 ;
  wire \f$bool$f$arg1$arg0  = \f$bool$f$arg1$arg0$arg0  == \f$bool$f$arg1$arg0$arg1  ;
  wire \f$bool$f$arg1  = !\f$bool$f$arg1$arg0  ;
  wire \f$bool$f  = \f$bool$f$arg0  && \f$bool$f$arg1  ;
  wire \f$bool  = \f$bool$f  ;
  wire[0:0] \f$true$content  = 1'd0 ;
  wire[0:0] \f$true  = \f$true$content  ;
  wire[1:0] \f$false$bool$g0  = \i0$data  ;
  wire[1:0] \f$false$bool$f$arg0$arg0$arg0$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$arg0$arg0$arg0$conj  = \f$false$bool$f$arg0$arg0$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$arg0$arg0$arg0  = \f$false$bool$f$arg0$arg0$arg0$arg0$conj [1:1] ;
  wire[0:0] \f$false$bool$f$arg0$arg0$arg0$arg1  = 1'd0 ;
  wire \f$false$bool$f$arg0$arg0$arg0  = \f$false$bool$f$arg0$arg0$arg0$arg0  == \f$false$bool$f$arg0$arg0$arg0$arg1  ;
  wire \f$false$bool$f$arg0$arg0  = !\f$false$bool$f$arg0$arg0$arg0  ;
  wire[1:0] \f$false$bool$f$arg0$arg1$arg0$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$arg1$arg0$arg0$conj  = \f$false$bool$f$arg0$arg1$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$arg1$arg0$arg0  = \f$false$bool$f$arg0$arg1$arg0$arg0$conj [0:0] ;
  wire[0:0] \f$false$bool$f$arg0$arg1$arg0$arg1  = 1'd1 ;
  wire \f$false$bool$f$arg0$arg1$arg0  = \f$false$bool$f$arg0$arg1$arg0$arg0  == \f$false$bool$f$arg0$arg1$arg0$arg1  ;
  wire \f$false$bool$f$arg0$arg1  = !\f$false$bool$f$arg0$arg1$arg0  ;
  wire \f$false$bool$f$arg0  = \f$false$bool$f$arg0$arg0  && \f$false$bool$f$arg0$arg1  ;
  wire \f$false$bool$f  = !\f$false$bool$f$arg0  ;
  wire \f$false$bool  = \f$false$bool$f  ;
  wire[0:0] \f$false$true$content  = 1'd1 ;
  wire[0:0] \f$false$true  = \f$false$true$content  ;
  wire[0:0] \f$false$false$content  = 1'd0 ;
  wire[0:0] \f$false$false  = \f$false$false$content  ;
  wire[0:0] \f$false  = ( \f$false$bool  ? \f$false$true  : \f$false$false  ) ;
  wire[0:0] \f  = ( \f$bool  ? \f$true  : \f$false  ) ;
  
  assign \o0  = \f  ;
endmodule

module \OFUN_1$BBB_0_1_2_2_2_2_Switch1 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , output [1:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[1:0] \f  = \i0$data  ;
  
  assign \o0  = \f  ;
endmodule

module \OFUN_2$BBB_0_1_2_2_2_2_Switch1 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , output [1:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[1:0] \f  = \i0$data  ;
  
  assign \o0  = \f  ;
endmodule

module \BBB_1_0_2_2_1_2 (
      input \clk , input \rst , input [63:0] \t 
    , input \bus_ins1$irdy , input [1:0] \bus_ins1$data , output \bus_ins1$trdy 
    , input \bus_ins2$irdy , input [1:0] \bus_ins2$data , output \bus_ins2$trdy 
    , input \bus_ins3$irdy , input [1:0] \bus_ins3$data , output \bus_ins3$trdy 
    , input \bus_ins4$irdy , input [0:0] \bus_ins4$data , output \bus_ins4$trdy 
    , output \bus_outs1$irdy , output [1:0] \bus_outs1$data , input \bus_outs1$trdy 
    , output \bus_outs2$irdy , output [1:0] \bus_outs2$data , input \bus_outs2$trdy 
    , output \bus_outs3$irdy , output [1:0] \bus_outs3$data , input \bus_outs3$trdy 
    , output \bus_outs4$irdy , output [0:0] \bus_outs4$data , input \bus_outs4$trdy 
    , input \Sink1$unbound_trdy 
    , output \Sink1$irdy 
    , output [1:0] \Sink1$data 
    , input \RECEPTION1$CreditCounter1$PatientSource1$unbound_irdy 
    , input [0:0] \RECEPTION1$CreditCounter1$PatientSource1$unbound_data 
    , output \RECEPTION1$CreditCounter1$PatientSource1$trdy 
    , input \RECEPTION1$CreditCounter1$Sink1$unbound_trdy 
    , output \RECEPTION1$CreditCounter1$Sink1$irdy 
    , output [0:0] \RECEPTION1$CreditCounter1$Sink1$data 
  );
  
  //
  // Channel declarations
  //
  wire \toEjection$irdy  ;
  wire [1:0] \toEjection$data  ;
  wire \toEjection$trdy  ;
  wire \toDFIFO$irdy  ;
  wire [1:0] \toDFIFO$data  ;
  wire \toDFIFO$trdy  ;
  wire \bypassLine$irdy  ;
  wire [1:0] \bypassLine$data  ;
  wire \bypassLine$trdy  ;
  wire \goodPkts$irdy  ;
  wire [1:0] \goodPkts$data  ;
  wire \goodPkts$trdy  ;
  wire \badPkts$irdy  ;
  wire [1:0] \badPkts$data  ;
  wire \badPkts$trdy  ;
  wire \channel1$irdy  ;
  wire [1:0] \channel1$data  ;
  wire \channel1$trdy  ;
  wire \channel2$irdy  ;
  wire \channel2$data  ;
  wire \channel2$trdy  ;
  
  //
  // Function Channels
  //
  wire \sfunchan_0_Switch1$data  ;
  wire [1:0] \ofunchan_1_Switch1$data  ;
  wire [1:0] \ofunchan_2_Switch1$data  ;
  
  //
  // Component and Macro instantiations
  //
  \Switch2  #(
    .OUTPUTSIZE0(2),
    .OUTPUTSIZE1(2),
    .INPUTSIZE(2)
  ) \Switch1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\bus_ins1$irdy )
    , .\i0$data (\bus_ins1$data )
    , .\i0$trdy (\bus_ins1$trdy )
    , .\o0$irdy (\goodPkts$irdy )
    , .\o0$data (\goodPkts$data )
    , .\o0$trdy (\goodPkts$trdy )
    , .\o1$irdy (\badPkts$irdy )
    , .\o1$data (\badPkts$data )
    , .\o1$trdy (\badPkts$trdy )
    , .\sel$data (\sfunchan_0_Switch1$data )
    , .\f0$data (\ofunchan_1_Switch1$data )
    , .\f1$data (\ofunchan_2_Switch1$data )
  );
  
  \SFUN_0$BBB_1_0_2_2_1_2_Switch1  \sfun_0_Switch1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\bus_ins1$data )
    , .\o0 (\sfunchan_0_Switch1$data )
  );
  
  \OFUN_1$BBB_1_0_2_2_1_2_Switch1  \ofun_1_Switch1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\bus_ins1$data )
    , .\o0 (\ofunchan_1_Switch1$data )
  );
  
  \OFUN_2$BBB_1_0_2_2_1_2_Switch1  \ofun_2_Switch1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\bus_ins1$data )
    , .\o0 (\ofunchan_2_Switch1$data )
  );
  
  assign \Sink1$irdy  = \badPkts$irdy  ;
  assign \Sink1$data  = \badPkts$data  ;
  \Sink  #(
    .DATASIZE(2)
  ) \Sink1  (
      .\clk (\clk ), .\rst (\rst ), .\t (\t )
    , .\i0$irdy (\badPkts$irdy )
    , .\i0$data (\badPkts$data )
    , .\i0$trdy (\badPkts$trdy )
    , .\unbound_trdy (\Sink1$unbound_trdy )
  );
  
  \CTRLJoin2  #(
    .INPUTSIZE1(1),
    .OUTPUTSIZE(2),
    .INPUTSIZE0(2)
  ) \CtrlJoin1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\channel1$irdy )
    , .\i0$data (\channel1$data )
    , .\i0$trdy (\channel1$trdy )
    , .\i1$irdy (\channel2$irdy )
    , .\i1$data (\channel2$data )
    , .\i1$trdy (\channel2$trdy )
    , .\o0$irdy (\bus_outs2$irdy )
    , .\o0$data (\bus_outs2$data )
    , .\o0$trdy (\bus_outs2$trdy )
  );
  
  \Queue  #(
    .NUM_DATA(0),
    .DATASIZE(1),
    .LENGTH(2)
  ) \Queue1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\bus_ins4$irdy )
    , .\i0$data (\bus_ins4$data )
    , .\i0$trdy (\bus_ins4$trdy )
    , .\o0$irdy (\channel2$irdy )
    , .\o0$data (\channel2$data )
    , .\o0$trdy (\channel2$trdy )
  );
  
  \RECEPTION_1_0_1_2  \RECEPTION1  (
      .\clk (\clk ), .\rst (\rst ), .\t (\t )
    , .\input$irdy (\bus_ins2$irdy )
    , .\input$data (\bus_ins2$data )
    , .\input$trdy (\bus_ins2$trdy )
    , .\bus_outs1$irdy (\bus_outs1$irdy )
    , .\bus_outs1$data (\bus_outs1$data )
    , .\bus_outs1$trdy (\bus_outs1$trdy )
    , .\bus_outs2$irdy (\bypassLine$irdy )
    , .\bus_outs2$data (\bypassLine$data )
    , .\bus_outs2$trdy (\bypassLine$trdy )
    , .\bus_outs3$irdy (\toDFIFO$irdy )
    , .\bus_outs3$data (\toDFIFO$data )
    , .\bus_outs3$trdy (\toDFIFO$trdy )
    , .\bus_outs4$irdy (\bus_outs4$irdy )
    , .\bus_outs4$data (\bus_outs4$data )
    , .\bus_outs4$trdy (\bus_outs4$trdy )
    , .\CreditCounter1$PatientSource1$unbound_irdy (\RECEPTION1$CreditCounter1$PatientSource1$unbound_irdy )
    , .\CreditCounter1$PatientSource1$unbound_data (\RECEPTION1$CreditCounter1$PatientSource1$unbound_data )
    , .\CreditCounter1$PatientSource1$trdy (\RECEPTION1$CreditCounter1$PatientSource1$trdy )
    , .\CreditCounter1$Sink1$unbound_trdy (\RECEPTION1$CreditCounter1$Sink1$unbound_trdy )
    , .\CreditCounter1$Sink1$irdy (\RECEPTION1$CreditCounter1$Sink1$irdy )
    , .\CreditCounter1$Sink1$data (\RECEPTION1$CreditCounter1$Sink1$data )
  );
  
  \DFIFO_2$type3  \DFIFO1  (
      .\clk (\clk ), .\rst (\rst )
    , .\bus_ins1$irdy (\toDFIFO$irdy )
    , .\bus_ins1$data (\toDFIFO$data )
    , .\bus_ins1$trdy (\toDFIFO$trdy )
    , .\bus_ins2$irdy (\bus_ins3$irdy )
    , .\bus_ins2$data (\bus_ins3$data )
    , .\bus_ins2$trdy (\bus_ins3$trdy )
    , .\bus_outs1$irdy (\bus_outs3$irdy )
    , .\bus_outs1$data (\bus_outs3$data )
    , .\bus_outs1$trdy (\bus_outs3$trdy )
    , .\bus_outs2$irdy (\toEjection$irdy )
    , .\bus_outs2$data (\toEjection$data )
    , .\bus_outs2$trdy (\toEjection$trdy )
  );
  
  \EJECTION_2$type2  \EJECTION1  (
      .\clk (\clk ), .\rst (\rst )
    , .\bus_ins1$irdy (\goodPkts$irdy )
    , .\bus_ins1$data (\goodPkts$data )
    , .\bus_ins1$trdy (\goodPkts$trdy )
    , .\bus_ins2$irdy (\bypassLine$irdy )
    , .\bus_ins2$data (\bypassLine$data )
    , .\bus_ins2$trdy (\bypassLine$trdy )
    , .\bus_ins3$irdy (\toEjection$irdy )
    , .\bus_ins3$data (\toEjection$data )
    , .\bus_ins3$trdy (\toEjection$trdy )
    , .\output$irdy (\channel1$irdy )
    , .\output$data (\channel1$data )
    , .\output$trdy (\channel1$trdy )
  );
  
endmodule


//
// BBB_1_0_2_2_1_2 switch functions
//
module \SFUN_0$BBB_1_0_2_2_1_2_Switch1 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , output [0:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[1:0] \f$bool$g0  = \i0$data  ;
  wire[1:0] \f$bool$f$arg0$arg0$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$arg0$arg0$arg0$conj  = \f$bool$f$arg0$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$arg0$arg0$arg0  = \f$bool$f$arg0$arg0$arg0$conj [1:1] ;
  wire[0:0] \f$bool$f$arg0$arg0$arg1  = 1'd1 ;
  wire \f$bool$f$arg0$arg0  = \f$bool$f$arg0$arg0$arg0  == \f$bool$f$arg0$arg0$arg1  ;
  wire \f$bool$f$arg0  = !\f$bool$f$arg0$arg0  ;
  wire[1:0] \f$bool$f$arg1$arg0$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$arg1$arg0$arg0$conj  = \f$bool$f$arg1$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$arg1$arg0$arg0  = \f$bool$f$arg1$arg0$arg0$conj [0:0] ;
  wire[0:0] \f$bool$f$arg1$arg0$arg1  = 1'd0 ;
  wire \f$bool$f$arg1$arg0  = \f$bool$f$arg1$arg0$arg0  == \f$bool$f$arg1$arg0$arg1  ;
  wire \f$bool$f$arg1  = !\f$bool$f$arg1$arg0  ;
  wire \f$bool$f  = \f$bool$f$arg0  && \f$bool$f$arg1  ;
  wire \f$bool  = \f$bool$f  ;
  wire[0:0] \f$true$content  = 1'd0 ;
  wire[0:0] \f$true  = \f$true$content  ;
  wire[1:0] \f$false$bool$g0  = \i0$data  ;
  wire[1:0] \f$false$bool$f$arg0$arg0$arg0$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$arg0$arg0$arg0$conj  = \f$false$bool$f$arg0$arg0$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$arg0$arg0$arg0  = \f$false$bool$f$arg0$arg0$arg0$arg0$conj [1:1] ;
  wire[0:0] \f$false$bool$f$arg0$arg0$arg0$arg1  = 1'd1 ;
  wire \f$false$bool$f$arg0$arg0$arg0  = \f$false$bool$f$arg0$arg0$arg0$arg0  == \f$false$bool$f$arg0$arg0$arg0$arg1  ;
  wire \f$false$bool$f$arg0$arg0  = !\f$false$bool$f$arg0$arg0$arg0  ;
  wire[1:0] \f$false$bool$f$arg0$arg1$arg0$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$arg1$arg0$arg0$conj  = \f$false$bool$f$arg0$arg1$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$arg1$arg0$arg0  = \f$false$bool$f$arg0$arg1$arg0$arg0$conj [0:0] ;
  wire[0:0] \f$false$bool$f$arg0$arg1$arg0$arg1  = 1'd0 ;
  wire \f$false$bool$f$arg0$arg1$arg0  = \f$false$bool$f$arg0$arg1$arg0$arg0  == \f$false$bool$f$arg0$arg1$arg0$arg1  ;
  wire \f$false$bool$f$arg0$arg1  = !\f$false$bool$f$arg0$arg1$arg0  ;
  wire \f$false$bool$f$arg0  = \f$false$bool$f$arg0$arg0  && \f$false$bool$f$arg0$arg1  ;
  wire \f$false$bool$f  = !\f$false$bool$f$arg0  ;
  wire \f$false$bool  = \f$false$bool$f  ;
  wire[0:0] \f$false$true$content  = 1'd1 ;
  wire[0:0] \f$false$true  = \f$false$true$content  ;
  wire[0:0] \f$false$false$content  = 1'd0 ;
  wire[0:0] \f$false$false  = \f$false$false$content  ;
  wire[0:0] \f$false  = ( \f$false$bool  ? \f$false$true  : \f$false$false  ) ;
  wire[0:0] \f  = ( \f$bool  ? \f$true  : \f$false  ) ;
  
  assign \o0  = \f  ;
endmodule

module \OFUN_1$BBB_1_0_2_2_1_2_Switch1 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , output [1:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[1:0] \f  = \i0$data  ;
  
  assign \o0  = \f  ;
endmodule

module \OFUN_2$BBB_1_0_2_2_1_2_Switch1 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , output [1:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[1:0] \f  = \i0$data  ;
  
  assign \o0  = \f  ;
endmodule

module \BBB_1_1_2_2_2_2 (
      input \clk , input \rst , input [63:0] \t 
    , input \bus_ins1$irdy , input [1:0] \bus_ins1$data , output \bus_ins1$trdy 
    , input \bus_ins2$irdy , input [1:0] \bus_ins2$data , output \bus_ins2$trdy 
    , input \bus_ins3$irdy , input [1:0] \bus_ins3$data , output \bus_ins3$trdy 
    , input \bus_ins4$irdy , input [0:0] \bus_ins4$data , output \bus_ins4$trdy 
    , output \bus_outs1$irdy , output [1:0] \bus_outs1$data , input \bus_outs1$trdy 
    , output \bus_outs2$irdy , output [1:0] \bus_outs2$data , input \bus_outs2$trdy 
    , output \bus_outs3$irdy , output [1:0] \bus_outs3$data , input \bus_outs3$trdy 
    , output \bus_outs4$irdy , output [0:0] \bus_outs4$data , input \bus_outs4$trdy 
    , input \Sink1$unbound_trdy 
    , output \Sink1$irdy 
    , output [1:0] \Sink1$data 
    , input \RECEPTION1$CreditCounter1$PatientSource1$unbound_irdy 
    , input [0:0] \RECEPTION1$CreditCounter1$PatientSource1$unbound_data 
    , output \RECEPTION1$CreditCounter1$PatientSource1$trdy 
    , input \RECEPTION1$CreditCounter1$Sink1$unbound_trdy 
    , output \RECEPTION1$CreditCounter1$Sink1$irdy 
    , output [0:0] \RECEPTION1$CreditCounter1$Sink1$data 
  );
  
  //
  // Channel declarations
  //
  wire \toEjection$irdy  ;
  wire [1:0] \toEjection$data  ;
  wire \toEjection$trdy  ;
  wire \toDFIFO$irdy  ;
  wire [1:0] \toDFIFO$data  ;
  wire \toDFIFO$trdy  ;
  wire \bypassLine$irdy  ;
  wire [1:0] \bypassLine$data  ;
  wire \bypassLine$trdy  ;
  wire \goodPkts$irdy  ;
  wire [1:0] \goodPkts$data  ;
  wire \goodPkts$trdy  ;
  wire \badPkts$irdy  ;
  wire [1:0] \badPkts$data  ;
  wire \badPkts$trdy  ;
  wire \channel1$irdy  ;
  wire [1:0] \channel1$data  ;
  wire \channel1$trdy  ;
  wire \channel2$irdy  ;
  wire \channel2$data  ;
  wire \channel2$trdy  ;
  
  //
  // Function Channels
  //
  wire \sfunchan_0_Switch1$data  ;
  wire [1:0] \ofunchan_1_Switch1$data  ;
  wire [1:0] \ofunchan_2_Switch1$data  ;
  
  //
  // Component and Macro instantiations
  //
  \Switch2  #(
    .OUTPUTSIZE0(2),
    .OUTPUTSIZE1(2),
    .INPUTSIZE(2)
  ) \Switch1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\bus_ins1$irdy )
    , .\i0$data (\bus_ins1$data )
    , .\i0$trdy (\bus_ins1$trdy )
    , .\o0$irdy (\goodPkts$irdy )
    , .\o0$data (\goodPkts$data )
    , .\o0$trdy (\goodPkts$trdy )
    , .\o1$irdy (\badPkts$irdy )
    , .\o1$data (\badPkts$data )
    , .\o1$trdy (\badPkts$trdy )
    , .\sel$data (\sfunchan_0_Switch1$data )
    , .\f0$data (\ofunchan_1_Switch1$data )
    , .\f1$data (\ofunchan_2_Switch1$data )
  );
  
  \SFUN_0$BBB_1_1_2_2_2_2_Switch1  \sfun_0_Switch1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\bus_ins1$data )
    , .\o0 (\sfunchan_0_Switch1$data )
  );
  
  \OFUN_1$BBB_1_1_2_2_2_2_Switch1  \ofun_1_Switch1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\bus_ins1$data )
    , .\o0 (\ofunchan_1_Switch1$data )
  );
  
  \OFUN_2$BBB_1_1_2_2_2_2_Switch1  \ofun_2_Switch1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\bus_ins1$data )
    , .\o0 (\ofunchan_2_Switch1$data )
  );
  
  assign \Sink1$irdy  = \badPkts$irdy  ;
  assign \Sink1$data  = \badPkts$data  ;
  \Sink  #(
    .DATASIZE(2)
  ) \Sink1  (
      .\clk (\clk ), .\rst (\rst ), .\t (\t )
    , .\i0$irdy (\badPkts$irdy )
    , .\i0$data (\badPkts$data )
    , .\i0$trdy (\badPkts$trdy )
    , .\unbound_trdy (\Sink1$unbound_trdy )
  );
  
  \CTRLJoin2  #(
    .INPUTSIZE1(1),
    .OUTPUTSIZE(2),
    .INPUTSIZE0(2)
  ) \CtrlJoin1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\channel1$irdy )
    , .\i0$data (\channel1$data )
    , .\i0$trdy (\channel1$trdy )
    , .\i1$irdy (\channel2$irdy )
    , .\i1$data (\channel2$data )
    , .\i1$trdy (\channel2$trdy )
    , .\o0$irdy (\bus_outs2$irdy )
    , .\o0$data (\bus_outs2$data )
    , .\o0$trdy (\bus_outs2$trdy )
  );
  
  \Queue  #(
    .NUM_DATA(0),
    .DATASIZE(1),
    .LENGTH(2)
  ) \Queue1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\bus_ins4$irdy )
    , .\i0$data (\bus_ins4$data )
    , .\i0$trdy (\bus_ins4$trdy )
    , .\o0$irdy (\channel2$irdy )
    , .\o0$data (\channel2$data )
    , .\o0$trdy (\channel2$trdy )
  );
  
  \RECEPTION_1_1_2_2  \RECEPTION1  (
      .\clk (\clk ), .\rst (\rst ), .\t (\t )
    , .\input$irdy (\bus_ins2$irdy )
    , .\input$data (\bus_ins2$data )
    , .\input$trdy (\bus_ins2$trdy )
    , .\bus_outs1$irdy (\bus_outs1$irdy )
    , .\bus_outs1$data (\bus_outs1$data )
    , .\bus_outs1$trdy (\bus_outs1$trdy )
    , .\bus_outs2$irdy (\bypassLine$irdy )
    , .\bus_outs2$data (\bypassLine$data )
    , .\bus_outs2$trdy (\bypassLine$trdy )
    , .\bus_outs3$irdy (\toDFIFO$irdy )
    , .\bus_outs3$data (\toDFIFO$data )
    , .\bus_outs3$trdy (\toDFIFO$trdy )
    , .\bus_outs4$irdy (\bus_outs4$irdy )
    , .\bus_outs4$data (\bus_outs4$data )
    , .\bus_outs4$trdy (\bus_outs4$trdy )
    , .\CreditCounter1$PatientSource1$unbound_irdy (\RECEPTION1$CreditCounter1$PatientSource1$unbound_irdy )
    , .\CreditCounter1$PatientSource1$unbound_data (\RECEPTION1$CreditCounter1$PatientSource1$unbound_data )
    , .\CreditCounter1$PatientSource1$trdy (\RECEPTION1$CreditCounter1$PatientSource1$trdy )
    , .\CreditCounter1$Sink1$unbound_trdy (\RECEPTION1$CreditCounter1$Sink1$unbound_trdy )
    , .\CreditCounter1$Sink1$irdy (\RECEPTION1$CreditCounter1$Sink1$irdy )
    , .\CreditCounter1$Sink1$data (\RECEPTION1$CreditCounter1$Sink1$data )
  );
  
  \DFIFO_2$type2  \DFIFO1  (
      .\clk (\clk ), .\rst (\rst )
    , .\bus_ins1$irdy (\toDFIFO$irdy )
    , .\bus_ins1$data (\toDFIFO$data )
    , .\bus_ins1$trdy (\toDFIFO$trdy )
    , .\bus_ins2$irdy (\bus_ins3$irdy )
    , .\bus_ins2$data (\bus_ins3$data )
    , .\bus_ins2$trdy (\bus_ins3$trdy )
    , .\bus_outs1$irdy (\bus_outs3$irdy )
    , .\bus_outs1$data (\bus_outs3$data )
    , .\bus_outs1$trdy (\bus_outs3$trdy )
    , .\bus_outs2$irdy (\toEjection$irdy )
    , .\bus_outs2$data (\toEjection$data )
    , .\bus_outs2$trdy (\toEjection$trdy )
  );
  
  \EJECTION_2$type1  \EJECTION1  (
      .\clk (\clk ), .\rst (\rst )
    , .\bus_ins1$irdy (\goodPkts$irdy )
    , .\bus_ins1$data (\goodPkts$data )
    , .\bus_ins1$trdy (\goodPkts$trdy )
    , .\bus_ins2$irdy (\bypassLine$irdy )
    , .\bus_ins2$data (\bypassLine$data )
    , .\bus_ins2$trdy (\bypassLine$trdy )
    , .\bus_ins3$irdy (\toEjection$irdy )
    , .\bus_ins3$data (\toEjection$data )
    , .\bus_ins3$trdy (\toEjection$trdy )
    , .\output$irdy (\channel1$irdy )
    , .\output$data (\channel1$data )
    , .\output$trdy (\channel1$trdy )
  );
  
endmodule


//
// BBB_1_1_2_2_2_2 switch functions
//
module \SFUN_0$BBB_1_1_2_2_2_2_Switch1 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , output [0:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[1:0] \f$bool$g0  = \i0$data  ;
  wire[1:0] \f$bool$f$arg0$arg0$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$arg0$arg0$arg0$conj  = \f$bool$f$arg0$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$arg0$arg0$arg0  = \f$bool$f$arg0$arg0$arg0$conj [1:1] ;
  wire[0:0] \f$bool$f$arg0$arg0$arg1  = 1'd1 ;
  wire \f$bool$f$arg0$arg0  = \f$bool$f$arg0$arg0$arg0  == \f$bool$f$arg0$arg0$arg1  ;
  wire \f$bool$f$arg0  = !\f$bool$f$arg0$arg0  ;
  wire[1:0] \f$bool$f$arg1$arg0$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$arg1$arg0$arg0$conj  = \f$bool$f$arg1$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$arg1$arg0$arg0  = \f$bool$f$arg1$arg0$arg0$conj [0:0] ;
  wire[0:0] \f$bool$f$arg1$arg0$arg1  = 1'd1 ;
  wire \f$bool$f$arg1$arg0  = \f$bool$f$arg1$arg0$arg0  == \f$bool$f$arg1$arg0$arg1  ;
  wire \f$bool$f$arg1  = !\f$bool$f$arg1$arg0  ;
  wire \f$bool$f  = \f$bool$f$arg0  && \f$bool$f$arg1  ;
  wire \f$bool  = \f$bool$f  ;
  wire[0:0] \f$true$content  = 1'd0 ;
  wire[0:0] \f$true  = \f$true$content  ;
  wire[1:0] \f$false$bool$g0  = \i0$data  ;
  wire[1:0] \f$false$bool$f$arg0$arg0$arg0$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$arg0$arg0$arg0$conj  = \f$false$bool$f$arg0$arg0$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$arg0$arg0$arg0  = \f$false$bool$f$arg0$arg0$arg0$arg0$conj [1:1] ;
  wire[0:0] \f$false$bool$f$arg0$arg0$arg0$arg1  = 1'd1 ;
  wire \f$false$bool$f$arg0$arg0$arg0  = \f$false$bool$f$arg0$arg0$arg0$arg0  == \f$false$bool$f$arg0$arg0$arg0$arg1  ;
  wire \f$false$bool$f$arg0$arg0  = !\f$false$bool$f$arg0$arg0$arg0  ;
  wire[1:0] \f$false$bool$f$arg0$arg1$arg0$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$arg1$arg0$arg0$conj  = \f$false$bool$f$arg0$arg1$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$arg1$arg0$arg0  = \f$false$bool$f$arg0$arg1$arg0$arg0$conj [0:0] ;
  wire[0:0] \f$false$bool$f$arg0$arg1$arg0$arg1  = 1'd1 ;
  wire \f$false$bool$f$arg0$arg1$arg0  = \f$false$bool$f$arg0$arg1$arg0$arg0  == \f$false$bool$f$arg0$arg1$arg0$arg1  ;
  wire \f$false$bool$f$arg0$arg1  = !\f$false$bool$f$arg0$arg1$arg0  ;
  wire \f$false$bool$f$arg0  = \f$false$bool$f$arg0$arg0  && \f$false$bool$f$arg0$arg1  ;
  wire \f$false$bool$f  = !\f$false$bool$f$arg0  ;
  wire \f$false$bool  = \f$false$bool$f  ;
  wire[0:0] \f$false$true$content  = 1'd1 ;
  wire[0:0] \f$false$true  = \f$false$true$content  ;
  wire[0:0] \f$false$false$content  = 1'd0 ;
  wire[0:0] \f$false$false  = \f$false$false$content  ;
  wire[0:0] \f$false  = ( \f$false$bool  ? \f$false$true  : \f$false$false  ) ;
  wire[0:0] \f  = ( \f$bool  ? \f$true  : \f$false  ) ;
  
  assign \o0  = \f  ;
endmodule

module \OFUN_1$BBB_1_1_2_2_2_2_Switch1 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , output [1:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[1:0] \f  = \i0$data  ;
  
  assign \o0  = \f  ;
endmodule

module \OFUN_2$BBB_1_1_2_2_2_2_Switch1 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , output [1:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[1:0] \f  = \i0$data  ;
  
  assign \o0  = \f  ;
endmodule

module \BBB_0_0_2_2_0_2 (
      input \clk , input \rst , input [63:0] \t 
    , input \bus_ins1$irdy , input [1:0] \bus_ins1$data , output \bus_ins1$trdy 
    , input \bus_ins2$irdy , input [1:0] \bus_ins2$data , output \bus_ins2$trdy 
    , input \bus_ins3$irdy , input [1:0] \bus_ins3$data , output \bus_ins3$trdy 
    , input \bus_ins4$irdy , input [0:0] \bus_ins4$data , output \bus_ins4$trdy 
    , output \bus_outs1$irdy , output [1:0] \bus_outs1$data , input \bus_outs1$trdy 
    , output \bus_outs2$irdy , output [1:0] \bus_outs2$data , input \bus_outs2$trdy 
    , output \bus_outs3$irdy , output [1:0] \bus_outs3$data , input \bus_outs3$trdy 
    , output \bus_outs4$irdy , output [0:0] \bus_outs4$data , input \bus_outs4$trdy 
    , input \Sink1$unbound_trdy 
    , output \Sink1$irdy 
    , output [1:0] \Sink1$data 
    , input \RECEPTION1$CreditCounter1$PatientSource1$unbound_irdy 
    , input [0:0] \RECEPTION1$CreditCounter1$PatientSource1$unbound_data 
    , output \RECEPTION1$CreditCounter1$PatientSource1$trdy 
    , input \RECEPTION1$CreditCounter1$Sink1$unbound_trdy 
    , output \RECEPTION1$CreditCounter1$Sink1$irdy 
    , output [0:0] \RECEPTION1$CreditCounter1$Sink1$data 
  );
  
  //
  // Channel declarations
  //
  wire \toEjection$irdy  ;
  wire [1:0] \toEjection$data  ;
  wire \toEjection$trdy  ;
  wire \toDFIFO$irdy  ;
  wire [1:0] \toDFIFO$data  ;
  wire \toDFIFO$trdy  ;
  wire \bypassLine$irdy  ;
  wire [1:0] \bypassLine$data  ;
  wire \bypassLine$trdy  ;
  wire \goodPkts$irdy  ;
  wire [1:0] \goodPkts$data  ;
  wire \goodPkts$trdy  ;
  wire \badPkts$irdy  ;
  wire [1:0] \badPkts$data  ;
  wire \badPkts$trdy  ;
  wire \channel1$irdy  ;
  wire [1:0] \channel1$data  ;
  wire \channel1$trdy  ;
  wire \channel2$irdy  ;
  wire \channel2$data  ;
  wire \channel2$trdy  ;
  
  //
  // Function Channels
  //
  wire \sfunchan_0_Switch1$data  ;
  wire [1:0] \ofunchan_1_Switch1$data  ;
  wire [1:0] \ofunchan_2_Switch1$data  ;
  
  //
  // Component and Macro instantiations
  //
  \Switch2  #(
    .OUTPUTSIZE0(2),
    .OUTPUTSIZE1(2),
    .INPUTSIZE(2)
  ) \Switch1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\bus_ins1$irdy )
    , .\i0$data (\bus_ins1$data )
    , .\i0$trdy (\bus_ins1$trdy )
    , .\o0$irdy (\goodPkts$irdy )
    , .\o0$data (\goodPkts$data )
    , .\o0$trdy (\goodPkts$trdy )
    , .\o1$irdy (\badPkts$irdy )
    , .\o1$data (\badPkts$data )
    , .\o1$trdy (\badPkts$trdy )
    , .\sel$data (\sfunchan_0_Switch1$data )
    , .\f0$data (\ofunchan_1_Switch1$data )
    , .\f1$data (\ofunchan_2_Switch1$data )
  );
  
  \SFUN_0$BBB_0_0_2_2_0_2_Switch1  \sfun_0_Switch1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\bus_ins1$data )
    , .\o0 (\sfunchan_0_Switch1$data )
  );
  
  \OFUN_1$BBB_0_0_2_2_0_2_Switch1  \ofun_1_Switch1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\bus_ins1$data )
    , .\o0 (\ofunchan_1_Switch1$data )
  );
  
  \OFUN_2$BBB_0_0_2_2_0_2_Switch1  \ofun_2_Switch1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\bus_ins1$data )
    , .\o0 (\ofunchan_2_Switch1$data )
  );
  
  assign \Sink1$irdy  = \badPkts$irdy  ;
  assign \Sink1$data  = \badPkts$data  ;
  \Sink  #(
    .DATASIZE(2)
  ) \Sink1  (
      .\clk (\clk ), .\rst (\rst ), .\t (\t )
    , .\i0$irdy (\badPkts$irdy )
    , .\i0$data (\badPkts$data )
    , .\i0$trdy (\badPkts$trdy )
    , .\unbound_trdy (\Sink1$unbound_trdy )
  );
  
  \CTRLJoin2  #(
    .INPUTSIZE1(1),
    .OUTPUTSIZE(2),
    .INPUTSIZE0(2)
  ) \CtrlJoin1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\channel1$irdy )
    , .\i0$data (\channel1$data )
    , .\i0$trdy (\channel1$trdy )
    , .\i1$irdy (\channel2$irdy )
    , .\i1$data (\channel2$data )
    , .\i1$trdy (\channel2$trdy )
    , .\o0$irdy (\bus_outs2$irdy )
    , .\o0$data (\bus_outs2$data )
    , .\o0$trdy (\bus_outs2$trdy )
  );
  
  \Queue  #(
    .NUM_DATA(0),
    .DATASIZE(1),
    .LENGTH(2)
  ) \Queue1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\bus_ins4$irdy )
    , .\i0$data (\bus_ins4$data )
    , .\i0$trdy (\bus_ins4$trdy )
    , .\o0$irdy (\channel2$irdy )
    , .\o0$data (\channel2$data )
    , .\o0$trdy (\channel2$trdy )
  );
  
  \RECEPTION_0_0_0_2  \RECEPTION1  (
      .\clk (\clk ), .\rst (\rst ), .\t (\t )
    , .\input$irdy (\bus_ins2$irdy )
    , .\input$data (\bus_ins2$data )
    , .\input$trdy (\bus_ins2$trdy )
    , .\bus_outs1$irdy (\bus_outs1$irdy )
    , .\bus_outs1$data (\bus_outs1$data )
    , .\bus_outs1$trdy (\bus_outs1$trdy )
    , .\bus_outs2$irdy (\bypassLine$irdy )
    , .\bus_outs2$data (\bypassLine$data )
    , .\bus_outs2$trdy (\bypassLine$trdy )
    , .\bus_outs3$irdy (\toDFIFO$irdy )
    , .\bus_outs3$data (\toDFIFO$data )
    , .\bus_outs3$trdy (\toDFIFO$trdy )
    , .\bus_outs4$irdy (\bus_outs4$irdy )
    , .\bus_outs4$data (\bus_outs4$data )
    , .\bus_outs4$trdy (\bus_outs4$trdy )
    , .\CreditCounter1$PatientSource1$unbound_irdy (\RECEPTION1$CreditCounter1$PatientSource1$unbound_irdy )
    , .\CreditCounter1$PatientSource1$unbound_data (\RECEPTION1$CreditCounter1$PatientSource1$unbound_data )
    , .\CreditCounter1$PatientSource1$trdy (\RECEPTION1$CreditCounter1$PatientSource1$trdy )
    , .\CreditCounter1$Sink1$unbound_trdy (\RECEPTION1$CreditCounter1$Sink1$unbound_trdy )
    , .\CreditCounter1$Sink1$irdy (\RECEPTION1$CreditCounter1$Sink1$irdy )
    , .\CreditCounter1$Sink1$data (\RECEPTION1$CreditCounter1$Sink1$data )
  );
  
  \DFIFO_2$type0  \DFIFO1  (
      .\clk (\clk ), .\rst (\rst )
    , .\bus_ins1$irdy (\toDFIFO$irdy )
    , .\bus_ins1$data (\toDFIFO$data )
    , .\bus_ins1$trdy (\toDFIFO$trdy )
    , .\bus_ins2$irdy (\bus_ins3$irdy )
    , .\bus_ins2$data (\bus_ins3$data )
    , .\bus_ins2$trdy (\bus_ins3$trdy )
    , .\bus_outs1$irdy (\bus_outs3$irdy )
    , .\bus_outs1$data (\bus_outs3$data )
    , .\bus_outs1$trdy (\bus_outs3$trdy )
    , .\bus_outs2$irdy (\toEjection$irdy )
    , .\bus_outs2$data (\toEjection$data )
    , .\bus_outs2$trdy (\toEjection$trdy )
  );
  
  \EJECTION_2$type7  \EJECTION1  (
      .\clk (\clk ), .\rst (\rst )
    , .\bus_ins1$irdy (\goodPkts$irdy )
    , .\bus_ins1$data (\goodPkts$data )
    , .\bus_ins1$trdy (\goodPkts$trdy )
    , .\bus_ins2$irdy (\bypassLine$irdy )
    , .\bus_ins2$data (\bypassLine$data )
    , .\bus_ins2$trdy (\bypassLine$trdy )
    , .\bus_ins3$irdy (\toEjection$irdy )
    , .\bus_ins3$data (\toEjection$data )
    , .\bus_ins3$trdy (\toEjection$trdy )
    , .\output$irdy (\channel1$irdy )
    , .\output$data (\channel1$data )
    , .\output$trdy (\channel1$trdy )
  );
  
endmodule


//
// BBB_0_0_2_2_0_2 switch functions
//
module \SFUN_0$BBB_0_0_2_2_0_2_Switch1 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , output [0:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[1:0] \f$bool$g0  = \i0$data  ;
  wire[1:0] \f$bool$f$arg0$arg0$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$arg0$arg0$arg0$conj  = \f$bool$f$arg0$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$arg0$arg0$arg0  = \f$bool$f$arg0$arg0$arg0$conj [1:1] ;
  wire[0:0] \f$bool$f$arg0$arg0$arg1  = 1'd0 ;
  wire \f$bool$f$arg0$arg0  = \f$bool$f$arg0$arg0$arg0  == \f$bool$f$arg0$arg0$arg1  ;
  wire \f$bool$f$arg0  = !\f$bool$f$arg0$arg0  ;
  wire[1:0] \f$bool$f$arg1$arg0$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$arg1$arg0$arg0$conj  = \f$bool$f$arg1$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$arg1$arg0$arg0  = \f$bool$f$arg1$arg0$arg0$conj [0:0] ;
  wire[0:0] \f$bool$f$arg1$arg0$arg1  = 1'd0 ;
  wire \f$bool$f$arg1$arg0  = \f$bool$f$arg1$arg0$arg0  == \f$bool$f$arg1$arg0$arg1  ;
  wire \f$bool$f$arg1  = !\f$bool$f$arg1$arg0  ;
  wire \f$bool$f  = \f$bool$f$arg0  && \f$bool$f$arg1  ;
  wire \f$bool  = \f$bool$f  ;
  wire[0:0] \f$true$content  = 1'd0 ;
  wire[0:0] \f$true  = \f$true$content  ;
  wire[1:0] \f$false$bool$g0  = \i0$data  ;
  wire[1:0] \f$false$bool$f$arg0$arg0$arg0$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$arg0$arg0$arg0$conj  = \f$false$bool$f$arg0$arg0$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$arg0$arg0$arg0  = \f$false$bool$f$arg0$arg0$arg0$arg0$conj [1:1] ;
  wire[0:0] \f$false$bool$f$arg0$arg0$arg0$arg1  = 1'd0 ;
  wire \f$false$bool$f$arg0$arg0$arg0  = \f$false$bool$f$arg0$arg0$arg0$arg0  == \f$false$bool$f$arg0$arg0$arg0$arg1  ;
  wire \f$false$bool$f$arg0$arg0  = !\f$false$bool$f$arg0$arg0$arg0  ;
  wire[1:0] \f$false$bool$f$arg0$arg1$arg0$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$arg1$arg0$arg0$conj  = \f$false$bool$f$arg0$arg1$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$arg1$arg0$arg0  = \f$false$bool$f$arg0$arg1$arg0$arg0$conj [0:0] ;
  wire[0:0] \f$false$bool$f$arg0$arg1$arg0$arg1  = 1'd0 ;
  wire \f$false$bool$f$arg0$arg1$arg0  = \f$false$bool$f$arg0$arg1$arg0$arg0  == \f$false$bool$f$arg0$arg1$arg0$arg1  ;
  wire \f$false$bool$f$arg0$arg1  = !\f$false$bool$f$arg0$arg1$arg0  ;
  wire \f$false$bool$f$arg0  = \f$false$bool$f$arg0$arg0  && \f$false$bool$f$arg0$arg1  ;
  wire \f$false$bool$f  = !\f$false$bool$f$arg0  ;
  wire \f$false$bool  = \f$false$bool$f  ;
  wire[0:0] \f$false$true$content  = 1'd1 ;
  wire[0:0] \f$false$true  = \f$false$true$content  ;
  wire[0:0] \f$false$false$content  = 1'd0 ;
  wire[0:0] \f$false$false  = \f$false$false$content  ;
  wire[0:0] \f$false  = ( \f$false$bool  ? \f$false$true  : \f$false$false  ) ;
  wire[0:0] \f  = ( \f$bool  ? \f$true  : \f$false  ) ;
  
  assign \o0  = \f  ;
endmodule

module \OFUN_1$BBB_0_0_2_2_0_2_Switch1 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , output [1:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[1:0] \f  = \i0$data  ;
  
  assign \o0  = \f  ;
endmodule

module \OFUN_2$BBB_0_0_2_2_0_2_Switch1 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , output [1:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[1:0] \f  = \i0$data  ;
  
  assign \o0  = \f  ;
endmodule

module \BBB_0_1_2_2_1_2 (
      input \clk , input \rst , input [63:0] \t 
    , input \bus_ins1$irdy , input [1:0] \bus_ins1$data , output \bus_ins1$trdy 
    , input \bus_ins2$irdy , input [1:0] \bus_ins2$data , output \bus_ins2$trdy 
    , input \bus_ins3$irdy , input [1:0] \bus_ins3$data , output \bus_ins3$trdy 
    , input \bus_ins4$irdy , input [0:0] \bus_ins4$data , output \bus_ins4$trdy 
    , output \bus_outs1$irdy , output [1:0] \bus_outs1$data , input \bus_outs1$trdy 
    , output \bus_outs2$irdy , output [1:0] \bus_outs2$data , input \bus_outs2$trdy 
    , output \bus_outs3$irdy , output [1:0] \bus_outs3$data , input \bus_outs3$trdy 
    , output \bus_outs4$irdy , output [0:0] \bus_outs4$data , input \bus_outs4$trdy 
    , input \Sink1$unbound_trdy 
    , output \Sink1$irdy 
    , output [1:0] \Sink1$data 
    , input \RECEPTION1$CreditCounter1$PatientSource1$unbound_irdy 
    , input [0:0] \RECEPTION1$CreditCounter1$PatientSource1$unbound_data 
    , output \RECEPTION1$CreditCounter1$PatientSource1$trdy 
    , input \RECEPTION1$CreditCounter1$Sink1$unbound_trdy 
    , output \RECEPTION1$CreditCounter1$Sink1$irdy 
    , output [0:0] \RECEPTION1$CreditCounter1$Sink1$data 
  );
  
  //
  // Channel declarations
  //
  wire \toEjection$irdy  ;
  wire [1:0] \toEjection$data  ;
  wire \toEjection$trdy  ;
  wire \toDFIFO$irdy  ;
  wire [1:0] \toDFIFO$data  ;
  wire \toDFIFO$trdy  ;
  wire \bypassLine$irdy  ;
  wire [1:0] \bypassLine$data  ;
  wire \bypassLine$trdy  ;
  wire \goodPkts$irdy  ;
  wire [1:0] \goodPkts$data  ;
  wire \goodPkts$trdy  ;
  wire \badPkts$irdy  ;
  wire [1:0] \badPkts$data  ;
  wire \badPkts$trdy  ;
  wire \channel1$irdy  ;
  wire [1:0] \channel1$data  ;
  wire \channel1$trdy  ;
  wire \channel2$irdy  ;
  wire \channel2$data  ;
  wire \channel2$trdy  ;
  
  //
  // Function Channels
  //
  wire \sfunchan_0_Switch1$data  ;
  wire [1:0] \ofunchan_1_Switch1$data  ;
  wire [1:0] \ofunchan_2_Switch1$data  ;
  
  //
  // Component and Macro instantiations
  //
  \Switch2  #(
    .OUTPUTSIZE0(2),
    .OUTPUTSIZE1(2),
    .INPUTSIZE(2)
  ) \Switch1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\bus_ins1$irdy )
    , .\i0$data (\bus_ins1$data )
    , .\i0$trdy (\bus_ins1$trdy )
    , .\o0$irdy (\goodPkts$irdy )
    , .\o0$data (\goodPkts$data )
    , .\o0$trdy (\goodPkts$trdy )
    , .\o1$irdy (\badPkts$irdy )
    , .\o1$data (\badPkts$data )
    , .\o1$trdy (\badPkts$trdy )
    , .\sel$data (\sfunchan_0_Switch1$data )
    , .\f0$data (\ofunchan_1_Switch1$data )
    , .\f1$data (\ofunchan_2_Switch1$data )
  );
  
  \SFUN_0$BBB_0_1_2_2_1_2_Switch1  \sfun_0_Switch1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\bus_ins1$data )
    , .\o0 (\sfunchan_0_Switch1$data )
  );
  
  \OFUN_1$BBB_0_1_2_2_1_2_Switch1  \ofun_1_Switch1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\bus_ins1$data )
    , .\o0 (\ofunchan_1_Switch1$data )
  );
  
  \OFUN_2$BBB_0_1_2_2_1_2_Switch1  \ofun_2_Switch1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\bus_ins1$data )
    , .\o0 (\ofunchan_2_Switch1$data )
  );
  
  assign \Sink1$irdy  = \badPkts$irdy  ;
  assign \Sink1$data  = \badPkts$data  ;
  \Sink  #(
    .DATASIZE(2)
  ) \Sink1  (
      .\clk (\clk ), .\rst (\rst ), .\t (\t )
    , .\i0$irdy (\badPkts$irdy )
    , .\i0$data (\badPkts$data )
    , .\i0$trdy (\badPkts$trdy )
    , .\unbound_trdy (\Sink1$unbound_trdy )
  );
  
  \CTRLJoin2  #(
    .INPUTSIZE1(1),
    .OUTPUTSIZE(2),
    .INPUTSIZE0(2)
  ) \CtrlJoin1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\channel1$irdy )
    , .\i0$data (\channel1$data )
    , .\i0$trdy (\channel1$trdy )
    , .\i1$irdy (\channel2$irdy )
    , .\i1$data (\channel2$data )
    , .\i1$trdy (\channel2$trdy )
    , .\o0$irdy (\bus_outs2$irdy )
    , .\o0$data (\bus_outs2$data )
    , .\o0$trdy (\bus_outs2$trdy )
  );
  
  \Queue  #(
    .NUM_DATA(0),
    .DATASIZE(1),
    .LENGTH(2)
  ) \Queue1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\bus_ins4$irdy )
    , .\i0$data (\bus_ins4$data )
    , .\i0$trdy (\bus_ins4$trdy )
    , .\o0$irdy (\channel2$irdy )
    , .\o0$data (\channel2$data )
    , .\o0$trdy (\channel2$trdy )
  );
  
  \RECEPTION_0_1_1_2  \RECEPTION1  (
      .\clk (\clk ), .\rst (\rst ), .\t (\t )
    , .\input$irdy (\bus_ins2$irdy )
    , .\input$data (\bus_ins2$data )
    , .\input$trdy (\bus_ins2$trdy )
    , .\bus_outs1$irdy (\bus_outs1$irdy )
    , .\bus_outs1$data (\bus_outs1$data )
    , .\bus_outs1$trdy (\bus_outs1$trdy )
    , .\bus_outs2$irdy (\bypassLine$irdy )
    , .\bus_outs2$data (\bypassLine$data )
    , .\bus_outs2$trdy (\bypassLine$trdy )
    , .\bus_outs3$irdy (\toDFIFO$irdy )
    , .\bus_outs3$data (\toDFIFO$data )
    , .\bus_outs3$trdy (\toDFIFO$trdy )
    , .\bus_outs4$irdy (\bus_outs4$irdy )
    , .\bus_outs4$data (\bus_outs4$data )
    , .\bus_outs4$trdy (\bus_outs4$trdy )
    , .\CreditCounter1$PatientSource1$unbound_irdy (\RECEPTION1$CreditCounter1$PatientSource1$unbound_irdy )
    , .\CreditCounter1$PatientSource1$unbound_data (\RECEPTION1$CreditCounter1$PatientSource1$unbound_data )
    , .\CreditCounter1$PatientSource1$trdy (\RECEPTION1$CreditCounter1$PatientSource1$trdy )
    , .\CreditCounter1$Sink1$unbound_trdy (\RECEPTION1$CreditCounter1$Sink1$unbound_trdy )
    , .\CreditCounter1$Sink1$irdy (\RECEPTION1$CreditCounter1$Sink1$irdy )
    , .\CreditCounter1$Sink1$data (\RECEPTION1$CreditCounter1$Sink1$data )
  );
  
  \DFIFO_2$type0  \DFIFO1  (
      .\clk (\clk ), .\rst (\rst )
    , .\bus_ins1$irdy (\toDFIFO$irdy )
    , .\bus_ins1$data (\toDFIFO$data )
    , .\bus_ins1$trdy (\toDFIFO$trdy )
    , .\bus_ins2$irdy (\bus_ins3$irdy )
    , .\bus_ins2$data (\bus_ins3$data )
    , .\bus_ins2$trdy (\bus_ins3$trdy )
    , .\bus_outs1$irdy (\bus_outs3$irdy )
    , .\bus_outs1$data (\bus_outs3$data )
    , .\bus_outs1$trdy (\bus_outs3$trdy )
    , .\bus_outs2$irdy (\toEjection$irdy )
    , .\bus_outs2$data (\toEjection$data )
    , .\bus_outs2$trdy (\toEjection$trdy )
  );
  
  \EJECTION_2$type5  \EJECTION1  (
      .\clk (\clk ), .\rst (\rst )
    , .\bus_ins1$irdy (\goodPkts$irdy )
    , .\bus_ins1$data (\goodPkts$data )
    , .\bus_ins1$trdy (\goodPkts$trdy )
    , .\bus_ins2$irdy (\bypassLine$irdy )
    , .\bus_ins2$data (\bypassLine$data )
    , .\bus_ins2$trdy (\bypassLine$trdy )
    , .\bus_ins3$irdy (\toEjection$irdy )
    , .\bus_ins3$data (\toEjection$data )
    , .\bus_ins3$trdy (\toEjection$trdy )
    , .\output$irdy (\channel1$irdy )
    , .\output$data (\channel1$data )
    , .\output$trdy (\channel1$trdy )
  );
  
endmodule


//
// BBB_0_1_2_2_1_2 switch functions
//
module \SFUN_0$BBB_0_1_2_2_1_2_Switch1 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , output [0:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[1:0] \f$bool$g0  = \i0$data  ;
  wire[1:0] \f$bool$f$arg0$arg0$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$arg0$arg0$arg0$conj  = \f$bool$f$arg0$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$arg0$arg0$arg0  = \f$bool$f$arg0$arg0$arg0$conj [1:1] ;
  wire[0:0] \f$bool$f$arg0$arg0$arg1  = 1'd0 ;
  wire \f$bool$f$arg0$arg0  = \f$bool$f$arg0$arg0$arg0  == \f$bool$f$arg0$arg0$arg1  ;
  wire \f$bool$f$arg0  = !\f$bool$f$arg0$arg0  ;
  wire[1:0] \f$bool$f$arg1$arg0$arg0$conj$disj  = \f$bool$g0  ;
  wire[1:0] \f$bool$f$arg1$arg0$arg0$conj  = \f$bool$f$arg1$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$bool$f$arg1$arg0$arg0  = \f$bool$f$arg1$arg0$arg0$conj [0:0] ;
  wire[0:0] \f$bool$f$arg1$arg0$arg1  = 1'd1 ;
  wire \f$bool$f$arg1$arg0  = \f$bool$f$arg1$arg0$arg0  == \f$bool$f$arg1$arg0$arg1  ;
  wire \f$bool$f$arg1  = !\f$bool$f$arg1$arg0  ;
  wire \f$bool$f  = \f$bool$f$arg0  && \f$bool$f$arg1  ;
  wire \f$bool  = \f$bool$f  ;
  wire[0:0] \f$true$content  = 1'd0 ;
  wire[0:0] \f$true  = \f$true$content  ;
  wire[1:0] \f$false$bool$g0  = \i0$data  ;
  wire[1:0] \f$false$bool$f$arg0$arg0$arg0$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$arg0$arg0$arg0$conj  = \f$false$bool$f$arg0$arg0$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$arg0$arg0$arg0  = \f$false$bool$f$arg0$arg0$arg0$arg0$conj [1:1] ;
  wire[0:0] \f$false$bool$f$arg0$arg0$arg0$arg1  = 1'd0 ;
  wire \f$false$bool$f$arg0$arg0$arg0  = \f$false$bool$f$arg0$arg0$arg0$arg0  == \f$false$bool$f$arg0$arg0$arg0$arg1  ;
  wire \f$false$bool$f$arg0$arg0  = !\f$false$bool$f$arg0$arg0$arg0  ;
  wire[1:0] \f$false$bool$f$arg0$arg1$arg0$arg0$conj$disj  = \f$false$bool$g0  ;
  wire[1:0] \f$false$bool$f$arg0$arg1$arg0$arg0$conj  = \f$false$bool$f$arg0$arg1$arg0$arg0$conj$disj [1:0] ;
  wire[0:0] \f$false$bool$f$arg0$arg1$arg0$arg0  = \f$false$bool$f$arg0$arg1$arg0$arg0$conj [0:0] ;
  wire[0:0] \f$false$bool$f$arg0$arg1$arg0$arg1  = 1'd1 ;
  wire \f$false$bool$f$arg0$arg1$arg0  = \f$false$bool$f$arg0$arg1$arg0$arg0  == \f$false$bool$f$arg0$arg1$arg0$arg1  ;
  wire \f$false$bool$f$arg0$arg1  = !\f$false$bool$f$arg0$arg1$arg0  ;
  wire \f$false$bool$f$arg0  = \f$false$bool$f$arg0$arg0  && \f$false$bool$f$arg0$arg1  ;
  wire \f$false$bool$f  = !\f$false$bool$f$arg0  ;
  wire \f$false$bool  = \f$false$bool$f  ;
  wire[0:0] \f$false$true$content  = 1'd1 ;
  wire[0:0] \f$false$true  = \f$false$true$content  ;
  wire[0:0] \f$false$false$content  = 1'd0 ;
  wire[0:0] \f$false$false  = \f$false$false$content  ;
  wire[0:0] \f$false  = ( \f$false$bool  ? \f$false$true  : \f$false$false  ) ;
  wire[0:0] \f  = ( \f$bool  ? \f$true  : \f$false  ) ;
  
  assign \o0  = \f  ;
endmodule

module \OFUN_1$BBB_0_1_2_2_1_2_Switch1 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , output [1:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[1:0] \f  = \i0$data  ;
  
  assign \o0  = \f  ;
endmodule

module \OFUN_2$BBB_0_1_2_2_1_2_Switch1 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , output [1:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[1:0] \f  = \i0$data  ;
  
  assign \o0  = \f  ;
endmodule

module \LigeroRouter_0_0_2_2_2 (
      input \clk , input \rst , input [63:0] \t 
    , input \bus_ins1$irdy , input [1:0] \bus_ins1$data , output \bus_ins1$trdy 
    , input \bus_ins2$irdy , input [1:0] \bus_ins2$data , output \bus_ins2$trdy 
    , input \bus_ins3$irdy , input [1:0] \bus_ins3$data , output \bus_ins3$trdy 
    , input \bus_ins4$irdy , input [1:0] \bus_ins4$data , output \bus_ins4$trdy 
    , input \bus_ins5$irdy , input [1:0] \bus_ins5$data , output \bus_ins5$trdy 
    , input \bus_ins6$irdy , input [0:0] \bus_ins6$data , output \bus_ins6$trdy 
    , input \bus_ins7$irdy , input [0:0] \bus_ins7$data , output \bus_ins7$trdy 
    , input \bus_ins8$irdy , input [0:0] \bus_ins8$data , output \bus_ins8$trdy 
    , input \bus_ins9$irdy , input [0:0] \bus_ins9$data , output \bus_ins9$trdy 
    , output \bus_outs1$irdy , output [1:0] \bus_outs1$data , input \bus_outs1$trdy 
    , output \bus_outs2$irdy , output [1:0] \bus_outs2$data , input \bus_outs2$trdy 
    , output \bus_outs3$irdy , output [1:0] \bus_outs3$data , input \bus_outs3$trdy 
    , output \bus_outs4$irdy , output [1:0] \bus_outs4$data , input \bus_outs4$trdy 
    , output \bus_outs5$irdy , output [1:0] \bus_outs5$data , input \bus_outs5$trdy 
    , output \bus_outs6$irdy , output [0:0] \bus_outs6$data , input \bus_outs6$trdy 
    , output \bus_outs7$irdy , output [0:0] \bus_outs7$data , input \bus_outs7$trdy 
    , output \bus_outs8$irdy , output [0:0] \bus_outs8$data , input \bus_outs8$trdy 
    , output \bus_outs9$irdy , output [0:0] \bus_outs9$data , input \bus_outs9$trdy 
    , input \BBB1$Sink1$unbound_trdy 
    , output \BBB1$Sink1$irdy 
    , output [1:0] \BBB1$Sink1$data 
    , input \BBB1$RECEPTION1$CreditCounter1$PatientSource1$unbound_irdy 
    , input [0:0] \BBB1$RECEPTION1$CreditCounter1$PatientSource1$unbound_data 
    , output \BBB1$RECEPTION1$CreditCounter1$PatientSource1$trdy 
    , input \BBB1$RECEPTION1$CreditCounter1$Sink1$unbound_trdy 
    , output \BBB1$RECEPTION1$CreditCounter1$Sink1$irdy 
    , output [0:0] \BBB1$RECEPTION1$CreditCounter1$Sink1$data 
    , input \BBB2$Sink1$unbound_trdy 
    , output \BBB2$Sink1$irdy 
    , output [1:0] \BBB2$Sink1$data 
    , input \BBB2$RECEPTION1$CreditCounter1$PatientSource1$unbound_irdy 
    , input [0:0] \BBB2$RECEPTION1$CreditCounter1$PatientSource1$unbound_data 
    , output \BBB2$RECEPTION1$CreditCounter1$PatientSource1$trdy 
    , input \BBB2$RECEPTION1$CreditCounter1$Sink1$unbound_trdy 
    , output \BBB2$RECEPTION1$CreditCounter1$Sink1$irdy 
    , output [0:0] \BBB2$RECEPTION1$CreditCounter1$Sink1$data 
    , input \BBB3$Sink1$unbound_trdy 
    , output \BBB3$Sink1$irdy 
    , output [1:0] \BBB3$Sink1$data 
    , input \BBB3$RECEPTION1$CreditCounter1$PatientSource1$unbound_irdy 
    , input [0:0] \BBB3$RECEPTION1$CreditCounter1$PatientSource1$unbound_data 
    , output \BBB3$RECEPTION1$CreditCounter1$PatientSource1$trdy 
    , input \BBB3$RECEPTION1$CreditCounter1$Sink1$unbound_trdy 
    , output \BBB3$RECEPTION1$CreditCounter1$Sink1$irdy 
    , output [0:0] \BBB3$RECEPTION1$CreditCounter1$Sink1$data 
    , input \BBB4$Sink1$unbound_trdy 
    , output \BBB4$Sink1$irdy 
    , output [1:0] \BBB4$Sink1$data 
    , input \BBB4$RECEPTION1$CreditCounter1$PatientSource1$unbound_irdy 
    , input [0:0] \BBB4$RECEPTION1$CreditCounter1$PatientSource1$unbound_data 
    , output \BBB4$RECEPTION1$CreditCounter1$PatientSource1$trdy 
    , input \BBB4$RECEPTION1$CreditCounter1$Sink1$unbound_trdy 
    , output \BBB4$RECEPTION1$CreditCounter1$Sink1$irdy 
    , output [0:0] \BBB4$RECEPTION1$CreditCounter1$Sink1$data 
  );
  
  //
  // Channel declarations
  //
  wire \y_plus_loop$irdy  ;
  wire [1:0] \y_plus_loop$data  ;
  wire \y_plus_loop$trdy  ;
  wire \y_plus_cons$irdy  ;
  wire [1:0] \y_plus_cons$data  ;
  wire \y_plus_cons$trdy  ;
  wire \y_min_loop$irdy  ;
  wire [1:0] \y_min_loop$data  ;
  wire \y_min_loop$trdy  ;
  wire \y_min_cons$irdy  ;
  wire [1:0] \y_min_cons$data  ;
  wire \y_min_cons$trdy  ;
  wire \x_plus_loop$irdy  ;
  wire [1:0] \x_plus_loop$data  ;
  wire \x_plus_loop$trdy  ;
  wire \x_plus_cons$irdy  ;
  wire [1:0] \x_plus_cons$data  ;
  wire \x_plus_cons$trdy  ;
  wire \x_min_loop$irdy  ;
  wire [1:0] \x_min_loop$data  ;
  wire \x_min_loop$trdy  ;
  wire \x_min_cons$irdy  ;
  wire [1:0] \x_min_cons$data  ;
  wire \x_min_cons$trdy  ;
  wire \channel1$irdy  ;
  wire [1:0] \channel1$data  ;
  wire \channel1$trdy  ;
  wire \channel2$irdy  ;
  wire [1:0] \channel2$data  ;
  wire \channel2$trdy  ;
  wire \channel3$irdy  ;
  wire [1:0] \channel3$data  ;
  wire \channel3$trdy  ;
  wire \channel4$irdy  ;
  wire [1:0] \channel4$data  ;
  wire \channel4$trdy  ;
  wire \channel6$irdy  ;
  wire [1:0] \channel6$data  ;
  wire \channel6$trdy  ;
  wire \channel5$irdy  ;
  wire [1:0] \channel5$data  ;
  wire \channel5$trdy  ;
  wire \x_min_inj$irdy  ;
  wire [1:0] \x_min_inj$data  ;
  wire \x_min_inj$trdy  ;
  wire \x_plus_inj$irdy  ;
  wire [1:0] \x_plus_inj$data  ;
  wire \x_plus_inj$trdy  ;
  wire \y_min_inj$irdy  ;
  wire [1:0] \y_min_inj$data  ;
  wire \y_min_inj$trdy  ;
  wire \y_plus_inj$irdy  ;
  wire [1:0] \y_plus_inj$data  ;
  wire \y_plus_inj$trdy  ;
  wire \channel7$irdy  ;
  wire [1:0] \channel7$data  ;
  wire \channel7$trdy  ;
  
  //
  // Function Channels
  //
  wire [1:0] \ofunchan_0_Merge1$data  ;
  wire \sel_Merge1  ;
  wire [1:0] \ofunchan_0_Merge2$data  ;
  wire \sel_Merge2  ;
  wire [1:0] \ofunchan_0_Merge3$data  ;
  wire \sel_Merge3  ;
  
  //
  // Component and Macro instantiations
  //
  \Merge2  #(
    .INPUTSIZE1(2),
    .OUTPUTSIZE(2),
    .INPUTSIZE0(2)
  ) \Merge1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\x_min_cons$irdy )
    , .\i0$data (\x_min_cons$data )
    , .\i0$trdy (\x_min_cons$trdy )
    , .\i1$irdy (\channel6$irdy )
    , .\i1$data (\channel6$data )
    , .\i1$trdy (\channel6$trdy )
    , .\o0$irdy (\bus_outs1$irdy )
    , .\o0$data (\bus_outs1$data )
    , .\o0$trdy (\bus_outs1$trdy )
    , .\f$data (\ofunchan_0_Merge1$data )
    , .\sel (\sel_Merge1 )
  );
  
  \OFUN_0$LigeroRouter_0_0_2_2_2_Merge1  \ofun_0_Merge1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\x_min_cons$data )
    , .\i1$data (\channel6$data )
    , .\sel (\sel_Merge1 )
    , .\o0 (\ofunchan_0_Merge1$data )
  );
  
  \Merge2  #(
    .INPUTSIZE1(2),
    .OUTPUTSIZE(2),
    .INPUTSIZE0(2)
  ) \Merge2  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\x_plus_cons$irdy )
    , .\i0$data (\x_plus_cons$data )
    , .\i0$trdy (\x_plus_cons$trdy )
    , .\i1$irdy (\channel5$irdy )
    , .\i1$data (\channel5$data )
    , .\i1$trdy (\channel5$trdy )
    , .\o0$irdy (\channel6$irdy )
    , .\o0$data (\channel6$data )
    , .\o0$trdy (\channel6$trdy )
    , .\f$data (\ofunchan_0_Merge2$data )
    , .\sel (\sel_Merge2 )
  );
  
  \OFUN_0$LigeroRouter_0_0_2_2_2_Merge2  \ofun_0_Merge2  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\x_plus_cons$data )
    , .\i1$data (\channel5$data )
    , .\sel (\sel_Merge2 )
    , .\o0 (\ofunchan_0_Merge2$data )
  );
  
  \Merge2  #(
    .INPUTSIZE1(2),
    .OUTPUTSIZE(2),
    .INPUTSIZE0(2)
  ) \Merge3  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\y_min_cons$irdy )
    , .\i0$data (\y_min_cons$data )
    , .\i0$trdy (\y_min_cons$trdy )
    , .\i1$irdy (\y_plus_cons$irdy )
    , .\i1$data (\y_plus_cons$data )
    , .\i1$trdy (\y_plus_cons$trdy )
    , .\o0$irdy (\channel5$irdy )
    , .\o0$data (\channel5$data )
    , .\o0$trdy (\channel5$trdy )
    , .\f$data (\ofunchan_0_Merge3$data )
    , .\sel (\sel_Merge3 )
  );
  
  \OFUN_0$LigeroRouter_0_0_2_2_2_Merge3  \ofun_0_Merge3  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\y_min_cons$data )
    , .\i1$data (\y_plus_cons$data )
    , .\sel (\sel_Merge3 )
    , .\o0 (\ofunchan_0_Merge3$data )
  );
  
  \LoadBalancer4  #(
    .DATASIZE(2)
  ) \LoadBalancer1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\channel7$irdy )
    , .\i0$data (\channel7$data )
    , .\i0$trdy (\channel7$trdy )
    , .\o0$irdy (\x_min_inj$irdy )
    , .\o0$data (\x_min_inj$data )
    , .\o0$trdy (\x_min_inj$trdy )
    , .\o1$irdy (\x_plus_inj$irdy )
    , .\o1$data (\x_plus_inj$data )
    , .\o1$trdy (\x_plus_inj$trdy )
    , .\o2$irdy (\y_min_inj$irdy )
    , .\o2$data (\y_min_inj$data )
    , .\o2$trdy (\y_min_inj$trdy )
    , .\o3$irdy (\y_plus_inj$irdy )
    , .\o3$data (\y_plus_inj$data )
    , .\o3$trdy (\y_plus_inj$trdy )
  );
  
  \BBB_0_0_2_2_0_2  \BBB1  (
      .\clk (\clk ), .\rst (\rst ), .\t (\t )
    , .\bus_ins1$irdy (\channel1$irdy )
    , .\bus_ins1$data (\channel1$data )
    , .\bus_ins1$trdy (\channel1$trdy )
    , .\bus_ins2$irdy (\bus_ins2$irdy )
    , .\bus_ins2$data (\bus_ins2$data )
    , .\bus_ins2$trdy (\bus_ins2$trdy )
    , .\bus_ins3$irdy (\y_min_loop$irdy )
    , .\bus_ins3$data (\y_min_loop$data )
    , .\bus_ins3$trdy (\y_min_loop$trdy )
    , .\bus_ins4$irdy (\bus_ins6$irdy )
    , .\bus_ins4$data (\bus_ins6$data )
    , .\bus_ins4$trdy (\bus_ins6$trdy )
    , .\bus_outs1$irdy (\x_min_cons$irdy )
    , .\bus_outs1$data (\x_min_cons$data )
    , .\bus_outs1$trdy (\x_min_cons$trdy )
    , .\bus_outs2$irdy (\bus_outs2$irdy )
    , .\bus_outs2$data (\bus_outs2$data )
    , .\bus_outs2$trdy (\bus_outs2$trdy )
    , .\bus_outs3$irdy (\x_min_loop$irdy )
    , .\bus_outs3$data (\x_min_loop$data )
    , .\bus_outs3$trdy (\x_min_loop$trdy )
    , .\bus_outs4$irdy (\bus_outs6$irdy )
    , .\bus_outs4$data (\bus_outs6$data )
    , .\bus_outs4$trdy (\bus_outs6$trdy )
    , .\Sink1$unbound_trdy (\BBB1$Sink1$unbound_trdy )
    , .\Sink1$irdy (\BBB1$Sink1$irdy )
    , .\Sink1$data (\BBB1$Sink1$data )
    , .\RECEPTION1$CreditCounter1$PatientSource1$unbound_irdy (\BBB1$RECEPTION1$CreditCounter1$PatientSource1$unbound_irdy )
    , .\RECEPTION1$CreditCounter1$PatientSource1$unbound_data (\BBB1$RECEPTION1$CreditCounter1$PatientSource1$unbound_data )
    , .\RECEPTION1$CreditCounter1$PatientSource1$trdy (\BBB1$RECEPTION1$CreditCounter1$PatientSource1$trdy )
    , .\RECEPTION1$CreditCounter1$Sink1$unbound_trdy (\BBB1$RECEPTION1$CreditCounter1$Sink1$unbound_trdy )
    , .\RECEPTION1$CreditCounter1$Sink1$irdy (\BBB1$RECEPTION1$CreditCounter1$Sink1$irdy )
    , .\RECEPTION1$CreditCounter1$Sink1$data (\BBB1$RECEPTION1$CreditCounter1$Sink1$data )
  );
  
  \Latch$type4  \Latch1  (
      .\clk (\clk ), .\rst (\rst )
    , .\input$irdy (\x_min_inj$irdy )
    , .\input$data (\x_min_inj$data )
    , .\input$trdy (\x_min_inj$trdy )
    , .\output$irdy (\channel1$irdy )
    , .\output$data (\channel1$data )
    , .\output$trdy (\channel1$trdy )
  );
  
  \BBB_0_0_2_2_1_2  \BBB2  (
      .\clk (\clk ), .\rst (\rst ), .\t (\t )
    , .\bus_ins1$irdy (\channel2$irdy )
    , .\bus_ins1$data (\channel2$data )
    , .\bus_ins1$trdy (\channel2$trdy )
    , .\bus_ins2$irdy (\bus_ins3$irdy )
    , .\bus_ins2$data (\bus_ins3$data )
    , .\bus_ins2$trdy (\bus_ins3$trdy )
    , .\bus_ins3$irdy (\y_plus_loop$irdy )
    , .\bus_ins3$data (\y_plus_loop$data )
    , .\bus_ins3$trdy (\y_plus_loop$trdy )
    , .\bus_ins4$irdy (\bus_ins7$irdy )
    , .\bus_ins4$data (\bus_ins7$data )
    , .\bus_ins4$trdy (\bus_ins7$trdy )
    , .\bus_outs1$irdy (\x_plus_cons$irdy )
    , .\bus_outs1$data (\x_plus_cons$data )
    , .\bus_outs1$trdy (\x_plus_cons$trdy )
    , .\bus_outs2$irdy (\bus_outs3$irdy )
    , .\bus_outs2$data (\bus_outs3$data )
    , .\bus_outs2$trdy (\bus_outs3$trdy )
    , .\bus_outs3$irdy (\x_plus_loop$irdy )
    , .\bus_outs3$data (\x_plus_loop$data )
    , .\bus_outs3$trdy (\x_plus_loop$trdy )
    , .\bus_outs4$irdy (\bus_outs7$irdy )
    , .\bus_outs4$data (\bus_outs7$data )
    , .\bus_outs4$trdy (\bus_outs7$trdy )
    , .\Sink1$unbound_trdy (\BBB2$Sink1$unbound_trdy )
    , .\Sink1$irdy (\BBB2$Sink1$irdy )
    , .\Sink1$data (\BBB2$Sink1$data )
    , .\RECEPTION1$CreditCounter1$PatientSource1$unbound_irdy (\BBB2$RECEPTION1$CreditCounter1$PatientSource1$unbound_irdy )
    , .\RECEPTION1$CreditCounter1$PatientSource1$unbound_data (\BBB2$RECEPTION1$CreditCounter1$PatientSource1$unbound_data )
    , .\RECEPTION1$CreditCounter1$PatientSource1$trdy (\BBB2$RECEPTION1$CreditCounter1$PatientSource1$trdy )
    , .\RECEPTION1$CreditCounter1$Sink1$unbound_trdy (\BBB2$RECEPTION1$CreditCounter1$Sink1$unbound_trdy )
    , .\RECEPTION1$CreditCounter1$Sink1$irdy (\BBB2$RECEPTION1$CreditCounter1$Sink1$irdy )
    , .\RECEPTION1$CreditCounter1$Sink1$data (\BBB2$RECEPTION1$CreditCounter1$Sink1$data )
  );
  
  \Latch$type4  \Latch2  (
      .\clk (\clk ), .\rst (\rst )
    , .\input$irdy (\x_plus_inj$irdy )
    , .\input$data (\x_plus_inj$data )
    , .\input$trdy (\x_plus_inj$trdy )
    , .\output$irdy (\channel2$irdy )
    , .\output$data (\channel2$data )
    , .\output$trdy (\channel2$trdy )
  );
  
  \BBB_0_0_2_2_2_2  \BBB3  (
      .\clk (\clk ), .\rst (\rst ), .\t (\t )
    , .\bus_ins1$irdy (\channel3$irdy )
    , .\bus_ins1$data (\channel3$data )
    , .\bus_ins1$trdy (\channel3$trdy )
    , .\bus_ins2$irdy (\bus_ins4$irdy )
    , .\bus_ins2$data (\bus_ins4$data )
    , .\bus_ins2$trdy (\bus_ins4$trdy )
    , .\bus_ins3$irdy (\x_plus_loop$irdy )
    , .\bus_ins3$data (\x_plus_loop$data )
    , .\bus_ins3$trdy (\x_plus_loop$trdy )
    , .\bus_ins4$irdy (\bus_ins8$irdy )
    , .\bus_ins4$data (\bus_ins8$data )
    , .\bus_ins4$trdy (\bus_ins8$trdy )
    , .\bus_outs1$irdy (\y_min_cons$irdy )
    , .\bus_outs1$data (\y_min_cons$data )
    , .\bus_outs1$trdy (\y_min_cons$trdy )
    , .\bus_outs2$irdy (\bus_outs4$irdy )
    , .\bus_outs2$data (\bus_outs4$data )
    , .\bus_outs2$trdy (\bus_outs4$trdy )
    , .\bus_outs3$irdy (\y_min_loop$irdy )
    , .\bus_outs3$data (\y_min_loop$data )
    , .\bus_outs3$trdy (\y_min_loop$trdy )
    , .\bus_outs4$irdy (\bus_outs8$irdy )
    , .\bus_outs4$data (\bus_outs8$data )
    , .\bus_outs4$trdy (\bus_outs8$trdy )
    , .\Sink1$unbound_trdy (\BBB3$Sink1$unbound_trdy )
    , .\Sink1$irdy (\BBB3$Sink1$irdy )
    , .\Sink1$data (\BBB3$Sink1$data )
    , .\RECEPTION1$CreditCounter1$PatientSource1$unbound_irdy (\BBB3$RECEPTION1$CreditCounter1$PatientSource1$unbound_irdy )
    , .\RECEPTION1$CreditCounter1$PatientSource1$unbound_data (\BBB3$RECEPTION1$CreditCounter1$PatientSource1$unbound_data )
    , .\RECEPTION1$CreditCounter1$PatientSource1$trdy (\BBB3$RECEPTION1$CreditCounter1$PatientSource1$trdy )
    , .\RECEPTION1$CreditCounter1$Sink1$unbound_trdy (\BBB3$RECEPTION1$CreditCounter1$Sink1$unbound_trdy )
    , .\RECEPTION1$CreditCounter1$Sink1$irdy (\BBB3$RECEPTION1$CreditCounter1$Sink1$irdy )
    , .\RECEPTION1$CreditCounter1$Sink1$data (\BBB3$RECEPTION1$CreditCounter1$Sink1$data )
  );
  
  \Latch$type4  \Latch3  (
      .\clk (\clk ), .\rst (\rst )
    , .\input$irdy (\y_min_inj$irdy )
    , .\input$data (\y_min_inj$data )
    , .\input$trdy (\y_min_inj$trdy )
    , .\output$irdy (\channel3$irdy )
    , .\output$data (\channel3$data )
    , .\output$trdy (\channel3$trdy )
  );
  
  \BBB_0_0_2_2_3_2  \BBB4  (
      .\clk (\clk ), .\rst (\rst ), .\t (\t )
    , .\bus_ins1$irdy (\channel4$irdy )
    , .\bus_ins1$data (\channel4$data )
    , .\bus_ins1$trdy (\channel4$trdy )
    , .\bus_ins2$irdy (\bus_ins5$irdy )
    , .\bus_ins2$data (\bus_ins5$data )
    , .\bus_ins2$trdy (\bus_ins5$trdy )
    , .\bus_ins3$irdy (\x_min_loop$irdy )
    , .\bus_ins3$data (\x_min_loop$data )
    , .\bus_ins3$trdy (\x_min_loop$trdy )
    , .\bus_ins4$irdy (\bus_ins9$irdy )
    , .\bus_ins4$data (\bus_ins9$data )
    , .\bus_ins4$trdy (\bus_ins9$trdy )
    , .\bus_outs1$irdy (\y_plus_cons$irdy )
    , .\bus_outs1$data (\y_plus_cons$data )
    , .\bus_outs1$trdy (\y_plus_cons$trdy )
    , .\bus_outs2$irdy (\bus_outs5$irdy )
    , .\bus_outs2$data (\bus_outs5$data )
    , .\bus_outs2$trdy (\bus_outs5$trdy )
    , .\bus_outs3$irdy (\y_plus_loop$irdy )
    , .\bus_outs3$data (\y_plus_loop$data )
    , .\bus_outs3$trdy (\y_plus_loop$trdy )
    , .\bus_outs4$irdy (\bus_outs9$irdy )
    , .\bus_outs4$data (\bus_outs9$data )
    , .\bus_outs4$trdy (\bus_outs9$trdy )
    , .\Sink1$unbound_trdy (\BBB4$Sink1$unbound_trdy )
    , .\Sink1$irdy (\BBB4$Sink1$irdy )
    , .\Sink1$data (\BBB4$Sink1$data )
    , .\RECEPTION1$CreditCounter1$PatientSource1$unbound_irdy (\BBB4$RECEPTION1$CreditCounter1$PatientSource1$unbound_irdy )
    , .\RECEPTION1$CreditCounter1$PatientSource1$unbound_data (\BBB4$RECEPTION1$CreditCounter1$PatientSource1$unbound_data )
    , .\RECEPTION1$CreditCounter1$PatientSource1$trdy (\BBB4$RECEPTION1$CreditCounter1$PatientSource1$trdy )
    , .\RECEPTION1$CreditCounter1$Sink1$unbound_trdy (\BBB4$RECEPTION1$CreditCounter1$Sink1$unbound_trdy )
    , .\RECEPTION1$CreditCounter1$Sink1$irdy (\BBB4$RECEPTION1$CreditCounter1$Sink1$irdy )
    , .\RECEPTION1$CreditCounter1$Sink1$data (\BBB4$RECEPTION1$CreditCounter1$Sink1$data )
  );
  
  \Latch$type4  \Latch4  (
      .\clk (\clk ), .\rst (\rst )
    , .\input$irdy (\y_plus_inj$irdy )
    , .\input$data (\y_plus_inj$data )
    , .\input$trdy (\y_plus_inj$trdy )
    , .\output$irdy (\channel4$irdy )
    , .\output$data (\channel4$data )
    , .\output$trdy (\channel4$trdy )
  );
  
  \Latch$type4  \Latch5  (
      .\clk (\clk ), .\rst (\rst )
    , .\input$irdy (\bus_ins1$irdy )
    , .\input$data (\bus_ins1$data )
    , .\input$trdy (\bus_ins1$trdy )
    , .\output$irdy (\channel7$irdy )
    , .\output$data (\channel7$data )
    , .\output$trdy (\channel7$trdy )
  );
  
endmodule


//
// LigeroRouter_0_0_2_2_2 switch functions
//
module \OFUN_0$LigeroRouter_0_0_2_2_2_Merge1 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , input [1:0] \i1$data 
    , input \sel 
    , output [1:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[0:0] \f$bool$arg0$disj  = \sel  ;
  wire[0:0] \f$bool$arg0  = \f$bool$arg0$disj [0:0] ;
  wire[0:0] \f$bool$arg1  = 1'd0 ;
  wire \f$bool  = \f$bool$arg0  == \f$bool$arg1  ;
  wire[1:0] \f$true  = \i0$data  ;
  wire[0:0] \f$false$bool$arg0$disj  = \sel  ;
  wire[0:0] \f$false$bool$arg0  = \f$false$bool$arg0$disj [0:0] ;
  wire[0:0] \f$false$bool$arg1  = 1'd1 ;
  wire \f$false$bool  = \f$false$bool$arg0  == \f$false$bool$arg1  ;
  wire[1:0] \f$false$true  = \i1$data  ;
  wire[1:0] \f$false$false  = \i0$data  ;
  wire[1:0] \f$false  = ( \f$false$bool  ? \f$false$true  : \f$false$false  ) ;
  wire[1:0] \f  = ( \f$bool  ? \f$true  : \f$false  ) ;
  
  assign \o0  = \f  ;
endmodule

module \OFUN_0$LigeroRouter_0_0_2_2_2_Merge2 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , input [1:0] \i1$data 
    , input \sel 
    , output [1:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[0:0] \f$bool$arg0$disj  = \sel  ;
  wire[0:0] \f$bool$arg0  = \f$bool$arg0$disj [0:0] ;
  wire[0:0] \f$bool$arg1  = 1'd0 ;
  wire \f$bool  = \f$bool$arg0  == \f$bool$arg1  ;
  wire[1:0] \f$true  = \i0$data  ;
  wire[0:0] \f$false$bool$arg0$disj  = \sel  ;
  wire[0:0] \f$false$bool$arg0  = \f$false$bool$arg0$disj [0:0] ;
  wire[0:0] \f$false$bool$arg1  = 1'd1 ;
  wire \f$false$bool  = \f$false$bool$arg0  == \f$false$bool$arg1  ;
  wire[1:0] \f$false$true  = \i1$data  ;
  wire[1:0] \f$false$false  = \i0$data  ;
  wire[1:0] \f$false  = ( \f$false$bool  ? \f$false$true  : \f$false$false  ) ;
  wire[1:0] \f  = ( \f$bool  ? \f$true  : \f$false  ) ;
  
  assign \o0  = \f  ;
endmodule

module \OFUN_0$LigeroRouter_0_0_2_2_2_Merge3 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , input [1:0] \i1$data 
    , input \sel 
    , output [1:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[0:0] \f$bool$arg0$disj  = \sel  ;
  wire[0:0] \f$bool$arg0  = \f$bool$arg0$disj [0:0] ;
  wire[0:0] \f$bool$arg1  = 1'd0 ;
  wire \f$bool  = \f$bool$arg0  == \f$bool$arg1  ;
  wire[1:0] \f$true  = \i0$data  ;
  wire[0:0] \f$false$bool$arg0$disj  = \sel  ;
  wire[0:0] \f$false$bool$arg0  = \f$false$bool$arg0$disj [0:0] ;
  wire[0:0] \f$false$bool$arg1  = 1'd1 ;
  wire \f$false$bool  = \f$false$bool$arg0  == \f$false$bool$arg1  ;
  wire[1:0] \f$false$true  = \i1$data  ;
  wire[1:0] \f$false$false  = \i0$data  ;
  wire[1:0] \f$false  = ( \f$false$bool  ? \f$false$true  : \f$false$false  ) ;
  wire[1:0] \f  = ( \f$bool  ? \f$true  : \f$false  ) ;
  
  assign \o0  = \f  ;
endmodule

module \LigeroRouter_0_1_2_2_2 (
      input \clk , input \rst , input [63:0] \t 
    , input \bus_ins1$irdy , input [1:0] \bus_ins1$data , output \bus_ins1$trdy 
    , input \bus_ins2$irdy , input [1:0] \bus_ins2$data , output \bus_ins2$trdy 
    , input \bus_ins3$irdy , input [1:0] \bus_ins3$data , output \bus_ins3$trdy 
    , input \bus_ins4$irdy , input [1:0] \bus_ins4$data , output \bus_ins4$trdy 
    , input \bus_ins5$irdy , input [1:0] \bus_ins5$data , output \bus_ins5$trdy 
    , input \bus_ins6$irdy , input [0:0] \bus_ins6$data , output \bus_ins6$trdy 
    , input \bus_ins7$irdy , input [0:0] \bus_ins7$data , output \bus_ins7$trdy 
    , input \bus_ins8$irdy , input [0:0] \bus_ins8$data , output \bus_ins8$trdy 
    , input \bus_ins9$irdy , input [0:0] \bus_ins9$data , output \bus_ins9$trdy 
    , output \bus_outs1$irdy , output [1:0] \bus_outs1$data , input \bus_outs1$trdy 
    , output \bus_outs2$irdy , output [1:0] \bus_outs2$data , input \bus_outs2$trdy 
    , output \bus_outs3$irdy , output [1:0] \bus_outs3$data , input \bus_outs3$trdy 
    , output \bus_outs4$irdy , output [1:0] \bus_outs4$data , input \bus_outs4$trdy 
    , output \bus_outs5$irdy , output [1:0] \bus_outs5$data , input \bus_outs5$trdy 
    , output \bus_outs6$irdy , output [0:0] \bus_outs6$data , input \bus_outs6$trdy 
    , output \bus_outs7$irdy , output [0:0] \bus_outs7$data , input \bus_outs7$trdy 
    , output \bus_outs8$irdy , output [0:0] \bus_outs8$data , input \bus_outs8$trdy 
    , output \bus_outs9$irdy , output [0:0] \bus_outs9$data , input \bus_outs9$trdy 
    , input \BBB1$Sink1$unbound_trdy 
    , output \BBB1$Sink1$irdy 
    , output [1:0] \BBB1$Sink1$data 
    , input \BBB1$RECEPTION1$CreditCounter1$PatientSource1$unbound_irdy 
    , input [0:0] \BBB1$RECEPTION1$CreditCounter1$PatientSource1$unbound_data 
    , output \BBB1$RECEPTION1$CreditCounter1$PatientSource1$trdy 
    , input \BBB1$RECEPTION1$CreditCounter1$Sink1$unbound_trdy 
    , output \BBB1$RECEPTION1$CreditCounter1$Sink1$irdy 
    , output [0:0] \BBB1$RECEPTION1$CreditCounter1$Sink1$data 
    , input \BBB2$Sink1$unbound_trdy 
    , output \BBB2$Sink1$irdy 
    , output [1:0] \BBB2$Sink1$data 
    , input \BBB2$RECEPTION1$CreditCounter1$PatientSource1$unbound_irdy 
    , input [0:0] \BBB2$RECEPTION1$CreditCounter1$PatientSource1$unbound_data 
    , output \BBB2$RECEPTION1$CreditCounter1$PatientSource1$trdy 
    , input \BBB2$RECEPTION1$CreditCounter1$Sink1$unbound_trdy 
    , output \BBB2$RECEPTION1$CreditCounter1$Sink1$irdy 
    , output [0:0] \BBB2$RECEPTION1$CreditCounter1$Sink1$data 
    , input \BBB3$Sink1$unbound_trdy 
    , output \BBB3$Sink1$irdy 
    , output [1:0] \BBB3$Sink1$data 
    , input \BBB3$RECEPTION1$CreditCounter1$PatientSource1$unbound_irdy 
    , input [0:0] \BBB3$RECEPTION1$CreditCounter1$PatientSource1$unbound_data 
    , output \BBB3$RECEPTION1$CreditCounter1$PatientSource1$trdy 
    , input \BBB3$RECEPTION1$CreditCounter1$Sink1$unbound_trdy 
    , output \BBB3$RECEPTION1$CreditCounter1$Sink1$irdy 
    , output [0:0] \BBB3$RECEPTION1$CreditCounter1$Sink1$data 
    , input \BBB4$Sink1$unbound_trdy 
    , output \BBB4$Sink1$irdy 
    , output [1:0] \BBB4$Sink1$data 
    , input \BBB4$RECEPTION1$CreditCounter1$PatientSource1$unbound_irdy 
    , input [0:0] \BBB4$RECEPTION1$CreditCounter1$PatientSource1$unbound_data 
    , output \BBB4$RECEPTION1$CreditCounter1$PatientSource1$trdy 
    , input \BBB4$RECEPTION1$CreditCounter1$Sink1$unbound_trdy 
    , output \BBB4$RECEPTION1$CreditCounter1$Sink1$irdy 
    , output [0:0] \BBB4$RECEPTION1$CreditCounter1$Sink1$data 
  );
  
  //
  // Channel declarations
  //
  wire \y_plus_loop$irdy  ;
  wire [1:0] \y_plus_loop$data  ;
  wire \y_plus_loop$trdy  ;
  wire \y_plus_cons$irdy  ;
  wire [1:0] \y_plus_cons$data  ;
  wire \y_plus_cons$trdy  ;
  wire \y_min_loop$irdy  ;
  wire [1:0] \y_min_loop$data  ;
  wire \y_min_loop$trdy  ;
  wire \y_min_cons$irdy  ;
  wire [1:0] \y_min_cons$data  ;
  wire \y_min_cons$trdy  ;
  wire \x_plus_loop$irdy  ;
  wire [1:0] \x_plus_loop$data  ;
  wire \x_plus_loop$trdy  ;
  wire \x_plus_cons$irdy  ;
  wire [1:0] \x_plus_cons$data  ;
  wire \x_plus_cons$trdy  ;
  wire \x_min_loop$irdy  ;
  wire [1:0] \x_min_loop$data  ;
  wire \x_min_loop$trdy  ;
  wire \x_min_cons$irdy  ;
  wire [1:0] \x_min_cons$data  ;
  wire \x_min_cons$trdy  ;
  wire \channel1$irdy  ;
  wire [1:0] \channel1$data  ;
  wire \channel1$trdy  ;
  wire \channel2$irdy  ;
  wire [1:0] \channel2$data  ;
  wire \channel2$trdy  ;
  wire \channel3$irdy  ;
  wire [1:0] \channel3$data  ;
  wire \channel3$trdy  ;
  wire \channel4$irdy  ;
  wire [1:0] \channel4$data  ;
  wire \channel4$trdy  ;
  wire \channel6$irdy  ;
  wire [1:0] \channel6$data  ;
  wire \channel6$trdy  ;
  wire \channel5$irdy  ;
  wire [1:0] \channel5$data  ;
  wire \channel5$trdy  ;
  wire \x_min_inj$irdy  ;
  wire [1:0] \x_min_inj$data  ;
  wire \x_min_inj$trdy  ;
  wire \x_plus_inj$irdy  ;
  wire [1:0] \x_plus_inj$data  ;
  wire \x_plus_inj$trdy  ;
  wire \y_min_inj$irdy  ;
  wire [1:0] \y_min_inj$data  ;
  wire \y_min_inj$trdy  ;
  wire \y_plus_inj$irdy  ;
  wire [1:0] \y_plus_inj$data  ;
  wire \y_plus_inj$trdy  ;
  wire \channel7$irdy  ;
  wire [1:0] \channel7$data  ;
  wire \channel7$trdy  ;
  
  //
  // Function Channels
  //
  wire [1:0] \ofunchan_0_Merge1$data  ;
  wire \sel_Merge1  ;
  wire [1:0] \ofunchan_0_Merge2$data  ;
  wire \sel_Merge2  ;
  wire [1:0] \ofunchan_0_Merge3$data  ;
  wire \sel_Merge3  ;
  
  //
  // Component and Macro instantiations
  //
  \Merge2  #(
    .INPUTSIZE1(2),
    .OUTPUTSIZE(2),
    .INPUTSIZE0(2)
  ) \Merge1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\x_min_cons$irdy )
    , .\i0$data (\x_min_cons$data )
    , .\i0$trdy (\x_min_cons$trdy )
    , .\i1$irdy (\channel6$irdy )
    , .\i1$data (\channel6$data )
    , .\i1$trdy (\channel6$trdy )
    , .\o0$irdy (\bus_outs1$irdy )
    , .\o0$data (\bus_outs1$data )
    , .\o0$trdy (\bus_outs1$trdy )
    , .\f$data (\ofunchan_0_Merge1$data )
    , .\sel (\sel_Merge1 )
  );
  
  \OFUN_0$LigeroRouter_0_1_2_2_2_Merge1  \ofun_0_Merge1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\x_min_cons$data )
    , .\i1$data (\channel6$data )
    , .\sel (\sel_Merge1 )
    , .\o0 (\ofunchan_0_Merge1$data )
  );
  
  \Merge2  #(
    .INPUTSIZE1(2),
    .OUTPUTSIZE(2),
    .INPUTSIZE0(2)
  ) \Merge2  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\x_plus_cons$irdy )
    , .\i0$data (\x_plus_cons$data )
    , .\i0$trdy (\x_plus_cons$trdy )
    , .\i1$irdy (\channel5$irdy )
    , .\i1$data (\channel5$data )
    , .\i1$trdy (\channel5$trdy )
    , .\o0$irdy (\channel6$irdy )
    , .\o0$data (\channel6$data )
    , .\o0$trdy (\channel6$trdy )
    , .\f$data (\ofunchan_0_Merge2$data )
    , .\sel (\sel_Merge2 )
  );
  
  \OFUN_0$LigeroRouter_0_1_2_2_2_Merge2  \ofun_0_Merge2  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\x_plus_cons$data )
    , .\i1$data (\channel5$data )
    , .\sel (\sel_Merge2 )
    , .\o0 (\ofunchan_0_Merge2$data )
  );
  
  \Merge2  #(
    .INPUTSIZE1(2),
    .OUTPUTSIZE(2),
    .INPUTSIZE0(2)
  ) \Merge3  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\y_min_cons$irdy )
    , .\i0$data (\y_min_cons$data )
    , .\i0$trdy (\y_min_cons$trdy )
    , .\i1$irdy (\y_plus_cons$irdy )
    , .\i1$data (\y_plus_cons$data )
    , .\i1$trdy (\y_plus_cons$trdy )
    , .\o0$irdy (\channel5$irdy )
    , .\o0$data (\channel5$data )
    , .\o0$trdy (\channel5$trdy )
    , .\f$data (\ofunchan_0_Merge3$data )
    , .\sel (\sel_Merge3 )
  );
  
  \OFUN_0$LigeroRouter_0_1_2_2_2_Merge3  \ofun_0_Merge3  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\y_min_cons$data )
    , .\i1$data (\y_plus_cons$data )
    , .\sel (\sel_Merge3 )
    , .\o0 (\ofunchan_0_Merge3$data )
  );
  
  \LoadBalancer4  #(
    .DATASIZE(2)
  ) \LoadBalancer1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\channel7$irdy )
    , .\i0$data (\channel7$data )
    , .\i0$trdy (\channel7$trdy )
    , .\o0$irdy (\x_min_inj$irdy )
    , .\o0$data (\x_min_inj$data )
    , .\o0$trdy (\x_min_inj$trdy )
    , .\o1$irdy (\x_plus_inj$irdy )
    , .\o1$data (\x_plus_inj$data )
    , .\o1$trdy (\x_plus_inj$trdy )
    , .\o2$irdy (\y_min_inj$irdy )
    , .\o2$data (\y_min_inj$data )
    , .\o2$trdy (\y_min_inj$trdy )
    , .\o3$irdy (\y_plus_inj$irdy )
    , .\o3$data (\y_plus_inj$data )
    , .\o3$trdy (\y_plus_inj$trdy )
  );
  
  \BBB_0_1_2_2_0_2  \BBB1  (
      .\clk (\clk ), .\rst (\rst ), .\t (\t )
    , .\bus_ins1$irdy (\channel1$irdy )
    , .\bus_ins1$data (\channel1$data )
    , .\bus_ins1$trdy (\channel1$trdy )
    , .\bus_ins2$irdy (\bus_ins2$irdy )
    , .\bus_ins2$data (\bus_ins2$data )
    , .\bus_ins2$trdy (\bus_ins2$trdy )
    , .\bus_ins3$irdy (\y_min_loop$irdy )
    , .\bus_ins3$data (\y_min_loop$data )
    , .\bus_ins3$trdy (\y_min_loop$trdy )
    , .\bus_ins4$irdy (\bus_ins6$irdy )
    , .\bus_ins4$data (\bus_ins6$data )
    , .\bus_ins4$trdy (\bus_ins6$trdy )
    , .\bus_outs1$irdy (\x_min_cons$irdy )
    , .\bus_outs1$data (\x_min_cons$data )
    , .\bus_outs1$trdy (\x_min_cons$trdy )
    , .\bus_outs2$irdy (\bus_outs2$irdy )
    , .\bus_outs2$data (\bus_outs2$data )
    , .\bus_outs2$trdy (\bus_outs2$trdy )
    , .\bus_outs3$irdy (\x_min_loop$irdy )
    , .\bus_outs3$data (\x_min_loop$data )
    , .\bus_outs3$trdy (\x_min_loop$trdy )
    , .\bus_outs4$irdy (\bus_outs6$irdy )
    , .\bus_outs4$data (\bus_outs6$data )
    , .\bus_outs4$trdy (\bus_outs6$trdy )
    , .\Sink1$unbound_trdy (\BBB1$Sink1$unbound_trdy )
    , .\Sink1$irdy (\BBB1$Sink1$irdy )
    , .\Sink1$data (\BBB1$Sink1$data )
    , .\RECEPTION1$CreditCounter1$PatientSource1$unbound_irdy (\BBB1$RECEPTION1$CreditCounter1$PatientSource1$unbound_irdy )
    , .\RECEPTION1$CreditCounter1$PatientSource1$unbound_data (\BBB1$RECEPTION1$CreditCounter1$PatientSource1$unbound_data )
    , .\RECEPTION1$CreditCounter1$PatientSource1$trdy (\BBB1$RECEPTION1$CreditCounter1$PatientSource1$trdy )
    , .\RECEPTION1$CreditCounter1$Sink1$unbound_trdy (\BBB1$RECEPTION1$CreditCounter1$Sink1$unbound_trdy )
    , .\RECEPTION1$CreditCounter1$Sink1$irdy (\BBB1$RECEPTION1$CreditCounter1$Sink1$irdy )
    , .\RECEPTION1$CreditCounter1$Sink1$data (\BBB1$RECEPTION1$CreditCounter1$Sink1$data )
  );
  
  \Latch$type4  \Latch1  (
      .\clk (\clk ), .\rst (\rst )
    , .\input$irdy (\x_min_inj$irdy )
    , .\input$data (\x_min_inj$data )
    , .\input$trdy (\x_min_inj$trdy )
    , .\output$irdy (\channel1$irdy )
    , .\output$data (\channel1$data )
    , .\output$trdy (\channel1$trdy )
  );
  
  \BBB_0_1_2_2_1_2  \BBB2  (
      .\clk (\clk ), .\rst (\rst ), .\t (\t )
    , .\bus_ins1$irdy (\channel2$irdy )
    , .\bus_ins1$data (\channel2$data )
    , .\bus_ins1$trdy (\channel2$trdy )
    , .\bus_ins2$irdy (\bus_ins3$irdy )
    , .\bus_ins2$data (\bus_ins3$data )
    , .\bus_ins2$trdy (\bus_ins3$trdy )
    , .\bus_ins3$irdy (\y_plus_loop$irdy )
    , .\bus_ins3$data (\y_plus_loop$data )
    , .\bus_ins3$trdy (\y_plus_loop$trdy )
    , .\bus_ins4$irdy (\bus_ins7$irdy )
    , .\bus_ins4$data (\bus_ins7$data )
    , .\bus_ins4$trdy (\bus_ins7$trdy )
    , .\bus_outs1$irdy (\x_plus_cons$irdy )
    , .\bus_outs1$data (\x_plus_cons$data )
    , .\bus_outs1$trdy (\x_plus_cons$trdy )
    , .\bus_outs2$irdy (\bus_outs3$irdy )
    , .\bus_outs2$data (\bus_outs3$data )
    , .\bus_outs2$trdy (\bus_outs3$trdy )
    , .\bus_outs3$irdy (\x_plus_loop$irdy )
    , .\bus_outs3$data (\x_plus_loop$data )
    , .\bus_outs3$trdy (\x_plus_loop$trdy )
    , .\bus_outs4$irdy (\bus_outs7$irdy )
    , .\bus_outs4$data (\bus_outs7$data )
    , .\bus_outs4$trdy (\bus_outs7$trdy )
    , .\Sink1$unbound_trdy (\BBB2$Sink1$unbound_trdy )
    , .\Sink1$irdy (\BBB2$Sink1$irdy )
    , .\Sink1$data (\BBB2$Sink1$data )
    , .\RECEPTION1$CreditCounter1$PatientSource1$unbound_irdy (\BBB2$RECEPTION1$CreditCounter1$PatientSource1$unbound_irdy )
    , .\RECEPTION1$CreditCounter1$PatientSource1$unbound_data (\BBB2$RECEPTION1$CreditCounter1$PatientSource1$unbound_data )
    , .\RECEPTION1$CreditCounter1$PatientSource1$trdy (\BBB2$RECEPTION1$CreditCounter1$PatientSource1$trdy )
    , .\RECEPTION1$CreditCounter1$Sink1$unbound_trdy (\BBB2$RECEPTION1$CreditCounter1$Sink1$unbound_trdy )
    , .\RECEPTION1$CreditCounter1$Sink1$irdy (\BBB2$RECEPTION1$CreditCounter1$Sink1$irdy )
    , .\RECEPTION1$CreditCounter1$Sink1$data (\BBB2$RECEPTION1$CreditCounter1$Sink1$data )
  );
  
  \Latch$type4  \Latch2  (
      .\clk (\clk ), .\rst (\rst )
    , .\input$irdy (\x_plus_inj$irdy )
    , .\input$data (\x_plus_inj$data )
    , .\input$trdy (\x_plus_inj$trdy )
    , .\output$irdy (\channel2$irdy )
    , .\output$data (\channel2$data )
    , .\output$trdy (\channel2$trdy )
  );
  
  \BBB_0_1_2_2_2_2  \BBB3  (
      .\clk (\clk ), .\rst (\rst ), .\t (\t )
    , .\bus_ins1$irdy (\channel3$irdy )
    , .\bus_ins1$data (\channel3$data )
    , .\bus_ins1$trdy (\channel3$trdy )
    , .\bus_ins2$irdy (\bus_ins4$irdy )
    , .\bus_ins2$data (\bus_ins4$data )
    , .\bus_ins2$trdy (\bus_ins4$trdy )
    , .\bus_ins3$irdy (\x_plus_loop$irdy )
    , .\bus_ins3$data (\x_plus_loop$data )
    , .\bus_ins3$trdy (\x_plus_loop$trdy )
    , .\bus_ins4$irdy (\bus_ins8$irdy )
    , .\bus_ins4$data (\bus_ins8$data )
    , .\bus_ins4$trdy (\bus_ins8$trdy )
    , .\bus_outs1$irdy (\y_min_cons$irdy )
    , .\bus_outs1$data (\y_min_cons$data )
    , .\bus_outs1$trdy (\y_min_cons$trdy )
    , .\bus_outs2$irdy (\bus_outs4$irdy )
    , .\bus_outs2$data (\bus_outs4$data )
    , .\bus_outs2$trdy (\bus_outs4$trdy )
    , .\bus_outs3$irdy (\y_min_loop$irdy )
    , .\bus_outs3$data (\y_min_loop$data )
    , .\bus_outs3$trdy (\y_min_loop$trdy )
    , .\bus_outs4$irdy (\bus_outs8$irdy )
    , .\bus_outs4$data (\bus_outs8$data )
    , .\bus_outs4$trdy (\bus_outs8$trdy )
    , .\Sink1$unbound_trdy (\BBB3$Sink1$unbound_trdy )
    , .\Sink1$irdy (\BBB3$Sink1$irdy )
    , .\Sink1$data (\BBB3$Sink1$data )
    , .\RECEPTION1$CreditCounter1$PatientSource1$unbound_irdy (\BBB3$RECEPTION1$CreditCounter1$PatientSource1$unbound_irdy )
    , .\RECEPTION1$CreditCounter1$PatientSource1$unbound_data (\BBB3$RECEPTION1$CreditCounter1$PatientSource1$unbound_data )
    , .\RECEPTION1$CreditCounter1$PatientSource1$trdy (\BBB3$RECEPTION1$CreditCounter1$PatientSource1$trdy )
    , .\RECEPTION1$CreditCounter1$Sink1$unbound_trdy (\BBB3$RECEPTION1$CreditCounter1$Sink1$unbound_trdy )
    , .\RECEPTION1$CreditCounter1$Sink1$irdy (\BBB3$RECEPTION1$CreditCounter1$Sink1$irdy )
    , .\RECEPTION1$CreditCounter1$Sink1$data (\BBB3$RECEPTION1$CreditCounter1$Sink1$data )
  );
  
  \Latch$type4  \Latch3  (
      .\clk (\clk ), .\rst (\rst )
    , .\input$irdy (\y_min_inj$irdy )
    , .\input$data (\y_min_inj$data )
    , .\input$trdy (\y_min_inj$trdy )
    , .\output$irdy (\channel3$irdy )
    , .\output$data (\channel3$data )
    , .\output$trdy (\channel3$trdy )
  );
  
  \BBB_0_1_2_2_3_2  \BBB4  (
      .\clk (\clk ), .\rst (\rst ), .\t (\t )
    , .\bus_ins1$irdy (\channel4$irdy )
    , .\bus_ins1$data (\channel4$data )
    , .\bus_ins1$trdy (\channel4$trdy )
    , .\bus_ins2$irdy (\bus_ins5$irdy )
    , .\bus_ins2$data (\bus_ins5$data )
    , .\bus_ins2$trdy (\bus_ins5$trdy )
    , .\bus_ins3$irdy (\x_min_loop$irdy )
    , .\bus_ins3$data (\x_min_loop$data )
    , .\bus_ins3$trdy (\x_min_loop$trdy )
    , .\bus_ins4$irdy (\bus_ins9$irdy )
    , .\bus_ins4$data (\bus_ins9$data )
    , .\bus_ins4$trdy (\bus_ins9$trdy )
    , .\bus_outs1$irdy (\y_plus_cons$irdy )
    , .\bus_outs1$data (\y_plus_cons$data )
    , .\bus_outs1$trdy (\y_plus_cons$trdy )
    , .\bus_outs2$irdy (\bus_outs5$irdy )
    , .\bus_outs2$data (\bus_outs5$data )
    , .\bus_outs2$trdy (\bus_outs5$trdy )
    , .\bus_outs3$irdy (\y_plus_loop$irdy )
    , .\bus_outs3$data (\y_plus_loop$data )
    , .\bus_outs3$trdy (\y_plus_loop$trdy )
    , .\bus_outs4$irdy (\bus_outs9$irdy )
    , .\bus_outs4$data (\bus_outs9$data )
    , .\bus_outs4$trdy (\bus_outs9$trdy )
    , .\Sink1$unbound_trdy (\BBB4$Sink1$unbound_trdy )
    , .\Sink1$irdy (\BBB4$Sink1$irdy )
    , .\Sink1$data (\BBB4$Sink1$data )
    , .\RECEPTION1$CreditCounter1$PatientSource1$unbound_irdy (\BBB4$RECEPTION1$CreditCounter1$PatientSource1$unbound_irdy )
    , .\RECEPTION1$CreditCounter1$PatientSource1$unbound_data (\BBB4$RECEPTION1$CreditCounter1$PatientSource1$unbound_data )
    , .\RECEPTION1$CreditCounter1$PatientSource1$trdy (\BBB4$RECEPTION1$CreditCounter1$PatientSource1$trdy )
    , .\RECEPTION1$CreditCounter1$Sink1$unbound_trdy (\BBB4$RECEPTION1$CreditCounter1$Sink1$unbound_trdy )
    , .\RECEPTION1$CreditCounter1$Sink1$irdy (\BBB4$RECEPTION1$CreditCounter1$Sink1$irdy )
    , .\RECEPTION1$CreditCounter1$Sink1$data (\BBB4$RECEPTION1$CreditCounter1$Sink1$data )
  );
  
  \Latch$type4  \Latch4  (
      .\clk (\clk ), .\rst (\rst )
    , .\input$irdy (\y_plus_inj$irdy )
    , .\input$data (\y_plus_inj$data )
    , .\input$trdy (\y_plus_inj$trdy )
    , .\output$irdy (\channel4$irdy )
    , .\output$data (\channel4$data )
    , .\output$trdy (\channel4$trdy )
  );
  
  \Latch$type4  \Latch5  (
      .\clk (\clk ), .\rst (\rst )
    , .\input$irdy (\bus_ins1$irdy )
    , .\input$data (\bus_ins1$data )
    , .\input$trdy (\bus_ins1$trdy )
    , .\output$irdy (\channel7$irdy )
    , .\output$data (\channel7$data )
    , .\output$trdy (\channel7$trdy )
  );
  
endmodule


//
// LigeroRouter_0_1_2_2_2 switch functions
//
module \OFUN_0$LigeroRouter_0_1_2_2_2_Merge1 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , input [1:0] \i1$data 
    , input \sel 
    , output [1:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[0:0] \f$bool$arg0$disj  = \sel  ;
  wire[0:0] \f$bool$arg0  = \f$bool$arg0$disj [0:0] ;
  wire[0:0] \f$bool$arg1  = 1'd0 ;
  wire \f$bool  = \f$bool$arg0  == \f$bool$arg1  ;
  wire[1:0] \f$true  = \i0$data  ;
  wire[0:0] \f$false$bool$arg0$disj  = \sel  ;
  wire[0:0] \f$false$bool$arg0  = \f$false$bool$arg0$disj [0:0] ;
  wire[0:0] \f$false$bool$arg1  = 1'd1 ;
  wire \f$false$bool  = \f$false$bool$arg0  == \f$false$bool$arg1  ;
  wire[1:0] \f$false$true  = \i1$data  ;
  wire[1:0] \f$false$false  = \i0$data  ;
  wire[1:0] \f$false  = ( \f$false$bool  ? \f$false$true  : \f$false$false  ) ;
  wire[1:0] \f  = ( \f$bool  ? \f$true  : \f$false  ) ;
  
  assign \o0  = \f  ;
endmodule

module \OFUN_0$LigeroRouter_0_1_2_2_2_Merge2 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , input [1:0] \i1$data 
    , input \sel 
    , output [1:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[0:0] \f$bool$arg0$disj  = \sel  ;
  wire[0:0] \f$bool$arg0  = \f$bool$arg0$disj [0:0] ;
  wire[0:0] \f$bool$arg1  = 1'd0 ;
  wire \f$bool  = \f$bool$arg0  == \f$bool$arg1  ;
  wire[1:0] \f$true  = \i0$data  ;
  wire[0:0] \f$false$bool$arg0$disj  = \sel  ;
  wire[0:0] \f$false$bool$arg0  = \f$false$bool$arg0$disj [0:0] ;
  wire[0:0] \f$false$bool$arg1  = 1'd1 ;
  wire \f$false$bool  = \f$false$bool$arg0  == \f$false$bool$arg1  ;
  wire[1:0] \f$false$true  = \i1$data  ;
  wire[1:0] \f$false$false  = \i0$data  ;
  wire[1:0] \f$false  = ( \f$false$bool  ? \f$false$true  : \f$false$false  ) ;
  wire[1:0] \f  = ( \f$bool  ? \f$true  : \f$false  ) ;
  
  assign \o0  = \f  ;
endmodule

module \OFUN_0$LigeroRouter_0_1_2_2_2_Merge3 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , input [1:0] \i1$data 
    , input \sel 
    , output [1:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[0:0] \f$bool$arg0$disj  = \sel  ;
  wire[0:0] \f$bool$arg0  = \f$bool$arg0$disj [0:0] ;
  wire[0:0] \f$bool$arg1  = 1'd0 ;
  wire \f$bool  = \f$bool$arg0  == \f$bool$arg1  ;
  wire[1:0] \f$true  = \i0$data  ;
  wire[0:0] \f$false$bool$arg0$disj  = \sel  ;
  wire[0:0] \f$false$bool$arg0  = \f$false$bool$arg0$disj [0:0] ;
  wire[0:0] \f$false$bool$arg1  = 1'd1 ;
  wire \f$false$bool  = \f$false$bool$arg0  == \f$false$bool$arg1  ;
  wire[1:0] \f$false$true  = \i1$data  ;
  wire[1:0] \f$false$false  = \i0$data  ;
  wire[1:0] \f$false  = ( \f$false$bool  ? \f$false$true  : \f$false$false  ) ;
  wire[1:0] \f  = ( \f$bool  ? \f$true  : \f$false  ) ;
  
  assign \o0  = \f  ;
endmodule

module \LigeroRouter_1_1_2_2_2 (
      input \clk , input \rst , input [63:0] \t 
    , input \bus_ins1$irdy , input [1:0] \bus_ins1$data , output \bus_ins1$trdy 
    , input \bus_ins2$irdy , input [1:0] \bus_ins2$data , output \bus_ins2$trdy 
    , input \bus_ins3$irdy , input [1:0] \bus_ins3$data , output \bus_ins3$trdy 
    , input \bus_ins4$irdy , input [1:0] \bus_ins4$data , output \bus_ins4$trdy 
    , input \bus_ins5$irdy , input [1:0] \bus_ins5$data , output \bus_ins5$trdy 
    , input \bus_ins6$irdy , input [0:0] \bus_ins6$data , output \bus_ins6$trdy 
    , input \bus_ins7$irdy , input [0:0] \bus_ins7$data , output \bus_ins7$trdy 
    , input \bus_ins8$irdy , input [0:0] \bus_ins8$data , output \bus_ins8$trdy 
    , input \bus_ins9$irdy , input [0:0] \bus_ins9$data , output \bus_ins9$trdy 
    , output \bus_outs1$irdy , output [1:0] \bus_outs1$data , input \bus_outs1$trdy 
    , output \bus_outs2$irdy , output [1:0] \bus_outs2$data , input \bus_outs2$trdy 
    , output \bus_outs3$irdy , output [1:0] \bus_outs3$data , input \bus_outs3$trdy 
    , output \bus_outs4$irdy , output [1:0] \bus_outs4$data , input \bus_outs4$trdy 
    , output \bus_outs5$irdy , output [1:0] \bus_outs5$data , input \bus_outs5$trdy 
    , output \bus_outs6$irdy , output [0:0] \bus_outs6$data , input \bus_outs6$trdy 
    , output \bus_outs7$irdy , output [0:0] \bus_outs7$data , input \bus_outs7$trdy 
    , output \bus_outs8$irdy , output [0:0] \bus_outs8$data , input \bus_outs8$trdy 
    , output \bus_outs9$irdy , output [0:0] \bus_outs9$data , input \bus_outs9$trdy 
    , input \BBB1$Sink1$unbound_trdy 
    , output \BBB1$Sink1$irdy 
    , output [1:0] \BBB1$Sink1$data 
    , input \BBB1$RECEPTION1$CreditCounter1$PatientSource1$unbound_irdy 
    , input [0:0] \BBB1$RECEPTION1$CreditCounter1$PatientSource1$unbound_data 
    , output \BBB1$RECEPTION1$CreditCounter1$PatientSource1$trdy 
    , input \BBB1$RECEPTION1$CreditCounter1$Sink1$unbound_trdy 
    , output \BBB1$RECEPTION1$CreditCounter1$Sink1$irdy 
    , output [0:0] \BBB1$RECEPTION1$CreditCounter1$Sink1$data 
    , input \BBB2$Sink1$unbound_trdy 
    , output \BBB2$Sink1$irdy 
    , output [1:0] \BBB2$Sink1$data 
    , input \BBB2$RECEPTION1$CreditCounter1$PatientSource1$unbound_irdy 
    , input [0:0] \BBB2$RECEPTION1$CreditCounter1$PatientSource1$unbound_data 
    , output \BBB2$RECEPTION1$CreditCounter1$PatientSource1$trdy 
    , input \BBB2$RECEPTION1$CreditCounter1$Sink1$unbound_trdy 
    , output \BBB2$RECEPTION1$CreditCounter1$Sink1$irdy 
    , output [0:0] \BBB2$RECEPTION1$CreditCounter1$Sink1$data 
    , input \BBB3$Sink1$unbound_trdy 
    , output \BBB3$Sink1$irdy 
    , output [1:0] \BBB3$Sink1$data 
    , input \BBB3$RECEPTION1$CreditCounter1$PatientSource1$unbound_irdy 
    , input [0:0] \BBB3$RECEPTION1$CreditCounter1$PatientSource1$unbound_data 
    , output \BBB3$RECEPTION1$CreditCounter1$PatientSource1$trdy 
    , input \BBB3$RECEPTION1$CreditCounter1$Sink1$unbound_trdy 
    , output \BBB3$RECEPTION1$CreditCounter1$Sink1$irdy 
    , output [0:0] \BBB3$RECEPTION1$CreditCounter1$Sink1$data 
    , input \BBB4$Sink1$unbound_trdy 
    , output \BBB4$Sink1$irdy 
    , output [1:0] \BBB4$Sink1$data 
    , input \BBB4$RECEPTION1$CreditCounter1$PatientSource1$unbound_irdy 
    , input [0:0] \BBB4$RECEPTION1$CreditCounter1$PatientSource1$unbound_data 
    , output \BBB4$RECEPTION1$CreditCounter1$PatientSource1$trdy 
    , input \BBB4$RECEPTION1$CreditCounter1$Sink1$unbound_trdy 
    , output \BBB4$RECEPTION1$CreditCounter1$Sink1$irdy 
    , output [0:0] \BBB4$RECEPTION1$CreditCounter1$Sink1$data 
  );
  
  //
  // Channel declarations
  //
  wire \y_plus_loop$irdy  ;
  wire [1:0] \y_plus_loop$data  ;
  wire \y_plus_loop$trdy  ;
  wire \y_plus_cons$irdy  ;
  wire [1:0] \y_plus_cons$data  ;
  wire \y_plus_cons$trdy  ;
  wire \y_min_loop$irdy  ;
  wire [1:0] \y_min_loop$data  ;
  wire \y_min_loop$trdy  ;
  wire \y_min_cons$irdy  ;
  wire [1:0] \y_min_cons$data  ;
  wire \y_min_cons$trdy  ;
  wire \x_plus_loop$irdy  ;
  wire [1:0] \x_plus_loop$data  ;
  wire \x_plus_loop$trdy  ;
  wire \x_plus_cons$irdy  ;
  wire [1:0] \x_plus_cons$data  ;
  wire \x_plus_cons$trdy  ;
  wire \x_min_loop$irdy  ;
  wire [1:0] \x_min_loop$data  ;
  wire \x_min_loop$trdy  ;
  wire \x_min_cons$irdy  ;
  wire [1:0] \x_min_cons$data  ;
  wire \x_min_cons$trdy  ;
  wire \channel1$irdy  ;
  wire [1:0] \channel1$data  ;
  wire \channel1$trdy  ;
  wire \channel2$irdy  ;
  wire [1:0] \channel2$data  ;
  wire \channel2$trdy  ;
  wire \channel3$irdy  ;
  wire [1:0] \channel3$data  ;
  wire \channel3$trdy  ;
  wire \channel4$irdy  ;
  wire [1:0] \channel4$data  ;
  wire \channel4$trdy  ;
  wire \channel6$irdy  ;
  wire [1:0] \channel6$data  ;
  wire \channel6$trdy  ;
  wire \channel5$irdy  ;
  wire [1:0] \channel5$data  ;
  wire \channel5$trdy  ;
  wire \x_min_inj$irdy  ;
  wire [1:0] \x_min_inj$data  ;
  wire \x_min_inj$trdy  ;
  wire \x_plus_inj$irdy  ;
  wire [1:0] \x_plus_inj$data  ;
  wire \x_plus_inj$trdy  ;
  wire \y_min_inj$irdy  ;
  wire [1:0] \y_min_inj$data  ;
  wire \y_min_inj$trdy  ;
  wire \y_plus_inj$irdy  ;
  wire [1:0] \y_plus_inj$data  ;
  wire \y_plus_inj$trdy  ;
  wire \channel7$irdy  ;
  wire [1:0] \channel7$data  ;
  wire \channel7$trdy  ;
  
  //
  // Function Channels
  //
  wire [1:0] \ofunchan_0_Merge1$data  ;
  wire \sel_Merge1  ;
  wire [1:0] \ofunchan_0_Merge2$data  ;
  wire \sel_Merge2  ;
  wire [1:0] \ofunchan_0_Merge3$data  ;
  wire \sel_Merge3  ;
  
  //
  // Component and Macro instantiations
  //
  \Merge2  #(
    .INPUTSIZE1(2),
    .OUTPUTSIZE(2),
    .INPUTSIZE0(2)
  ) \Merge1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\x_min_cons$irdy )
    , .\i0$data (\x_min_cons$data )
    , .\i0$trdy (\x_min_cons$trdy )
    , .\i1$irdy (\channel6$irdy )
    , .\i1$data (\channel6$data )
    , .\i1$trdy (\channel6$trdy )
    , .\o0$irdy (\bus_outs1$irdy )
    , .\o0$data (\bus_outs1$data )
    , .\o0$trdy (\bus_outs1$trdy )
    , .\f$data (\ofunchan_0_Merge1$data )
    , .\sel (\sel_Merge1 )
  );
  
  \OFUN_0$LigeroRouter_1_1_2_2_2_Merge1  \ofun_0_Merge1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\x_min_cons$data )
    , .\i1$data (\channel6$data )
    , .\sel (\sel_Merge1 )
    , .\o0 (\ofunchan_0_Merge1$data )
  );
  
  \Merge2  #(
    .INPUTSIZE1(2),
    .OUTPUTSIZE(2),
    .INPUTSIZE0(2)
  ) \Merge2  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\x_plus_cons$irdy )
    , .\i0$data (\x_plus_cons$data )
    , .\i0$trdy (\x_plus_cons$trdy )
    , .\i1$irdy (\channel5$irdy )
    , .\i1$data (\channel5$data )
    , .\i1$trdy (\channel5$trdy )
    , .\o0$irdy (\channel6$irdy )
    , .\o0$data (\channel6$data )
    , .\o0$trdy (\channel6$trdy )
    , .\f$data (\ofunchan_0_Merge2$data )
    , .\sel (\sel_Merge2 )
  );
  
  \OFUN_0$LigeroRouter_1_1_2_2_2_Merge2  \ofun_0_Merge2  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\x_plus_cons$data )
    , .\i1$data (\channel5$data )
    , .\sel (\sel_Merge2 )
    , .\o0 (\ofunchan_0_Merge2$data )
  );
  
  \Merge2  #(
    .INPUTSIZE1(2),
    .OUTPUTSIZE(2),
    .INPUTSIZE0(2)
  ) \Merge3  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\y_min_cons$irdy )
    , .\i0$data (\y_min_cons$data )
    , .\i0$trdy (\y_min_cons$trdy )
    , .\i1$irdy (\y_plus_cons$irdy )
    , .\i1$data (\y_plus_cons$data )
    , .\i1$trdy (\y_plus_cons$trdy )
    , .\o0$irdy (\channel5$irdy )
    , .\o0$data (\channel5$data )
    , .\o0$trdy (\channel5$trdy )
    , .\f$data (\ofunchan_0_Merge3$data )
    , .\sel (\sel_Merge3 )
  );
  
  \OFUN_0$LigeroRouter_1_1_2_2_2_Merge3  \ofun_0_Merge3  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\y_min_cons$data )
    , .\i1$data (\y_plus_cons$data )
    , .\sel (\sel_Merge3 )
    , .\o0 (\ofunchan_0_Merge3$data )
  );
  
  \LoadBalancer4  #(
    .DATASIZE(2)
  ) \LoadBalancer1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\channel7$irdy )
    , .\i0$data (\channel7$data )
    , .\i0$trdy (\channel7$trdy )
    , .\o0$irdy (\x_min_inj$irdy )
    , .\o0$data (\x_min_inj$data )
    , .\o0$trdy (\x_min_inj$trdy )
    , .\o1$irdy (\x_plus_inj$irdy )
    , .\o1$data (\x_plus_inj$data )
    , .\o1$trdy (\x_plus_inj$trdy )
    , .\o2$irdy (\y_min_inj$irdy )
    , .\o2$data (\y_min_inj$data )
    , .\o2$trdy (\y_min_inj$trdy )
    , .\o3$irdy (\y_plus_inj$irdy )
    , .\o3$data (\y_plus_inj$data )
    , .\o3$trdy (\y_plus_inj$trdy )
  );
  
  \BBB_1_1_2_2_0_2  \BBB1  (
      .\clk (\clk ), .\rst (\rst ), .\t (\t )
    , .\bus_ins1$irdy (\channel1$irdy )
    , .\bus_ins1$data (\channel1$data )
    , .\bus_ins1$trdy (\channel1$trdy )
    , .\bus_ins2$irdy (\bus_ins2$irdy )
    , .\bus_ins2$data (\bus_ins2$data )
    , .\bus_ins2$trdy (\bus_ins2$trdy )
    , .\bus_ins3$irdy (\y_min_loop$irdy )
    , .\bus_ins3$data (\y_min_loop$data )
    , .\bus_ins3$trdy (\y_min_loop$trdy )
    , .\bus_ins4$irdy (\bus_ins6$irdy )
    , .\bus_ins4$data (\bus_ins6$data )
    , .\bus_ins4$trdy (\bus_ins6$trdy )
    , .\bus_outs1$irdy (\x_min_cons$irdy )
    , .\bus_outs1$data (\x_min_cons$data )
    , .\bus_outs1$trdy (\x_min_cons$trdy )
    , .\bus_outs2$irdy (\bus_outs2$irdy )
    , .\bus_outs2$data (\bus_outs2$data )
    , .\bus_outs2$trdy (\bus_outs2$trdy )
    , .\bus_outs3$irdy (\x_min_loop$irdy )
    , .\bus_outs3$data (\x_min_loop$data )
    , .\bus_outs3$trdy (\x_min_loop$trdy )
    , .\bus_outs4$irdy (\bus_outs6$irdy )
    , .\bus_outs4$data (\bus_outs6$data )
    , .\bus_outs4$trdy (\bus_outs6$trdy )
    , .\Sink1$unbound_trdy (\BBB1$Sink1$unbound_trdy )
    , .\Sink1$irdy (\BBB1$Sink1$irdy )
    , .\Sink1$data (\BBB1$Sink1$data )
    , .\RECEPTION1$CreditCounter1$PatientSource1$unbound_irdy (\BBB1$RECEPTION1$CreditCounter1$PatientSource1$unbound_irdy )
    , .\RECEPTION1$CreditCounter1$PatientSource1$unbound_data (\BBB1$RECEPTION1$CreditCounter1$PatientSource1$unbound_data )
    , .\RECEPTION1$CreditCounter1$PatientSource1$trdy (\BBB1$RECEPTION1$CreditCounter1$PatientSource1$trdy )
    , .\RECEPTION1$CreditCounter1$Sink1$unbound_trdy (\BBB1$RECEPTION1$CreditCounter1$Sink1$unbound_trdy )
    , .\RECEPTION1$CreditCounter1$Sink1$irdy (\BBB1$RECEPTION1$CreditCounter1$Sink1$irdy )
    , .\RECEPTION1$CreditCounter1$Sink1$data (\BBB1$RECEPTION1$CreditCounter1$Sink1$data )
  );
  
  \Latch$type4  \Latch1  (
      .\clk (\clk ), .\rst (\rst )
    , .\input$irdy (\x_min_inj$irdy )
    , .\input$data (\x_min_inj$data )
    , .\input$trdy (\x_min_inj$trdy )
    , .\output$irdy (\channel1$irdy )
    , .\output$data (\channel1$data )
    , .\output$trdy (\channel1$trdy )
  );
  
  \BBB_1_1_2_2_1_2  \BBB2  (
      .\clk (\clk ), .\rst (\rst ), .\t (\t )
    , .\bus_ins1$irdy (\channel2$irdy )
    , .\bus_ins1$data (\channel2$data )
    , .\bus_ins1$trdy (\channel2$trdy )
    , .\bus_ins2$irdy (\bus_ins3$irdy )
    , .\bus_ins2$data (\bus_ins3$data )
    , .\bus_ins2$trdy (\bus_ins3$trdy )
    , .\bus_ins3$irdy (\y_plus_loop$irdy )
    , .\bus_ins3$data (\y_plus_loop$data )
    , .\bus_ins3$trdy (\y_plus_loop$trdy )
    , .\bus_ins4$irdy (\bus_ins7$irdy )
    , .\bus_ins4$data (\bus_ins7$data )
    , .\bus_ins4$trdy (\bus_ins7$trdy )
    , .\bus_outs1$irdy (\x_plus_cons$irdy )
    , .\bus_outs1$data (\x_plus_cons$data )
    , .\bus_outs1$trdy (\x_plus_cons$trdy )
    , .\bus_outs2$irdy (\bus_outs3$irdy )
    , .\bus_outs2$data (\bus_outs3$data )
    , .\bus_outs2$trdy (\bus_outs3$trdy )
    , .\bus_outs3$irdy (\x_plus_loop$irdy )
    , .\bus_outs3$data (\x_plus_loop$data )
    , .\bus_outs3$trdy (\x_plus_loop$trdy )
    , .\bus_outs4$irdy (\bus_outs7$irdy )
    , .\bus_outs4$data (\bus_outs7$data )
    , .\bus_outs4$trdy (\bus_outs7$trdy )
    , .\Sink1$unbound_trdy (\BBB2$Sink1$unbound_trdy )
    , .\Sink1$irdy (\BBB2$Sink1$irdy )
    , .\Sink1$data (\BBB2$Sink1$data )
    , .\RECEPTION1$CreditCounter1$PatientSource1$unbound_irdy (\BBB2$RECEPTION1$CreditCounter1$PatientSource1$unbound_irdy )
    , .\RECEPTION1$CreditCounter1$PatientSource1$unbound_data (\BBB2$RECEPTION1$CreditCounter1$PatientSource1$unbound_data )
    , .\RECEPTION1$CreditCounter1$PatientSource1$trdy (\BBB2$RECEPTION1$CreditCounter1$PatientSource1$trdy )
    , .\RECEPTION1$CreditCounter1$Sink1$unbound_trdy (\BBB2$RECEPTION1$CreditCounter1$Sink1$unbound_trdy )
    , .\RECEPTION1$CreditCounter1$Sink1$irdy (\BBB2$RECEPTION1$CreditCounter1$Sink1$irdy )
    , .\RECEPTION1$CreditCounter1$Sink1$data (\BBB2$RECEPTION1$CreditCounter1$Sink1$data )
  );
  
  \Latch$type4  \Latch2  (
      .\clk (\clk ), .\rst (\rst )
    , .\input$irdy (\x_plus_inj$irdy )
    , .\input$data (\x_plus_inj$data )
    , .\input$trdy (\x_plus_inj$trdy )
    , .\output$irdy (\channel2$irdy )
    , .\output$data (\channel2$data )
    , .\output$trdy (\channel2$trdy )
  );
  
  \BBB_1_1_2_2_2_2  \BBB3  (
      .\clk (\clk ), .\rst (\rst ), .\t (\t )
    , .\bus_ins1$irdy (\channel3$irdy )
    , .\bus_ins1$data (\channel3$data )
    , .\bus_ins1$trdy (\channel3$trdy )
    , .\bus_ins2$irdy (\bus_ins4$irdy )
    , .\bus_ins2$data (\bus_ins4$data )
    , .\bus_ins2$trdy (\bus_ins4$trdy )
    , .\bus_ins3$irdy (\x_plus_loop$irdy )
    , .\bus_ins3$data (\x_plus_loop$data )
    , .\bus_ins3$trdy (\x_plus_loop$trdy )
    , .\bus_ins4$irdy (\bus_ins8$irdy )
    , .\bus_ins4$data (\bus_ins8$data )
    , .\bus_ins4$trdy (\bus_ins8$trdy )
    , .\bus_outs1$irdy (\y_min_cons$irdy )
    , .\bus_outs1$data (\y_min_cons$data )
    , .\bus_outs1$trdy (\y_min_cons$trdy )
    , .\bus_outs2$irdy (\bus_outs4$irdy )
    , .\bus_outs2$data (\bus_outs4$data )
    , .\bus_outs2$trdy (\bus_outs4$trdy )
    , .\bus_outs3$irdy (\y_min_loop$irdy )
    , .\bus_outs3$data (\y_min_loop$data )
    , .\bus_outs3$trdy (\y_min_loop$trdy )
    , .\bus_outs4$irdy (\bus_outs8$irdy )
    , .\bus_outs4$data (\bus_outs8$data )
    , .\bus_outs4$trdy (\bus_outs8$trdy )
    , .\Sink1$unbound_trdy (\BBB3$Sink1$unbound_trdy )
    , .\Sink1$irdy (\BBB3$Sink1$irdy )
    , .\Sink1$data (\BBB3$Sink1$data )
    , .\RECEPTION1$CreditCounter1$PatientSource1$unbound_irdy (\BBB3$RECEPTION1$CreditCounter1$PatientSource1$unbound_irdy )
    , .\RECEPTION1$CreditCounter1$PatientSource1$unbound_data (\BBB3$RECEPTION1$CreditCounter1$PatientSource1$unbound_data )
    , .\RECEPTION1$CreditCounter1$PatientSource1$trdy (\BBB3$RECEPTION1$CreditCounter1$PatientSource1$trdy )
    , .\RECEPTION1$CreditCounter1$Sink1$unbound_trdy (\BBB3$RECEPTION1$CreditCounter1$Sink1$unbound_trdy )
    , .\RECEPTION1$CreditCounter1$Sink1$irdy (\BBB3$RECEPTION1$CreditCounter1$Sink1$irdy )
    , .\RECEPTION1$CreditCounter1$Sink1$data (\BBB3$RECEPTION1$CreditCounter1$Sink1$data )
  );
  
  \Latch$type4  \Latch3  (
      .\clk (\clk ), .\rst (\rst )
    , .\input$irdy (\y_min_inj$irdy )
    , .\input$data (\y_min_inj$data )
    , .\input$trdy (\y_min_inj$trdy )
    , .\output$irdy (\channel3$irdy )
    , .\output$data (\channel3$data )
    , .\output$trdy (\channel3$trdy )
  );
  
  \BBB_1_1_2_2_3_2  \BBB4  (
      .\clk (\clk ), .\rst (\rst ), .\t (\t )
    , .\bus_ins1$irdy (\channel4$irdy )
    , .\bus_ins1$data (\channel4$data )
    , .\bus_ins1$trdy (\channel4$trdy )
    , .\bus_ins2$irdy (\bus_ins5$irdy )
    , .\bus_ins2$data (\bus_ins5$data )
    , .\bus_ins2$trdy (\bus_ins5$trdy )
    , .\bus_ins3$irdy (\x_min_loop$irdy )
    , .\bus_ins3$data (\x_min_loop$data )
    , .\bus_ins3$trdy (\x_min_loop$trdy )
    , .\bus_ins4$irdy (\bus_ins9$irdy )
    , .\bus_ins4$data (\bus_ins9$data )
    , .\bus_ins4$trdy (\bus_ins9$trdy )
    , .\bus_outs1$irdy (\y_plus_cons$irdy )
    , .\bus_outs1$data (\y_plus_cons$data )
    , .\bus_outs1$trdy (\y_plus_cons$trdy )
    , .\bus_outs2$irdy (\bus_outs5$irdy )
    , .\bus_outs2$data (\bus_outs5$data )
    , .\bus_outs2$trdy (\bus_outs5$trdy )
    , .\bus_outs3$irdy (\y_plus_loop$irdy )
    , .\bus_outs3$data (\y_plus_loop$data )
    , .\bus_outs3$trdy (\y_plus_loop$trdy )
    , .\bus_outs4$irdy (\bus_outs9$irdy )
    , .\bus_outs4$data (\bus_outs9$data )
    , .\bus_outs4$trdy (\bus_outs9$trdy )
    , .\Sink1$unbound_trdy (\BBB4$Sink1$unbound_trdy )
    , .\Sink1$irdy (\BBB4$Sink1$irdy )
    , .\Sink1$data (\BBB4$Sink1$data )
    , .\RECEPTION1$CreditCounter1$PatientSource1$unbound_irdy (\BBB4$RECEPTION1$CreditCounter1$PatientSource1$unbound_irdy )
    , .\RECEPTION1$CreditCounter1$PatientSource1$unbound_data (\BBB4$RECEPTION1$CreditCounter1$PatientSource1$unbound_data )
    , .\RECEPTION1$CreditCounter1$PatientSource1$trdy (\BBB4$RECEPTION1$CreditCounter1$PatientSource1$trdy )
    , .\RECEPTION1$CreditCounter1$Sink1$unbound_trdy (\BBB4$RECEPTION1$CreditCounter1$Sink1$unbound_trdy )
    , .\RECEPTION1$CreditCounter1$Sink1$irdy (\BBB4$RECEPTION1$CreditCounter1$Sink1$irdy )
    , .\RECEPTION1$CreditCounter1$Sink1$data (\BBB4$RECEPTION1$CreditCounter1$Sink1$data )
  );
  
  \Latch$type4  \Latch4  (
      .\clk (\clk ), .\rst (\rst )
    , .\input$irdy (\y_plus_inj$irdy )
    , .\input$data (\y_plus_inj$data )
    , .\input$trdy (\y_plus_inj$trdy )
    , .\output$irdy (\channel4$irdy )
    , .\output$data (\channel4$data )
    , .\output$trdy (\channel4$trdy )
  );
  
  \Latch$type4  \Latch5  (
      .\clk (\clk ), .\rst (\rst )
    , .\input$irdy (\bus_ins1$irdy )
    , .\input$data (\bus_ins1$data )
    , .\input$trdy (\bus_ins1$trdy )
    , .\output$irdy (\channel7$irdy )
    , .\output$data (\channel7$data )
    , .\output$trdy (\channel7$trdy )
  );
  
endmodule


//
// LigeroRouter_1_1_2_2_2 switch functions
//
module \OFUN_0$LigeroRouter_1_1_2_2_2_Merge1 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , input [1:0] \i1$data 
    , input \sel 
    , output [1:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[0:0] \f$bool$arg0$disj  = \sel  ;
  wire[0:0] \f$bool$arg0  = \f$bool$arg0$disj [0:0] ;
  wire[0:0] \f$bool$arg1  = 1'd0 ;
  wire \f$bool  = \f$bool$arg0  == \f$bool$arg1  ;
  wire[1:0] \f$true  = \i0$data  ;
  wire[0:0] \f$false$bool$arg0$disj  = \sel  ;
  wire[0:0] \f$false$bool$arg0  = \f$false$bool$arg0$disj [0:0] ;
  wire[0:0] \f$false$bool$arg1  = 1'd1 ;
  wire \f$false$bool  = \f$false$bool$arg0  == \f$false$bool$arg1  ;
  wire[1:0] \f$false$true  = \i1$data  ;
  wire[1:0] \f$false$false  = \i0$data  ;
  wire[1:0] \f$false  = ( \f$false$bool  ? \f$false$true  : \f$false$false  ) ;
  wire[1:0] \f  = ( \f$bool  ? \f$true  : \f$false  ) ;
  
  assign \o0  = \f  ;
endmodule

module \OFUN_0$LigeroRouter_1_1_2_2_2_Merge2 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , input [1:0] \i1$data 
    , input \sel 
    , output [1:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[0:0] \f$bool$arg0$disj  = \sel  ;
  wire[0:0] \f$bool$arg0  = \f$bool$arg0$disj [0:0] ;
  wire[0:0] \f$bool$arg1  = 1'd0 ;
  wire \f$bool  = \f$bool$arg0  == \f$bool$arg1  ;
  wire[1:0] \f$true  = \i0$data  ;
  wire[0:0] \f$false$bool$arg0$disj  = \sel  ;
  wire[0:0] \f$false$bool$arg0  = \f$false$bool$arg0$disj [0:0] ;
  wire[0:0] \f$false$bool$arg1  = 1'd1 ;
  wire \f$false$bool  = \f$false$bool$arg0  == \f$false$bool$arg1  ;
  wire[1:0] \f$false$true  = \i1$data  ;
  wire[1:0] \f$false$false  = \i0$data  ;
  wire[1:0] \f$false  = ( \f$false$bool  ? \f$false$true  : \f$false$false  ) ;
  wire[1:0] \f  = ( \f$bool  ? \f$true  : \f$false  ) ;
  
  assign \o0  = \f  ;
endmodule

module \OFUN_0$LigeroRouter_1_1_2_2_2_Merge3 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , input [1:0] \i1$data 
    , input \sel 
    , output [1:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[0:0] \f$bool$arg0$disj  = \sel  ;
  wire[0:0] \f$bool$arg0  = \f$bool$arg0$disj [0:0] ;
  wire[0:0] \f$bool$arg1  = 1'd0 ;
  wire \f$bool  = \f$bool$arg0  == \f$bool$arg1  ;
  wire[1:0] \f$true  = \i0$data  ;
  wire[0:0] \f$false$bool$arg0$disj  = \sel  ;
  wire[0:0] \f$false$bool$arg0  = \f$false$bool$arg0$disj [0:0] ;
  wire[0:0] \f$false$bool$arg1  = 1'd1 ;
  wire \f$false$bool  = \f$false$bool$arg0  == \f$false$bool$arg1  ;
  wire[1:0] \f$false$true  = \i1$data  ;
  wire[1:0] \f$false$false  = \i0$data  ;
  wire[1:0] \f$false  = ( \f$false$bool  ? \f$false$true  : \f$false$false  ) ;
  wire[1:0] \f  = ( \f$bool  ? \f$true  : \f$false  ) ;
  
  assign \o0  = \f  ;
endmodule

module \LigeroRouter_1_0_2_2_2 (
      input \clk , input \rst , input [63:0] \t 
    , input \bus_ins1$irdy , input [1:0] \bus_ins1$data , output \bus_ins1$trdy 
    , input \bus_ins2$irdy , input [1:0] \bus_ins2$data , output \bus_ins2$trdy 
    , input \bus_ins3$irdy , input [1:0] \bus_ins3$data , output \bus_ins3$trdy 
    , input \bus_ins4$irdy , input [1:0] \bus_ins4$data , output \bus_ins4$trdy 
    , input \bus_ins5$irdy , input [1:0] \bus_ins5$data , output \bus_ins5$trdy 
    , input \bus_ins6$irdy , input [0:0] \bus_ins6$data , output \bus_ins6$trdy 
    , input \bus_ins7$irdy , input [0:0] \bus_ins7$data , output \bus_ins7$trdy 
    , input \bus_ins8$irdy , input [0:0] \bus_ins8$data , output \bus_ins8$trdy 
    , input \bus_ins9$irdy , input [0:0] \bus_ins9$data , output \bus_ins9$trdy 
    , output \bus_outs1$irdy , output [1:0] \bus_outs1$data , input \bus_outs1$trdy 
    , output \bus_outs2$irdy , output [1:0] \bus_outs2$data , input \bus_outs2$trdy 
    , output \bus_outs3$irdy , output [1:0] \bus_outs3$data , input \bus_outs3$trdy 
    , output \bus_outs4$irdy , output [1:0] \bus_outs4$data , input \bus_outs4$trdy 
    , output \bus_outs5$irdy , output [1:0] \bus_outs5$data , input \bus_outs5$trdy 
    , output \bus_outs6$irdy , output [0:0] \bus_outs6$data , input \bus_outs6$trdy 
    , output \bus_outs7$irdy , output [0:0] \bus_outs7$data , input \bus_outs7$trdy 
    , output \bus_outs8$irdy , output [0:0] \bus_outs8$data , input \bus_outs8$trdy 
    , output \bus_outs9$irdy , output [0:0] \bus_outs9$data , input \bus_outs9$trdy 
    , input \BBB1$Sink1$unbound_trdy 
    , output \BBB1$Sink1$irdy 
    , output [1:0] \BBB1$Sink1$data 
    , input \BBB1$RECEPTION1$CreditCounter1$PatientSource1$unbound_irdy 
    , input [0:0] \BBB1$RECEPTION1$CreditCounter1$PatientSource1$unbound_data 
    , output \BBB1$RECEPTION1$CreditCounter1$PatientSource1$trdy 
    , input \BBB1$RECEPTION1$CreditCounter1$Sink1$unbound_trdy 
    , output \BBB1$RECEPTION1$CreditCounter1$Sink1$irdy 
    , output [0:0] \BBB1$RECEPTION1$CreditCounter1$Sink1$data 
    , input \BBB2$Sink1$unbound_trdy 
    , output \BBB2$Sink1$irdy 
    , output [1:0] \BBB2$Sink1$data 
    , input \BBB2$RECEPTION1$CreditCounter1$PatientSource1$unbound_irdy 
    , input [0:0] \BBB2$RECEPTION1$CreditCounter1$PatientSource1$unbound_data 
    , output \BBB2$RECEPTION1$CreditCounter1$PatientSource1$trdy 
    , input \BBB2$RECEPTION1$CreditCounter1$Sink1$unbound_trdy 
    , output \BBB2$RECEPTION1$CreditCounter1$Sink1$irdy 
    , output [0:0] \BBB2$RECEPTION1$CreditCounter1$Sink1$data 
    , input \BBB3$Sink1$unbound_trdy 
    , output \BBB3$Sink1$irdy 
    , output [1:0] \BBB3$Sink1$data 
    , input \BBB3$RECEPTION1$CreditCounter1$PatientSource1$unbound_irdy 
    , input [0:0] \BBB3$RECEPTION1$CreditCounter1$PatientSource1$unbound_data 
    , output \BBB3$RECEPTION1$CreditCounter1$PatientSource1$trdy 
    , input \BBB3$RECEPTION1$CreditCounter1$Sink1$unbound_trdy 
    , output \BBB3$RECEPTION1$CreditCounter1$Sink1$irdy 
    , output [0:0] \BBB3$RECEPTION1$CreditCounter1$Sink1$data 
    , input \BBB4$Sink1$unbound_trdy 
    , output \BBB4$Sink1$irdy 
    , output [1:0] \BBB4$Sink1$data 
    , input \BBB4$RECEPTION1$CreditCounter1$PatientSource1$unbound_irdy 
    , input [0:0] \BBB4$RECEPTION1$CreditCounter1$PatientSource1$unbound_data 
    , output \BBB4$RECEPTION1$CreditCounter1$PatientSource1$trdy 
    , input \BBB4$RECEPTION1$CreditCounter1$Sink1$unbound_trdy 
    , output \BBB4$RECEPTION1$CreditCounter1$Sink1$irdy 
    , output [0:0] \BBB4$RECEPTION1$CreditCounter1$Sink1$data 
  );
  
  //
  // Channel declarations
  //
  wire \y_plus_loop$irdy  ;
  wire [1:0] \y_plus_loop$data  ;
  wire \y_plus_loop$trdy  ;
  wire \y_plus_cons$irdy  ;
  wire [1:0] \y_plus_cons$data  ;
  wire \y_plus_cons$trdy  ;
  wire \y_min_loop$irdy  ;
  wire [1:0] \y_min_loop$data  ;
  wire \y_min_loop$trdy  ;
  wire \y_min_cons$irdy  ;
  wire [1:0] \y_min_cons$data  ;
  wire \y_min_cons$trdy  ;
  wire \x_plus_loop$irdy  ;
  wire [1:0] \x_plus_loop$data  ;
  wire \x_plus_loop$trdy  ;
  wire \x_plus_cons$irdy  ;
  wire [1:0] \x_plus_cons$data  ;
  wire \x_plus_cons$trdy  ;
  wire \x_min_loop$irdy  ;
  wire [1:0] \x_min_loop$data  ;
  wire \x_min_loop$trdy  ;
  wire \x_min_cons$irdy  ;
  wire [1:0] \x_min_cons$data  ;
  wire \x_min_cons$trdy  ;
  wire \channel1$irdy  ;
  wire [1:0] \channel1$data  ;
  wire \channel1$trdy  ;
  wire \channel2$irdy  ;
  wire [1:0] \channel2$data  ;
  wire \channel2$trdy  ;
  wire \channel3$irdy  ;
  wire [1:0] \channel3$data  ;
  wire \channel3$trdy  ;
  wire \channel4$irdy  ;
  wire [1:0] \channel4$data  ;
  wire \channel4$trdy  ;
  wire \channel6$irdy  ;
  wire [1:0] \channel6$data  ;
  wire \channel6$trdy  ;
  wire \channel5$irdy  ;
  wire [1:0] \channel5$data  ;
  wire \channel5$trdy  ;
  wire \x_min_inj$irdy  ;
  wire [1:0] \x_min_inj$data  ;
  wire \x_min_inj$trdy  ;
  wire \x_plus_inj$irdy  ;
  wire [1:0] \x_plus_inj$data  ;
  wire \x_plus_inj$trdy  ;
  wire \y_min_inj$irdy  ;
  wire [1:0] \y_min_inj$data  ;
  wire \y_min_inj$trdy  ;
  wire \y_plus_inj$irdy  ;
  wire [1:0] \y_plus_inj$data  ;
  wire \y_plus_inj$trdy  ;
  wire \channel7$irdy  ;
  wire [1:0] \channel7$data  ;
  wire \channel7$trdy  ;
  
  //
  // Function Channels
  //
  wire [1:0] \ofunchan_0_Merge1$data  ;
  wire \sel_Merge1  ;
  wire [1:0] \ofunchan_0_Merge2$data  ;
  wire \sel_Merge2  ;
  wire [1:0] \ofunchan_0_Merge3$data  ;
  wire \sel_Merge3  ;
  
  //
  // Component and Macro instantiations
  //
  \Merge2  #(
    .INPUTSIZE1(2),
    .OUTPUTSIZE(2),
    .INPUTSIZE0(2)
  ) \Merge1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\x_min_cons$irdy )
    , .\i0$data (\x_min_cons$data )
    , .\i0$trdy (\x_min_cons$trdy )
    , .\i1$irdy (\channel6$irdy )
    , .\i1$data (\channel6$data )
    , .\i1$trdy (\channel6$trdy )
    , .\o0$irdy (\bus_outs1$irdy )
    , .\o0$data (\bus_outs1$data )
    , .\o0$trdy (\bus_outs1$trdy )
    , .\f$data (\ofunchan_0_Merge1$data )
    , .\sel (\sel_Merge1 )
  );
  
  \OFUN_0$LigeroRouter_1_0_2_2_2_Merge1  \ofun_0_Merge1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\x_min_cons$data )
    , .\i1$data (\channel6$data )
    , .\sel (\sel_Merge1 )
    , .\o0 (\ofunchan_0_Merge1$data )
  );
  
  \Merge2  #(
    .INPUTSIZE1(2),
    .OUTPUTSIZE(2),
    .INPUTSIZE0(2)
  ) \Merge2  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\x_plus_cons$irdy )
    , .\i0$data (\x_plus_cons$data )
    , .\i0$trdy (\x_plus_cons$trdy )
    , .\i1$irdy (\channel5$irdy )
    , .\i1$data (\channel5$data )
    , .\i1$trdy (\channel5$trdy )
    , .\o0$irdy (\channel6$irdy )
    , .\o0$data (\channel6$data )
    , .\o0$trdy (\channel6$trdy )
    , .\f$data (\ofunchan_0_Merge2$data )
    , .\sel (\sel_Merge2 )
  );
  
  \OFUN_0$LigeroRouter_1_0_2_2_2_Merge2  \ofun_0_Merge2  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\x_plus_cons$data )
    , .\i1$data (\channel5$data )
    , .\sel (\sel_Merge2 )
    , .\o0 (\ofunchan_0_Merge2$data )
  );
  
  \Merge2  #(
    .INPUTSIZE1(2),
    .OUTPUTSIZE(2),
    .INPUTSIZE0(2)
  ) \Merge3  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\y_min_cons$irdy )
    , .\i0$data (\y_min_cons$data )
    , .\i0$trdy (\y_min_cons$trdy )
    , .\i1$irdy (\y_plus_cons$irdy )
    , .\i1$data (\y_plus_cons$data )
    , .\i1$trdy (\y_plus_cons$trdy )
    , .\o0$irdy (\channel5$irdy )
    , .\o0$data (\channel5$data )
    , .\o0$trdy (\channel5$trdy )
    , .\f$data (\ofunchan_0_Merge3$data )
    , .\sel (\sel_Merge3 )
  );
  
  \OFUN_0$LigeroRouter_1_0_2_2_2_Merge3  \ofun_0_Merge3  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$data (\y_min_cons$data )
    , .\i1$data (\y_plus_cons$data )
    , .\sel (\sel_Merge3 )
    , .\o0 (\ofunchan_0_Merge3$data )
  );
  
  \LoadBalancer4  #(
    .DATASIZE(2)
  ) \LoadBalancer1  (
      .\clk (\clk ), .\rst (\rst )
    , .\i0$irdy (\channel7$irdy )
    , .\i0$data (\channel7$data )
    , .\i0$trdy (\channel7$trdy )
    , .\o0$irdy (\x_min_inj$irdy )
    , .\o0$data (\x_min_inj$data )
    , .\o0$trdy (\x_min_inj$trdy )
    , .\o1$irdy (\x_plus_inj$irdy )
    , .\o1$data (\x_plus_inj$data )
    , .\o1$trdy (\x_plus_inj$trdy )
    , .\o2$irdy (\y_min_inj$irdy )
    , .\o2$data (\y_min_inj$data )
    , .\o2$trdy (\y_min_inj$trdy )
    , .\o3$irdy (\y_plus_inj$irdy )
    , .\o3$data (\y_plus_inj$data )
    , .\o3$trdy (\y_plus_inj$trdy )
  );
  
  \BBB_1_0_2_2_0_2  \BBB1  (
      .\clk (\clk ), .\rst (\rst ), .\t (\t )
    , .\bus_ins1$irdy (\channel1$irdy )
    , .\bus_ins1$data (\channel1$data )
    , .\bus_ins1$trdy (\channel1$trdy )
    , .\bus_ins2$irdy (\bus_ins2$irdy )
    , .\bus_ins2$data (\bus_ins2$data )
    , .\bus_ins2$trdy (\bus_ins2$trdy )
    , .\bus_ins3$irdy (\y_min_loop$irdy )
    , .\bus_ins3$data (\y_min_loop$data )
    , .\bus_ins3$trdy (\y_min_loop$trdy )
    , .\bus_ins4$irdy (\bus_ins6$irdy )
    , .\bus_ins4$data (\bus_ins6$data )
    , .\bus_ins4$trdy (\bus_ins6$trdy )
    , .\bus_outs1$irdy (\x_min_cons$irdy )
    , .\bus_outs1$data (\x_min_cons$data )
    , .\bus_outs1$trdy (\x_min_cons$trdy )
    , .\bus_outs2$irdy (\bus_outs2$irdy )
    , .\bus_outs2$data (\bus_outs2$data )
    , .\bus_outs2$trdy (\bus_outs2$trdy )
    , .\bus_outs3$irdy (\x_min_loop$irdy )
    , .\bus_outs3$data (\x_min_loop$data )
    , .\bus_outs3$trdy (\x_min_loop$trdy )
    , .\bus_outs4$irdy (\bus_outs6$irdy )
    , .\bus_outs4$data (\bus_outs6$data )
    , .\bus_outs4$trdy (\bus_outs6$trdy )
    , .\Sink1$unbound_trdy (\BBB1$Sink1$unbound_trdy )
    , .\Sink1$irdy (\BBB1$Sink1$irdy )
    , .\Sink1$data (\BBB1$Sink1$data )
    , .\RECEPTION1$CreditCounter1$PatientSource1$unbound_irdy (\BBB1$RECEPTION1$CreditCounter1$PatientSource1$unbound_irdy )
    , .\RECEPTION1$CreditCounter1$PatientSource1$unbound_data (\BBB1$RECEPTION1$CreditCounter1$PatientSource1$unbound_data )
    , .\RECEPTION1$CreditCounter1$PatientSource1$trdy (\BBB1$RECEPTION1$CreditCounter1$PatientSource1$trdy )
    , .\RECEPTION1$CreditCounter1$Sink1$unbound_trdy (\BBB1$RECEPTION1$CreditCounter1$Sink1$unbound_trdy )
    , .\RECEPTION1$CreditCounter1$Sink1$irdy (\BBB1$RECEPTION1$CreditCounter1$Sink1$irdy )
    , .\RECEPTION1$CreditCounter1$Sink1$data (\BBB1$RECEPTION1$CreditCounter1$Sink1$data )
  );
  
  \Latch$type4  \Latch1  (
      .\clk (\clk ), .\rst (\rst )
    , .\input$irdy (\x_min_inj$irdy )
    , .\input$data (\x_min_inj$data )
    , .\input$trdy (\x_min_inj$trdy )
    , .\output$irdy (\channel1$irdy )
    , .\output$data (\channel1$data )
    , .\output$trdy (\channel1$trdy )
  );
  
  \BBB_1_0_2_2_1_2  \BBB2  (
      .\clk (\clk ), .\rst (\rst ), .\t (\t )
    , .\bus_ins1$irdy (\channel2$irdy )
    , .\bus_ins1$data (\channel2$data )
    , .\bus_ins1$trdy (\channel2$trdy )
    , .\bus_ins2$irdy (\bus_ins3$irdy )
    , .\bus_ins2$data (\bus_ins3$data )
    , .\bus_ins2$trdy (\bus_ins3$trdy )
    , .\bus_ins3$irdy (\y_plus_loop$irdy )
    , .\bus_ins3$data (\y_plus_loop$data )
    , .\bus_ins3$trdy (\y_plus_loop$trdy )
    , .\bus_ins4$irdy (\bus_ins7$irdy )
    , .\bus_ins4$data (\bus_ins7$data )
    , .\bus_ins4$trdy (\bus_ins7$trdy )
    , .\bus_outs1$irdy (\x_plus_cons$irdy )
    , .\bus_outs1$data (\x_plus_cons$data )
    , .\bus_outs1$trdy (\x_plus_cons$trdy )
    , .\bus_outs2$irdy (\bus_outs3$irdy )
    , .\bus_outs2$data (\bus_outs3$data )
    , .\bus_outs2$trdy (\bus_outs3$trdy )
    , .\bus_outs3$irdy (\x_plus_loop$irdy )
    , .\bus_outs3$data (\x_plus_loop$data )
    , .\bus_outs3$trdy (\x_plus_loop$trdy )
    , .\bus_outs4$irdy (\bus_outs7$irdy )
    , .\bus_outs4$data (\bus_outs7$data )
    , .\bus_outs4$trdy (\bus_outs7$trdy )
    , .\Sink1$unbound_trdy (\BBB2$Sink1$unbound_trdy )
    , .\Sink1$irdy (\BBB2$Sink1$irdy )
    , .\Sink1$data (\BBB2$Sink1$data )
    , .\RECEPTION1$CreditCounter1$PatientSource1$unbound_irdy (\BBB2$RECEPTION1$CreditCounter1$PatientSource1$unbound_irdy )
    , .\RECEPTION1$CreditCounter1$PatientSource1$unbound_data (\BBB2$RECEPTION1$CreditCounter1$PatientSource1$unbound_data )
    , .\RECEPTION1$CreditCounter1$PatientSource1$trdy (\BBB2$RECEPTION1$CreditCounter1$PatientSource1$trdy )
    , .\RECEPTION1$CreditCounter1$Sink1$unbound_trdy (\BBB2$RECEPTION1$CreditCounter1$Sink1$unbound_trdy )
    , .\RECEPTION1$CreditCounter1$Sink1$irdy (\BBB2$RECEPTION1$CreditCounter1$Sink1$irdy )
    , .\RECEPTION1$CreditCounter1$Sink1$data (\BBB2$RECEPTION1$CreditCounter1$Sink1$data )
  );
  
  \Latch$type4  \Latch2  (
      .\clk (\clk ), .\rst (\rst )
    , .\input$irdy (\x_plus_inj$irdy )
    , .\input$data (\x_plus_inj$data )
    , .\input$trdy (\x_plus_inj$trdy )
    , .\output$irdy (\channel2$irdy )
    , .\output$data (\channel2$data )
    , .\output$trdy (\channel2$trdy )
  );
  
  \BBB_1_0_2_2_2_2  \BBB3  (
      .\clk (\clk ), .\rst (\rst ), .\t (\t )
    , .\bus_ins1$irdy (\channel3$irdy )
    , .\bus_ins1$data (\channel3$data )
    , .\bus_ins1$trdy (\channel3$trdy )
    , .\bus_ins2$irdy (\bus_ins4$irdy )
    , .\bus_ins2$data (\bus_ins4$data )
    , .\bus_ins2$trdy (\bus_ins4$trdy )
    , .\bus_ins3$irdy (\x_plus_loop$irdy )
    , .\bus_ins3$data (\x_plus_loop$data )
    , .\bus_ins3$trdy (\x_plus_loop$trdy )
    , .\bus_ins4$irdy (\bus_ins8$irdy )
    , .\bus_ins4$data (\bus_ins8$data )
    , .\bus_ins4$trdy (\bus_ins8$trdy )
    , .\bus_outs1$irdy (\y_min_cons$irdy )
    , .\bus_outs1$data (\y_min_cons$data )
    , .\bus_outs1$trdy (\y_min_cons$trdy )
    , .\bus_outs2$irdy (\bus_outs4$irdy )
    , .\bus_outs2$data (\bus_outs4$data )
    , .\bus_outs2$trdy (\bus_outs4$trdy )
    , .\bus_outs3$irdy (\y_min_loop$irdy )
    , .\bus_outs3$data (\y_min_loop$data )
    , .\bus_outs3$trdy (\y_min_loop$trdy )
    , .\bus_outs4$irdy (\bus_outs8$irdy )
    , .\bus_outs4$data (\bus_outs8$data )
    , .\bus_outs4$trdy (\bus_outs8$trdy )
    , .\Sink1$unbound_trdy (\BBB3$Sink1$unbound_trdy )
    , .\Sink1$irdy (\BBB3$Sink1$irdy )
    , .\Sink1$data (\BBB3$Sink1$data )
    , .\RECEPTION1$CreditCounter1$PatientSource1$unbound_irdy (\BBB3$RECEPTION1$CreditCounter1$PatientSource1$unbound_irdy )
    , .\RECEPTION1$CreditCounter1$PatientSource1$unbound_data (\BBB3$RECEPTION1$CreditCounter1$PatientSource1$unbound_data )
    , .\RECEPTION1$CreditCounter1$PatientSource1$trdy (\BBB3$RECEPTION1$CreditCounter1$PatientSource1$trdy )
    , .\RECEPTION1$CreditCounter1$Sink1$unbound_trdy (\BBB3$RECEPTION1$CreditCounter1$Sink1$unbound_trdy )
    , .\RECEPTION1$CreditCounter1$Sink1$irdy (\BBB3$RECEPTION1$CreditCounter1$Sink1$irdy )
    , .\RECEPTION1$CreditCounter1$Sink1$data (\BBB3$RECEPTION1$CreditCounter1$Sink1$data )
  );
  
  \Latch$type4  \Latch3  (
      .\clk (\clk ), .\rst (\rst )
    , .\input$irdy (\y_min_inj$irdy )
    , .\input$data (\y_min_inj$data )
    , .\input$trdy (\y_min_inj$trdy )
    , .\output$irdy (\channel3$irdy )
    , .\output$data (\channel3$data )
    , .\output$trdy (\channel3$trdy )
  );
  
  \BBB_1_0_2_2_3_2  \BBB4  (
      .\clk (\clk ), .\rst (\rst ), .\t (\t )
    , .\bus_ins1$irdy (\channel4$irdy )
    , .\bus_ins1$data (\channel4$data )
    , .\bus_ins1$trdy (\channel4$trdy )
    , .\bus_ins2$irdy (\bus_ins5$irdy )
    , .\bus_ins2$data (\bus_ins5$data )
    , .\bus_ins2$trdy (\bus_ins5$trdy )
    , .\bus_ins3$irdy (\x_min_loop$irdy )
    , .\bus_ins3$data (\x_min_loop$data )
    , .\bus_ins3$trdy (\x_min_loop$trdy )
    , .\bus_ins4$irdy (\bus_ins9$irdy )
    , .\bus_ins4$data (\bus_ins9$data )
    , .\bus_ins4$trdy (\bus_ins9$trdy )
    , .\bus_outs1$irdy (\y_plus_cons$irdy )
    , .\bus_outs1$data (\y_plus_cons$data )
    , .\bus_outs1$trdy (\y_plus_cons$trdy )
    , .\bus_outs2$irdy (\bus_outs5$irdy )
    , .\bus_outs2$data (\bus_outs5$data )
    , .\bus_outs2$trdy (\bus_outs5$trdy )
    , .\bus_outs3$irdy (\y_plus_loop$irdy )
    , .\bus_outs3$data (\y_plus_loop$data )
    , .\bus_outs3$trdy (\y_plus_loop$trdy )
    , .\bus_outs4$irdy (\bus_outs9$irdy )
    , .\bus_outs4$data (\bus_outs9$data )
    , .\bus_outs4$trdy (\bus_outs9$trdy )
    , .\Sink1$unbound_trdy (\BBB4$Sink1$unbound_trdy )
    , .\Sink1$irdy (\BBB4$Sink1$irdy )
    , .\Sink1$data (\BBB4$Sink1$data )
    , .\RECEPTION1$CreditCounter1$PatientSource1$unbound_irdy (\BBB4$RECEPTION1$CreditCounter1$PatientSource1$unbound_irdy )
    , .\RECEPTION1$CreditCounter1$PatientSource1$unbound_data (\BBB4$RECEPTION1$CreditCounter1$PatientSource1$unbound_data )
    , .\RECEPTION1$CreditCounter1$PatientSource1$trdy (\BBB4$RECEPTION1$CreditCounter1$PatientSource1$trdy )
    , .\RECEPTION1$CreditCounter1$Sink1$unbound_trdy (\BBB4$RECEPTION1$CreditCounter1$Sink1$unbound_trdy )
    , .\RECEPTION1$CreditCounter1$Sink1$irdy (\BBB4$RECEPTION1$CreditCounter1$Sink1$irdy )
    , .\RECEPTION1$CreditCounter1$Sink1$data (\BBB4$RECEPTION1$CreditCounter1$Sink1$data )
  );
  
  \Latch$type4  \Latch4  (
      .\clk (\clk ), .\rst (\rst )
    , .\input$irdy (\y_plus_inj$irdy )
    , .\input$data (\y_plus_inj$data )
    , .\input$trdy (\y_plus_inj$trdy )
    , .\output$irdy (\channel4$irdy )
    , .\output$data (\channel4$data )
    , .\output$trdy (\channel4$trdy )
  );
  
  \Latch$type4  \Latch5  (
      .\clk (\clk ), .\rst (\rst )
    , .\input$irdy (\bus_ins1$irdy )
    , .\input$data (\bus_ins1$data )
    , .\input$trdy (\bus_ins1$trdy )
    , .\output$irdy (\channel7$irdy )
    , .\output$data (\channel7$data )
    , .\output$trdy (\channel7$trdy )
  );
  
endmodule


//
// LigeroRouter_1_0_2_2_2 switch functions
//
module \OFUN_0$LigeroRouter_1_0_2_2_2_Merge1 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , input [1:0] \i1$data 
    , input \sel 
    , output [1:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[0:0] \f$bool$arg0$disj  = \sel  ;
  wire[0:0] \f$bool$arg0  = \f$bool$arg0$disj [0:0] ;
  wire[0:0] \f$bool$arg1  = 1'd0 ;
  wire \f$bool  = \f$bool$arg0  == \f$bool$arg1  ;
  wire[1:0] \f$true  = \i0$data  ;
  wire[0:0] \f$false$bool$arg0$disj  = \sel  ;
  wire[0:0] \f$false$bool$arg0  = \f$false$bool$arg0$disj [0:0] ;
  wire[0:0] \f$false$bool$arg1  = 1'd1 ;
  wire \f$false$bool  = \f$false$bool$arg0  == \f$false$bool$arg1  ;
  wire[1:0] \f$false$true  = \i1$data  ;
  wire[1:0] \f$false$false  = \i0$data  ;
  wire[1:0] \f$false  = ( \f$false$bool  ? \f$false$true  : \f$false$false  ) ;
  wire[1:0] \f  = ( \f$bool  ? \f$true  : \f$false  ) ;
  
  assign \o0  = \f  ;
endmodule

module \OFUN_0$LigeroRouter_1_0_2_2_2_Merge2 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , input [1:0] \i1$data 
    , input \sel 
    , output [1:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[0:0] \f$bool$arg0$disj  = \sel  ;
  wire[0:0] \f$bool$arg0  = \f$bool$arg0$disj [0:0] ;
  wire[0:0] \f$bool$arg1  = 1'd0 ;
  wire \f$bool  = \f$bool$arg0  == \f$bool$arg1  ;
  wire[1:0] \f$true  = \i0$data  ;
  wire[0:0] \f$false$bool$arg0$disj  = \sel  ;
  wire[0:0] \f$false$bool$arg0  = \f$false$bool$arg0$disj [0:0] ;
  wire[0:0] \f$false$bool$arg1  = 1'd1 ;
  wire \f$false$bool  = \f$false$bool$arg0  == \f$false$bool$arg1  ;
  wire[1:0] \f$false$true  = \i1$data  ;
  wire[1:0] \f$false$false  = \i0$data  ;
  wire[1:0] \f$false  = ( \f$false$bool  ? \f$false$true  : \f$false$false  ) ;
  wire[1:0] \f  = ( \f$bool  ? \f$true  : \f$false  ) ;
  
  assign \o0  = \f  ;
endmodule

module \OFUN_0$LigeroRouter_1_0_2_2_2_Merge3 (
      input \clk , input \rst 
    , input [1:0] \i0$data 
    , input [1:0] \i1$data 
    , input \sel 
    , output [1:0] \o0 
  );
  
  //
  // Function logic
  //
  wire[0:0] \f$bool$arg0$disj  = \sel  ;
  wire[0:0] \f$bool$arg0  = \f$bool$arg0$disj [0:0] ;
  wire[0:0] \f$bool$arg1  = 1'd0 ;
  wire \f$bool  = \f$bool$arg0  == \f$bool$arg1  ;
  wire[1:0] \f$true  = \i0$data  ;
  wire[0:0] \f$false$bool$arg0$disj  = \sel  ;
  wire[0:0] \f$false$bool$arg0  = \f$false$bool$arg0$disj [0:0] ;
  wire[0:0] \f$false$bool$arg1  = 1'd1 ;
  wire \f$false$bool  = \f$false$bool$arg0  == \f$false$bool$arg1  ;
  wire[1:0] \f$false$true  = \i1$data  ;
  wire[1:0] \f$false$false  = \i0$data  ;
  wire[1:0] \f$false  = ( \f$false$bool  ? \f$false$true  : \f$false$false  ) ;
  wire[1:0] \f  = ( \f$bool  ? \f$true  : \f$false  ) ;
  
  assign \o0  = \f  ;
endmodule


//
// Top level module
//
module \top (
      input \clk , input \rst , input [63:0] \t 
    , input \Source1$unbound_irdy 
    , input [1:0] \Source1$unbound_data 
    , output \Source1$trdy 
    , input \Source2$unbound_irdy 
    , input [1:0] \Source2$unbound_data 
    , output \Source2$trdy 
    , input \Source3$unbound_irdy 
    , input [1:0] \Source3$unbound_data 
    , output \Source3$trdy 
    , input \Source4$unbound_irdy 
    , input [1:0] \Source4$unbound_data 
    , output \Source4$trdy 
    , input \LigeroRouter1$BBB1$Sink1$unbound_trdy 
    , output \LigeroRouter1$BBB1$Sink1$irdy 
    , output [1:0] \LigeroRouter1$BBB1$Sink1$data 
    , input \LigeroRouter1$BBB1$RECEPTION1$CreditCounter1$PatientSource1$unbound_irdy 
    , input [0:0] \LigeroRouter1$BBB1$RECEPTION1$CreditCounter1$PatientSource1$unbound_data 
    , output \LigeroRouter1$BBB1$RECEPTION1$CreditCounter1$PatientSource1$trdy 
    , input \LigeroRouter1$BBB1$RECEPTION1$CreditCounter1$Sink1$unbound_trdy 
    , output \LigeroRouter1$BBB1$RECEPTION1$CreditCounter1$Sink1$irdy 
    , output [0:0] \LigeroRouter1$BBB1$RECEPTION1$CreditCounter1$Sink1$data 
    , input \LigeroRouter1$BBB2$Sink1$unbound_trdy 
    , output \LigeroRouter1$BBB2$Sink1$irdy 
    , output [1:0] \LigeroRouter1$BBB2$Sink1$data 
    , input \LigeroRouter1$BBB2$RECEPTION1$CreditCounter1$PatientSource1$unbound_irdy 
    , input [0:0] \LigeroRouter1$BBB2$RECEPTION1$CreditCounter1$PatientSource1$unbound_data 
    , output \LigeroRouter1$BBB2$RECEPTION1$CreditCounter1$PatientSource1$trdy 
    , input \LigeroRouter1$BBB2$RECEPTION1$CreditCounter1$Sink1$unbound_trdy 
    , output \LigeroRouter1$BBB2$RECEPTION1$CreditCounter1$Sink1$irdy 
    , output [0:0] \LigeroRouter1$BBB2$RECEPTION1$CreditCounter1$Sink1$data 
    , input \LigeroRouter1$BBB3$Sink1$unbound_trdy 
    , output \LigeroRouter1$BBB3$Sink1$irdy 
    , output [1:0] \LigeroRouter1$BBB3$Sink1$data 
    , input \LigeroRouter1$BBB3$RECEPTION1$CreditCounter1$PatientSource1$unbound_irdy 
    , input [0:0] \LigeroRouter1$BBB3$RECEPTION1$CreditCounter1$PatientSource1$unbound_data 
    , output \LigeroRouter1$BBB3$RECEPTION1$CreditCounter1$PatientSource1$trdy 
    , input \LigeroRouter1$BBB3$RECEPTION1$CreditCounter1$Sink1$unbound_trdy 
    , output \LigeroRouter1$BBB3$RECEPTION1$CreditCounter1$Sink1$irdy 
    , output [0:0] \LigeroRouter1$BBB3$RECEPTION1$CreditCounter1$Sink1$data 
    , input \LigeroRouter1$BBB4$Sink1$unbound_trdy 
    , output \LigeroRouter1$BBB4$Sink1$irdy 
    , output [1:0] \LigeroRouter1$BBB4$Sink1$data 
    , input \LigeroRouter1$BBB4$RECEPTION1$CreditCounter1$PatientSource1$unbound_irdy 
    , input [0:0] \LigeroRouter1$BBB4$RECEPTION1$CreditCounter1$PatientSource1$unbound_data 
    , output \LigeroRouter1$BBB4$RECEPTION1$CreditCounter1$PatientSource1$trdy 
    , input \LigeroRouter1$BBB4$RECEPTION1$CreditCounter1$Sink1$unbound_trdy 
    , output \LigeroRouter1$BBB4$RECEPTION1$CreditCounter1$Sink1$irdy 
    , output [0:0] \LigeroRouter1$BBB4$RECEPTION1$CreditCounter1$Sink1$data 
    , input \LigeroRouter2$BBB1$Sink1$unbound_trdy 
    , output \LigeroRouter2$BBB1$Sink1$irdy 
    , output [1:0] \LigeroRouter2$BBB1$Sink1$data 
    , input \LigeroRouter2$BBB1$RECEPTION1$CreditCounter1$PatientSource1$unbound_irdy 
    , input [0:0] \LigeroRouter2$BBB1$RECEPTION1$CreditCounter1$PatientSource1$unbound_data 
    , output \LigeroRouter2$BBB1$RECEPTION1$CreditCounter1$PatientSource1$trdy 
    , input \LigeroRouter2$BBB1$RECEPTION1$CreditCounter1$Sink1$unbound_trdy 
    , output \LigeroRouter2$BBB1$RECEPTION1$CreditCounter1$Sink1$irdy 
    , output [0:0] \LigeroRouter2$BBB1$RECEPTION1$CreditCounter1$Sink1$data 
    , input \LigeroRouter2$BBB2$Sink1$unbound_trdy 
    , output \LigeroRouter2$BBB2$Sink1$irdy 
    , output [1:0] \LigeroRouter2$BBB2$Sink1$data 
    , input \LigeroRouter2$BBB2$RECEPTION1$CreditCounter1$PatientSource1$unbound_irdy 
    , input [0:0] \LigeroRouter2$BBB2$RECEPTION1$CreditCounter1$PatientSource1$unbound_data 
    , output \LigeroRouter2$BBB2$RECEPTION1$CreditCounter1$PatientSource1$trdy 
    , input \LigeroRouter2$BBB2$RECEPTION1$CreditCounter1$Sink1$unbound_trdy 
    , output \LigeroRouter2$BBB2$RECEPTION1$CreditCounter1$Sink1$irdy 
    , output [0:0] \LigeroRouter2$BBB2$RECEPTION1$CreditCounter1$Sink1$data 
    , input \LigeroRouter2$BBB3$Sink1$unbound_trdy 
    , output \LigeroRouter2$BBB3$Sink1$irdy 
    , output [1:0] \LigeroRouter2$BBB3$Sink1$data 
    , input \LigeroRouter2$BBB3$RECEPTION1$CreditCounter1$PatientSource1$unbound_irdy 
    , input [0:0] \LigeroRouter2$BBB3$RECEPTION1$CreditCounter1$PatientSource1$unbound_data 
    , output \LigeroRouter2$BBB3$RECEPTION1$CreditCounter1$PatientSource1$trdy 
    , input \LigeroRouter2$BBB3$RECEPTION1$CreditCounter1$Sink1$unbound_trdy 
    , output \LigeroRouter2$BBB3$RECEPTION1$CreditCounter1$Sink1$irdy 
    , output [0:0] \LigeroRouter2$BBB3$RECEPTION1$CreditCounter1$Sink1$data 
    , input \LigeroRouter2$BBB4$Sink1$unbound_trdy 
    , output \LigeroRouter2$BBB4$Sink1$irdy 
    , output [1:0] \LigeroRouter2$BBB4$Sink1$data 
    , input \LigeroRouter2$BBB4$RECEPTION1$CreditCounter1$PatientSource1$unbound_irdy 
    , input [0:0] \LigeroRouter2$BBB4$RECEPTION1$CreditCounter1$PatientSource1$unbound_data 
    , output \LigeroRouter2$BBB4$RECEPTION1$CreditCounter1$PatientSource1$trdy 
    , input \LigeroRouter2$BBB4$RECEPTION1$CreditCounter1$Sink1$unbound_trdy 
    , output \LigeroRouter2$BBB4$RECEPTION1$CreditCounter1$Sink1$irdy 
    , output [0:0] \LigeroRouter2$BBB4$RECEPTION1$CreditCounter1$Sink1$data 
    , input \LigeroRouter3$BBB1$Sink1$unbound_trdy 
    , output \LigeroRouter3$BBB1$Sink1$irdy 
    , output [1:0] \LigeroRouter3$BBB1$Sink1$data 
    , input \LigeroRouter3$BBB1$RECEPTION1$CreditCounter1$PatientSource1$unbound_irdy 
    , input [0:0] \LigeroRouter3$BBB1$RECEPTION1$CreditCounter1$PatientSource1$unbound_data 
    , output \LigeroRouter3$BBB1$RECEPTION1$CreditCounter1$PatientSource1$trdy 
    , input \LigeroRouter3$BBB1$RECEPTION1$CreditCounter1$Sink1$unbound_trdy 
    , output \LigeroRouter3$BBB1$RECEPTION1$CreditCounter1$Sink1$irdy 
    , output [0:0] \LigeroRouter3$BBB1$RECEPTION1$CreditCounter1$Sink1$data 
    , input \LigeroRouter3$BBB2$Sink1$unbound_trdy 
    , output \LigeroRouter3$BBB2$Sink1$irdy 
    , output [1:0] \LigeroRouter3$BBB2$Sink1$data 
    , input \LigeroRouter3$BBB2$RECEPTION1$CreditCounter1$PatientSource1$unbound_irdy 
    , input [0:0] \LigeroRouter3$BBB2$RECEPTION1$CreditCounter1$PatientSource1$unbound_data 
    , output \LigeroRouter3$BBB2$RECEPTION1$CreditCounter1$PatientSource1$trdy 
    , input \LigeroRouter3$BBB2$RECEPTION1$CreditCounter1$Sink1$unbound_trdy 
    , output \LigeroRouter3$BBB2$RECEPTION1$CreditCounter1$Sink1$irdy 
    , output [0:0] \LigeroRouter3$BBB2$RECEPTION1$CreditCounter1$Sink1$data 
    , input \LigeroRouter3$BBB3$Sink1$unbound_trdy 
    , output \LigeroRouter3$BBB3$Sink1$irdy 
    , output [1:0] \LigeroRouter3$BBB3$Sink1$data 
    , input \LigeroRouter3$BBB3$RECEPTION1$CreditCounter1$PatientSource1$unbound_irdy 
    , input [0:0] \LigeroRouter3$BBB3$RECEPTION1$CreditCounter1$PatientSource1$unbound_data 
    , output \LigeroRouter3$BBB3$RECEPTION1$CreditCounter1$PatientSource1$trdy 
    , input \LigeroRouter3$BBB3$RECEPTION1$CreditCounter1$Sink1$unbound_trdy 
    , output \LigeroRouter3$BBB3$RECEPTION1$CreditCounter1$Sink1$irdy 
    , output [0:0] \LigeroRouter3$BBB3$RECEPTION1$CreditCounter1$Sink1$data 
    , input \LigeroRouter3$BBB4$Sink1$unbound_trdy 
    , output \LigeroRouter3$BBB4$Sink1$irdy 
    , output [1:0] \LigeroRouter3$BBB4$Sink1$data 
    , input \LigeroRouter3$BBB4$RECEPTION1$CreditCounter1$PatientSource1$unbound_irdy 
    , input [0:0] \LigeroRouter3$BBB4$RECEPTION1$CreditCounter1$PatientSource1$unbound_data 
    , output \LigeroRouter3$BBB4$RECEPTION1$CreditCounter1$PatientSource1$trdy 
    , input \LigeroRouter3$BBB4$RECEPTION1$CreditCounter1$Sink1$unbound_trdy 
    , output \LigeroRouter3$BBB4$RECEPTION1$CreditCounter1$Sink1$irdy 
    , output [0:0] \LigeroRouter3$BBB4$RECEPTION1$CreditCounter1$Sink1$data 
    , input \LigeroRouter4$BBB1$Sink1$unbound_trdy 
    , output \LigeroRouter4$BBB1$Sink1$irdy 
    , output [1:0] \LigeroRouter4$BBB1$Sink1$data 
    , input \LigeroRouter4$BBB1$RECEPTION1$CreditCounter1$PatientSource1$unbound_irdy 
    , input [0:0] \LigeroRouter4$BBB1$RECEPTION1$CreditCounter1$PatientSource1$unbound_data 
    , output \LigeroRouter4$BBB1$RECEPTION1$CreditCounter1$PatientSource1$trdy 
    , input \LigeroRouter4$BBB1$RECEPTION1$CreditCounter1$Sink1$unbound_trdy 
    , output \LigeroRouter4$BBB1$RECEPTION1$CreditCounter1$Sink1$irdy 
    , output [0:0] \LigeroRouter4$BBB1$RECEPTION1$CreditCounter1$Sink1$data 
    , input \LigeroRouter4$BBB2$Sink1$unbound_trdy 
    , output \LigeroRouter4$BBB2$Sink1$irdy 
    , output [1:0] \LigeroRouter4$BBB2$Sink1$data 
    , input \LigeroRouter4$BBB2$RECEPTION1$CreditCounter1$PatientSource1$unbound_irdy 
    , input [0:0] \LigeroRouter4$BBB2$RECEPTION1$CreditCounter1$PatientSource1$unbound_data 
    , output \LigeroRouter4$BBB2$RECEPTION1$CreditCounter1$PatientSource1$trdy 
    , input \LigeroRouter4$BBB2$RECEPTION1$CreditCounter1$Sink1$unbound_trdy 
    , output \LigeroRouter4$BBB2$RECEPTION1$CreditCounter1$Sink1$irdy 
    , output [0:0] \LigeroRouter4$BBB2$RECEPTION1$CreditCounter1$Sink1$data 
    , input \LigeroRouter4$BBB3$Sink1$unbound_trdy 
    , output \LigeroRouter4$BBB3$Sink1$irdy 
    , output [1:0] \LigeroRouter4$BBB3$Sink1$data 
    , input \LigeroRouter4$BBB3$RECEPTION1$CreditCounter1$PatientSource1$unbound_irdy 
    , input [0:0] \LigeroRouter4$BBB3$RECEPTION1$CreditCounter1$PatientSource1$unbound_data 
    , output \LigeroRouter4$BBB3$RECEPTION1$CreditCounter1$PatientSource1$trdy 
    , input \LigeroRouter4$BBB3$RECEPTION1$CreditCounter1$Sink1$unbound_trdy 
    , output \LigeroRouter4$BBB3$RECEPTION1$CreditCounter1$Sink1$irdy 
    , output [0:0] \LigeroRouter4$BBB3$RECEPTION1$CreditCounter1$Sink1$data 
    , input \LigeroRouter4$BBB4$Sink1$unbound_trdy 
    , output \LigeroRouter4$BBB4$Sink1$irdy 
    , output [1:0] \LigeroRouter4$BBB4$Sink1$data 
    , input \LigeroRouter4$BBB4$RECEPTION1$CreditCounter1$PatientSource1$unbound_irdy 
    , input [0:0] \LigeroRouter4$BBB4$RECEPTION1$CreditCounter1$PatientSource1$unbound_data 
    , output \LigeroRouter4$BBB4$RECEPTION1$CreditCounter1$PatientSource1$trdy 
    , input \LigeroRouter4$BBB4$RECEPTION1$CreditCounter1$Sink1$unbound_trdy 
    , output \LigeroRouter4$BBB4$RECEPTION1$CreditCounter1$Sink1$irdy 
    , output [0:0] \LigeroRouter4$BBB4$RECEPTION1$CreditCounter1$Sink1$data 
    , input \Sink1$unbound_trdy 
    , output \Sink1$irdy 
    , output [1:0] \Sink1$data 
    , input \Sink2$unbound_trdy 
    , output \Sink2$irdy 
    , output [1:0] \Sink2$data 
    , input \Sink3$unbound_trdy 
    , output \Sink3$irdy 
    , output [1:0] \Sink3$data 
    , input \Sink4$unbound_trdy 
    , output \Sink4$irdy 
    , output [1:0] \Sink4$data 
  );
  
  //
  // Channel declarations
  //
  wire \bus_wires1$irdy  ;
  wire [1:0] \bus_wires1$data  ;
  wire \bus_wires1$trdy  ;
  wire \bus_wires2$irdy  ;
  wire [1:0] \bus_wires2$data  ;
  wire \bus_wires2$trdy  ;
  wire \bus_wires3$irdy  ;
  wire [1:0] \bus_wires3$data  ;
  wire \bus_wires3$trdy  ;
  wire \bus_wires4$irdy  ;
  wire [1:0] \bus_wires4$data  ;
  wire \bus_wires4$trdy  ;
  wire \bus_wires5$irdy  ;
  wire [1:0] \bus_wires5$data  ;
  wire \bus_wires5$trdy  ;
  wire \bus_wires6$irdy  ;
  wire \bus_wires6$data  ;
  wire \bus_wires6$trdy  ;
  wire \bus_wires7$irdy  ;
  wire \bus_wires7$data  ;
  wire \bus_wires7$trdy  ;
  wire \bus_wires8$irdy  ;
  wire \bus_wires8$data  ;
  wire \bus_wires8$trdy  ;
  wire \bus_wires9$irdy  ;
  wire \bus_wires9$data  ;
  wire \bus_wires9$trdy  ;
  wire \bus_wires10$irdy  ;
  wire [1:0] \bus_wires10$data  ;
  wire \bus_wires10$trdy  ;
  wire \bus_wires11$irdy  ;
  wire [1:0] \bus_wires11$data  ;
  wire \bus_wires11$trdy  ;
  wire \bus_wires12$irdy  ;
  wire [1:0] \bus_wires12$data  ;
  wire \bus_wires12$trdy  ;
  wire \bus_wires13$irdy  ;
  wire [1:0] \bus_wires13$data  ;
  wire \bus_wires13$trdy  ;
  wire \bus_wires14$irdy  ;
  wire [1:0] \bus_wires14$data  ;
  wire \bus_wires14$trdy  ;
  wire \bus_wires15$irdy  ;
  wire \bus_wires15$data  ;
  wire \bus_wires15$trdy  ;
  wire \bus_wires16$irdy  ;
  wire \bus_wires16$data  ;
  wire \bus_wires16$trdy  ;
  wire \bus_wires17$irdy  ;
  wire \bus_wires17$data  ;
  wire \bus_wires17$trdy  ;
  wire \bus_wires18$irdy  ;
  wire \bus_wires18$data  ;
  wire \bus_wires18$trdy  ;
  wire \bus_wires19$irdy  ;
  wire [1:0] \bus_wires19$data  ;
  wire \bus_wires19$trdy  ;
  wire \bus_wires20$irdy  ;
  wire [1:0] \bus_wires20$data  ;
  wire \bus_wires20$trdy  ;
  wire \bus_wires21$irdy  ;
  wire [1:0] \bus_wires21$data  ;
  wire \bus_wires21$trdy  ;
  wire \bus_wires22$irdy  ;
  wire [1:0] \bus_wires22$data  ;
  wire \bus_wires22$trdy  ;
  wire \bus_wires23$irdy  ;
  wire [1:0] \bus_wires23$data  ;
  wire \bus_wires23$trdy  ;
  wire \bus_wires24$irdy  ;
  wire \bus_wires24$data  ;
  wire \bus_wires24$trdy  ;
  wire \bus_wires25$irdy  ;
  wire \bus_wires25$data  ;
  wire \bus_wires25$trdy  ;
  wire \bus_wires26$irdy  ;
  wire \bus_wires26$data  ;
  wire \bus_wires26$trdy  ;
  wire \bus_wires27$irdy  ;
  wire \bus_wires27$data  ;
  wire \bus_wires27$trdy  ;
  wire \bus_wires28$irdy  ;
  wire [1:0] \bus_wires28$data  ;
  wire \bus_wires28$trdy  ;
  wire \bus_wires29$irdy  ;
  wire [1:0] \bus_wires29$data  ;
  wire \bus_wires29$trdy  ;
  wire \bus_wires30$irdy  ;
  wire [1:0] \bus_wires30$data  ;
  wire \bus_wires30$trdy  ;
  wire \bus_wires31$irdy  ;
  wire [1:0] \bus_wires31$data  ;
  wire \bus_wires31$trdy  ;
  wire \bus_wires32$irdy  ;
  wire [1:0] \bus_wires32$data  ;
  wire \bus_wires32$trdy  ;
  wire \bus_wires33$irdy  ;
  wire \bus_wires33$data  ;
  wire \bus_wires33$trdy  ;
  wire \bus_wires34$irdy  ;
  wire \bus_wires34$data  ;
  wire \bus_wires34$trdy  ;
  wire \bus_wires35$irdy  ;
  wire \bus_wires35$data  ;
  wire \bus_wires35$trdy  ;
  wire \bus_wires36$irdy  ;
  wire \bus_wires36$data  ;
  wire \bus_wires36$trdy  ;
  wire \bus_locals1$irdy  ;
  wire [1:0] \bus_locals1$data  ;
  wire \bus_locals1$trdy  ;
  wire \bus_locals2$irdy  ;
  wire [1:0] \bus_locals2$data  ;
  wire \bus_locals2$trdy  ;
  wire \bus_locals3$irdy  ;
  wire [1:0] \bus_locals3$data  ;
  wire \bus_locals3$trdy  ;
  wire \bus_locals4$irdy  ;
  wire [1:0] \bus_locals4$data  ;
  wire \bus_locals4$trdy  ;
  
  //
  // Component and Macro instantiations
  //
  assign \Source1$trdy  = \bus_locals1$trdy  ;
  \Source  #(
    .DATASIZE(2)
  ) \Source1  (
      .\clk (\clk ), .\rst (\rst ), .\t (\t )
    , .\o0$irdy (\bus_locals1$irdy )
    , .\o0$data (\bus_locals1$data )
    , .\o0$trdy (\bus_locals1$trdy )
    , .\unbound_irdy (\Source1$unbound_irdy )
    , .\unbound_data (\Source1$unbound_data )
  );
  
  assign \Source2$trdy  = \bus_locals2$trdy  ;
  \Source  #(
    .DATASIZE(2)
  ) \Source2  (
      .\clk (\clk ), .\rst (\rst ), .\t (\t )
    , .\o0$irdy (\bus_locals2$irdy )
    , .\o0$data (\bus_locals2$data )
    , .\o0$trdy (\bus_locals2$trdy )
    , .\unbound_irdy (\Source2$unbound_irdy )
    , .\unbound_data (\Source2$unbound_data )
  );
  
  assign \Source3$trdy  = \bus_locals3$trdy  ;
  \Source  #(
    .DATASIZE(2)
  ) \Source3  (
      .\clk (\clk ), .\rst (\rst ), .\t (\t )
    , .\o0$irdy (\bus_locals3$irdy )
    , .\o0$data (\bus_locals3$data )
    , .\o0$trdy (\bus_locals3$trdy )
    , .\unbound_irdy (\Source3$unbound_irdy )
    , .\unbound_data (\Source3$unbound_data )
  );
  
  assign \Source4$trdy  = \bus_locals4$trdy  ;
  \Source  #(
    .DATASIZE(2)
  ) \Source4  (
      .\clk (\clk ), .\rst (\rst ), .\t (\t )
    , .\o0$irdy (\bus_locals4$irdy )
    , .\o0$data (\bus_locals4$data )
    , .\o0$trdy (\bus_locals4$trdy )
    , .\unbound_irdy (\Source4$unbound_irdy )
    , .\unbound_data (\Source4$unbound_data )
  );
  
  assign \Sink1$irdy  = \bus_wires1$irdy  ;
  assign \Sink1$data  = \bus_wires1$data  ;
  \Sink  #(
    .DATASIZE(2)
  ) \Sink1  (
      .\clk (\clk ), .\rst (\rst ), .\t (\t )
    , .\i0$irdy (\bus_wires1$irdy )
    , .\i0$data (\bus_wires1$data )
    , .\i0$trdy (\bus_wires1$trdy )
    , .\unbound_trdy (\Sink1$unbound_trdy )
  );
  
  assign \Sink2$irdy  = \bus_wires10$irdy  ;
  assign \Sink2$data  = \bus_wires10$data  ;
  \Sink  #(
    .DATASIZE(2)
  ) \Sink2  (
      .\clk (\clk ), .\rst (\rst ), .\t (\t )
    , .\i0$irdy (\bus_wires10$irdy )
    , .\i0$data (\bus_wires10$data )
    , .\i0$trdy (\bus_wires10$trdy )
    , .\unbound_trdy (\Sink2$unbound_trdy )
  );
  
  assign \Sink3$irdy  = \bus_wires19$irdy  ;
  assign \Sink3$data  = \bus_wires19$data  ;
  \Sink  #(
    .DATASIZE(2)
  ) \Sink3  (
      .\clk (\clk ), .\rst (\rst ), .\t (\t )
    , .\i0$irdy (\bus_wires19$irdy )
    , .\i0$data (\bus_wires19$data )
    , .\i0$trdy (\bus_wires19$trdy )
    , .\unbound_trdy (\Sink3$unbound_trdy )
  );
  
  assign \Sink4$irdy  = \bus_wires28$irdy  ;
  assign \Sink4$data  = \bus_wires28$data  ;
  \Sink  #(
    .DATASIZE(2)
  ) \Sink4  (
      .\clk (\clk ), .\rst (\rst ), .\t (\t )
    , .\i0$irdy (\bus_wires28$irdy )
    , .\i0$data (\bus_wires28$data )
    , .\i0$trdy (\bus_wires28$trdy )
    , .\unbound_trdy (\Sink4$unbound_trdy )
  );
  
  \LigeroRouter_0_0_2_2_2  \LigeroRouter1  (
      .\clk (\clk ), .\rst (\rst ), .\t (\t )
    , .\bus_ins1$irdy (\bus_locals1$irdy )
    , .\bus_ins1$data (\bus_locals1$data )
    , .\bus_ins1$trdy (\bus_locals1$trdy )
    , .\bus_ins2$irdy (\bus_wires12$irdy )
    , .\bus_ins2$data (\bus_wires12$data )
    , .\bus_ins2$trdy (\bus_wires12$trdy )
    , .\bus_ins3$irdy (\bus_wires11$irdy )
    , .\bus_ins3$data (\bus_wires11$data )
    , .\bus_ins3$trdy (\bus_wires11$trdy )
    , .\bus_ins4$irdy (\bus_wires22$irdy )
    , .\bus_ins4$data (\bus_wires22$data )
    , .\bus_ins4$trdy (\bus_wires22$trdy )
    , .\bus_ins5$irdy (\bus_wires23$irdy )
    , .\bus_ins5$data (\bus_wires23$data )
    , .\bus_ins5$trdy (\bus_wires23$trdy )
    , .\bus_ins6$irdy (\bus_wires16$irdy )
    , .\bus_ins6$data (\bus_wires16$data )
    , .\bus_ins6$trdy (\bus_wires16$trdy )
    , .\bus_ins7$irdy (\bus_wires15$irdy )
    , .\bus_ins7$data (\bus_wires15$data )
    , .\bus_ins7$trdy (\bus_wires15$trdy )
    , .\bus_ins8$irdy (\bus_wires26$irdy )
    , .\bus_ins8$data (\bus_wires26$data )
    , .\bus_ins8$trdy (\bus_wires26$trdy )
    , .\bus_ins9$irdy (\bus_wires27$irdy )
    , .\bus_ins9$data (\bus_wires27$data )
    , .\bus_ins9$trdy (\bus_wires27$trdy )
    , .\bus_outs1$irdy (\bus_wires1$irdy )
    , .\bus_outs1$data (\bus_wires1$data )
    , .\bus_outs1$trdy (\bus_wires1$trdy )
    , .\bus_outs2$irdy (\bus_wires2$irdy )
    , .\bus_outs2$data (\bus_wires2$data )
    , .\bus_outs2$trdy (\bus_wires2$trdy )
    , .\bus_outs3$irdy (\bus_wires3$irdy )
    , .\bus_outs3$data (\bus_wires3$data )
    , .\bus_outs3$trdy (\bus_wires3$trdy )
    , .\bus_outs4$irdy (\bus_wires4$irdy )
    , .\bus_outs4$data (\bus_wires4$data )
    , .\bus_outs4$trdy (\bus_wires4$trdy )
    , .\bus_outs5$irdy (\bus_wires5$irdy )
    , .\bus_outs5$data (\bus_wires5$data )
    , .\bus_outs5$trdy (\bus_wires5$trdy )
    , .\bus_outs6$irdy (\bus_wires6$irdy )
    , .\bus_outs6$data (\bus_wires6$data )
    , .\bus_outs6$trdy (\bus_wires6$trdy )
    , .\bus_outs7$irdy (\bus_wires7$irdy )
    , .\bus_outs7$data (\bus_wires7$data )
    , .\bus_outs7$trdy (\bus_wires7$trdy )
    , .\bus_outs8$irdy (\bus_wires8$irdy )
    , .\bus_outs8$data (\bus_wires8$data )
    , .\bus_outs8$trdy (\bus_wires8$trdy )
    , .\bus_outs9$irdy (\bus_wires9$irdy )
    , .\bus_outs9$data (\bus_wires9$data )
    , .\bus_outs9$trdy (\bus_wires9$trdy )
    , .\BBB1$Sink1$unbound_trdy (\LigeroRouter1$BBB1$Sink1$unbound_trdy )
    , .\BBB1$Sink1$irdy (\LigeroRouter1$BBB1$Sink1$irdy )
    , .\BBB1$Sink1$data (\LigeroRouter1$BBB1$Sink1$data )
    , .\BBB1$RECEPTION1$CreditCounter1$PatientSource1$unbound_irdy (\LigeroRouter1$BBB1$RECEPTION1$CreditCounter1$PatientSource1$unbound_irdy )
    , .\BBB1$RECEPTION1$CreditCounter1$PatientSource1$unbound_data (\LigeroRouter1$BBB1$RECEPTION1$CreditCounter1$PatientSource1$unbound_data )
    , .\BBB1$RECEPTION1$CreditCounter1$PatientSource1$trdy (\LigeroRouter1$BBB1$RECEPTION1$CreditCounter1$PatientSource1$trdy )
    , .\BBB1$RECEPTION1$CreditCounter1$Sink1$unbound_trdy (\LigeroRouter1$BBB1$RECEPTION1$CreditCounter1$Sink1$unbound_trdy )
    , .\BBB1$RECEPTION1$CreditCounter1$Sink1$irdy (\LigeroRouter1$BBB1$RECEPTION1$CreditCounter1$Sink1$irdy )
    , .\BBB1$RECEPTION1$CreditCounter1$Sink1$data (\LigeroRouter1$BBB1$RECEPTION1$CreditCounter1$Sink1$data )
    , .\BBB2$Sink1$unbound_trdy (\LigeroRouter1$BBB2$Sink1$unbound_trdy )
    , .\BBB2$Sink1$irdy (\LigeroRouter1$BBB2$Sink1$irdy )
    , .\BBB2$Sink1$data (\LigeroRouter1$BBB2$Sink1$data )
    , .\BBB2$RECEPTION1$CreditCounter1$PatientSource1$unbound_irdy (\LigeroRouter1$BBB2$RECEPTION1$CreditCounter1$PatientSource1$unbound_irdy )
    , .\BBB2$RECEPTION1$CreditCounter1$PatientSource1$unbound_data (\LigeroRouter1$BBB2$RECEPTION1$CreditCounter1$PatientSource1$unbound_data )
    , .\BBB2$RECEPTION1$CreditCounter1$PatientSource1$trdy (\LigeroRouter1$BBB2$RECEPTION1$CreditCounter1$PatientSource1$trdy )
    , .\BBB2$RECEPTION1$CreditCounter1$Sink1$unbound_trdy (\LigeroRouter1$BBB2$RECEPTION1$CreditCounter1$Sink1$unbound_trdy )
    , .\BBB2$RECEPTION1$CreditCounter1$Sink1$irdy (\LigeroRouter1$BBB2$RECEPTION1$CreditCounter1$Sink1$irdy )
    , .\BBB2$RECEPTION1$CreditCounter1$Sink1$data (\LigeroRouter1$BBB2$RECEPTION1$CreditCounter1$Sink1$data )
    , .\BBB3$Sink1$unbound_trdy (\LigeroRouter1$BBB3$Sink1$unbound_trdy )
    , .\BBB3$Sink1$irdy (\LigeroRouter1$BBB3$Sink1$irdy )
    , .\BBB3$Sink1$data (\LigeroRouter1$BBB3$Sink1$data )
    , .\BBB3$RECEPTION1$CreditCounter1$PatientSource1$unbound_irdy (\LigeroRouter1$BBB3$RECEPTION1$CreditCounter1$PatientSource1$unbound_irdy )
    , .\BBB3$RECEPTION1$CreditCounter1$PatientSource1$unbound_data (\LigeroRouter1$BBB3$RECEPTION1$CreditCounter1$PatientSource1$unbound_data )
    , .\BBB3$RECEPTION1$CreditCounter1$PatientSource1$trdy (\LigeroRouter1$BBB3$RECEPTION1$CreditCounter1$PatientSource1$trdy )
    , .\BBB3$RECEPTION1$CreditCounter1$Sink1$unbound_trdy (\LigeroRouter1$BBB3$RECEPTION1$CreditCounter1$Sink1$unbound_trdy )
    , .\BBB3$RECEPTION1$CreditCounter1$Sink1$irdy (\LigeroRouter1$BBB3$RECEPTION1$CreditCounter1$Sink1$irdy )
    , .\BBB3$RECEPTION1$CreditCounter1$Sink1$data (\LigeroRouter1$BBB3$RECEPTION1$CreditCounter1$Sink1$data )
    , .\BBB4$Sink1$unbound_trdy (\LigeroRouter1$BBB4$Sink1$unbound_trdy )
    , .\BBB4$Sink1$irdy (\LigeroRouter1$BBB4$Sink1$irdy )
    , .\BBB4$Sink1$data (\LigeroRouter1$BBB4$Sink1$data )
    , .\BBB4$RECEPTION1$CreditCounter1$PatientSource1$unbound_irdy (\LigeroRouter1$BBB4$RECEPTION1$CreditCounter1$PatientSource1$unbound_irdy )
    , .\BBB4$RECEPTION1$CreditCounter1$PatientSource1$unbound_data (\LigeroRouter1$BBB4$RECEPTION1$CreditCounter1$PatientSource1$unbound_data )
    , .\BBB4$RECEPTION1$CreditCounter1$PatientSource1$trdy (\LigeroRouter1$BBB4$RECEPTION1$CreditCounter1$PatientSource1$trdy )
    , .\BBB4$RECEPTION1$CreditCounter1$Sink1$unbound_trdy (\LigeroRouter1$BBB4$RECEPTION1$CreditCounter1$Sink1$unbound_trdy )
    , .\BBB4$RECEPTION1$CreditCounter1$Sink1$irdy (\LigeroRouter1$BBB4$RECEPTION1$CreditCounter1$Sink1$irdy )
    , .\BBB4$RECEPTION1$CreditCounter1$Sink1$data (\LigeroRouter1$BBB4$RECEPTION1$CreditCounter1$Sink1$data )
  );
  
  \LigeroRouter_1_0_2_2_2  \LigeroRouter2  (
      .\clk (\clk ), .\rst (\rst ), .\t (\t )
    , .\bus_ins1$irdy (\bus_locals2$irdy )
    , .\bus_ins1$data (\bus_locals2$data )
    , .\bus_ins1$trdy (\bus_locals2$trdy )
    , .\bus_ins2$irdy (\bus_wires3$irdy )
    , .\bus_ins2$data (\bus_wires3$data )
    , .\bus_ins2$trdy (\bus_wires3$trdy )
    , .\bus_ins3$irdy (\bus_wires2$irdy )
    , .\bus_ins3$data (\bus_wires2$data )
    , .\bus_ins3$trdy (\bus_wires2$trdy )
    , .\bus_ins4$irdy (\bus_wires31$irdy )
    , .\bus_ins4$data (\bus_wires31$data )
    , .\bus_ins4$trdy (\bus_wires31$trdy )
    , .\bus_ins5$irdy (\bus_wires32$irdy )
    , .\bus_ins5$data (\bus_wires32$data )
    , .\bus_ins5$trdy (\bus_wires32$trdy )
    , .\bus_ins6$irdy (\bus_wires7$irdy )
    , .\bus_ins6$data (\bus_wires7$data )
    , .\bus_ins6$trdy (\bus_wires7$trdy )
    , .\bus_ins7$irdy (\bus_wires6$irdy )
    , .\bus_ins7$data (\bus_wires6$data )
    , .\bus_ins7$trdy (\bus_wires6$trdy )
    , .\bus_ins8$irdy (\bus_wires35$irdy )
    , .\bus_ins8$data (\bus_wires35$data )
    , .\bus_ins8$trdy (\bus_wires35$trdy )
    , .\bus_ins9$irdy (\bus_wires36$irdy )
    , .\bus_ins9$data (\bus_wires36$data )
    , .\bus_ins9$trdy (\bus_wires36$trdy )
    , .\bus_outs1$irdy (\bus_wires10$irdy )
    , .\bus_outs1$data (\bus_wires10$data )
    , .\bus_outs1$trdy (\bus_wires10$trdy )
    , .\bus_outs2$irdy (\bus_wires11$irdy )
    , .\bus_outs2$data (\bus_wires11$data )
    , .\bus_outs2$trdy (\bus_wires11$trdy )
    , .\bus_outs3$irdy (\bus_wires12$irdy )
    , .\bus_outs3$data (\bus_wires12$data )
    , .\bus_outs3$trdy (\bus_wires12$trdy )
    , .\bus_outs4$irdy (\bus_wires13$irdy )
    , .\bus_outs4$data (\bus_wires13$data )
    , .\bus_outs4$trdy (\bus_wires13$trdy )
    , .\bus_outs5$irdy (\bus_wires14$irdy )
    , .\bus_outs5$data (\bus_wires14$data )
    , .\bus_outs5$trdy (\bus_wires14$trdy )
    , .\bus_outs6$irdy (\bus_wires15$irdy )
    , .\bus_outs6$data (\bus_wires15$data )
    , .\bus_outs6$trdy (\bus_wires15$trdy )
    , .\bus_outs7$irdy (\bus_wires16$irdy )
    , .\bus_outs7$data (\bus_wires16$data )
    , .\bus_outs7$trdy (\bus_wires16$trdy )
    , .\bus_outs8$irdy (\bus_wires17$irdy )
    , .\bus_outs8$data (\bus_wires17$data )
    , .\bus_outs8$trdy (\bus_wires17$trdy )
    , .\bus_outs9$irdy (\bus_wires18$irdy )
    , .\bus_outs9$data (\bus_wires18$data )
    , .\bus_outs9$trdy (\bus_wires18$trdy )
    , .\BBB1$Sink1$unbound_trdy (\LigeroRouter2$BBB1$Sink1$unbound_trdy )
    , .\BBB1$Sink1$irdy (\LigeroRouter2$BBB1$Sink1$irdy )
    , .\BBB1$Sink1$data (\LigeroRouter2$BBB1$Sink1$data )
    , .\BBB1$RECEPTION1$CreditCounter1$PatientSource1$unbound_irdy (\LigeroRouter2$BBB1$RECEPTION1$CreditCounter1$PatientSource1$unbound_irdy )
    , .\BBB1$RECEPTION1$CreditCounter1$PatientSource1$unbound_data (\LigeroRouter2$BBB1$RECEPTION1$CreditCounter1$PatientSource1$unbound_data )
    , .\BBB1$RECEPTION1$CreditCounter1$PatientSource1$trdy (\LigeroRouter2$BBB1$RECEPTION1$CreditCounter1$PatientSource1$trdy )
    , .\BBB1$RECEPTION1$CreditCounter1$Sink1$unbound_trdy (\LigeroRouter2$BBB1$RECEPTION1$CreditCounter1$Sink1$unbound_trdy )
    , .\BBB1$RECEPTION1$CreditCounter1$Sink1$irdy (\LigeroRouter2$BBB1$RECEPTION1$CreditCounter1$Sink1$irdy )
    , .\BBB1$RECEPTION1$CreditCounter1$Sink1$data (\LigeroRouter2$BBB1$RECEPTION1$CreditCounter1$Sink1$data )
    , .\BBB2$Sink1$unbound_trdy (\LigeroRouter2$BBB2$Sink1$unbound_trdy )
    , .\BBB2$Sink1$irdy (\LigeroRouter2$BBB2$Sink1$irdy )
    , .\BBB2$Sink1$data (\LigeroRouter2$BBB2$Sink1$data )
    , .\BBB2$RECEPTION1$CreditCounter1$PatientSource1$unbound_irdy (\LigeroRouter2$BBB2$RECEPTION1$CreditCounter1$PatientSource1$unbound_irdy )
    , .\BBB2$RECEPTION1$CreditCounter1$PatientSource1$unbound_data (\LigeroRouter2$BBB2$RECEPTION1$CreditCounter1$PatientSource1$unbound_data )
    , .\BBB2$RECEPTION1$CreditCounter1$PatientSource1$trdy (\LigeroRouter2$BBB2$RECEPTION1$CreditCounter1$PatientSource1$trdy )
    , .\BBB2$RECEPTION1$CreditCounter1$Sink1$unbound_trdy (\LigeroRouter2$BBB2$RECEPTION1$CreditCounter1$Sink1$unbound_trdy )
    , .\BBB2$RECEPTION1$CreditCounter1$Sink1$irdy (\LigeroRouter2$BBB2$RECEPTION1$CreditCounter1$Sink1$irdy )
    , .\BBB2$RECEPTION1$CreditCounter1$Sink1$data (\LigeroRouter2$BBB2$RECEPTION1$CreditCounter1$Sink1$data )
    , .\BBB3$Sink1$unbound_trdy (\LigeroRouter2$BBB3$Sink1$unbound_trdy )
    , .\BBB3$Sink1$irdy (\LigeroRouter2$BBB3$Sink1$irdy )
    , .\BBB3$Sink1$data (\LigeroRouter2$BBB3$Sink1$data )
    , .\BBB3$RECEPTION1$CreditCounter1$PatientSource1$unbound_irdy (\LigeroRouter2$BBB3$RECEPTION1$CreditCounter1$PatientSource1$unbound_irdy )
    , .\BBB3$RECEPTION1$CreditCounter1$PatientSource1$unbound_data (\LigeroRouter2$BBB3$RECEPTION1$CreditCounter1$PatientSource1$unbound_data )
    , .\BBB3$RECEPTION1$CreditCounter1$PatientSource1$trdy (\LigeroRouter2$BBB3$RECEPTION1$CreditCounter1$PatientSource1$trdy )
    , .\BBB3$RECEPTION1$CreditCounter1$Sink1$unbound_trdy (\LigeroRouter2$BBB3$RECEPTION1$CreditCounter1$Sink1$unbound_trdy )
    , .\BBB3$RECEPTION1$CreditCounter1$Sink1$irdy (\LigeroRouter2$BBB3$RECEPTION1$CreditCounter1$Sink1$irdy )
    , .\BBB3$RECEPTION1$CreditCounter1$Sink1$data (\LigeroRouter2$BBB3$RECEPTION1$CreditCounter1$Sink1$data )
    , .\BBB4$Sink1$unbound_trdy (\LigeroRouter2$BBB4$Sink1$unbound_trdy )
    , .\BBB4$Sink1$irdy (\LigeroRouter2$BBB4$Sink1$irdy )
    , .\BBB4$Sink1$data (\LigeroRouter2$BBB4$Sink1$data )
    , .\BBB4$RECEPTION1$CreditCounter1$PatientSource1$unbound_irdy (\LigeroRouter2$BBB4$RECEPTION1$CreditCounter1$PatientSource1$unbound_irdy )
    , .\BBB4$RECEPTION1$CreditCounter1$PatientSource1$unbound_data (\LigeroRouter2$BBB4$RECEPTION1$CreditCounter1$PatientSource1$unbound_data )
    , .\BBB4$RECEPTION1$CreditCounter1$PatientSource1$trdy (\LigeroRouter2$BBB4$RECEPTION1$CreditCounter1$PatientSource1$trdy )
    , .\BBB4$RECEPTION1$CreditCounter1$Sink1$unbound_trdy (\LigeroRouter2$BBB4$RECEPTION1$CreditCounter1$Sink1$unbound_trdy )
    , .\BBB4$RECEPTION1$CreditCounter1$Sink1$irdy (\LigeroRouter2$BBB4$RECEPTION1$CreditCounter1$Sink1$irdy )
    , .\BBB4$RECEPTION1$CreditCounter1$Sink1$data (\LigeroRouter2$BBB4$RECEPTION1$CreditCounter1$Sink1$data )
  );
  
  \LigeroRouter_0_1_2_2_2  \LigeroRouter3  (
      .\clk (\clk ), .\rst (\rst ), .\t (\t )
    , .\bus_ins1$irdy (\bus_locals3$irdy )
    , .\bus_ins1$data (\bus_locals3$data )
    , .\bus_ins1$trdy (\bus_locals3$trdy )
    , .\bus_ins2$irdy (\bus_wires30$irdy )
    , .\bus_ins2$data (\bus_wires30$data )
    , .\bus_ins2$trdy (\bus_wires30$trdy )
    , .\bus_ins3$irdy (\bus_wires29$irdy )
    , .\bus_ins3$data (\bus_wires29$data )
    , .\bus_ins3$trdy (\bus_wires29$trdy )
    , .\bus_ins4$irdy (\bus_wires4$irdy )
    , .\bus_ins4$data (\bus_wires4$data )
    , .\bus_ins4$trdy (\bus_wires4$trdy )
    , .\bus_ins5$irdy (\bus_wires5$irdy )
    , .\bus_ins5$data (\bus_wires5$data )
    , .\bus_ins5$trdy (\bus_wires5$trdy )
    , .\bus_ins6$irdy (\bus_wires34$irdy )
    , .\bus_ins6$data (\bus_wires34$data )
    , .\bus_ins6$trdy (\bus_wires34$trdy )
    , .\bus_ins7$irdy (\bus_wires33$irdy )
    , .\bus_ins7$data (\bus_wires33$data )
    , .\bus_ins7$trdy (\bus_wires33$trdy )
    , .\bus_ins8$irdy (\bus_wires8$irdy )
    , .\bus_ins8$data (\bus_wires8$data )
    , .\bus_ins8$trdy (\bus_wires8$trdy )
    , .\bus_ins9$irdy (\bus_wires9$irdy )
    , .\bus_ins9$data (\bus_wires9$data )
    , .\bus_ins9$trdy (\bus_wires9$trdy )
    , .\bus_outs1$irdy (\bus_wires19$irdy )
    , .\bus_outs1$data (\bus_wires19$data )
    , .\bus_outs1$trdy (\bus_wires19$trdy )
    , .\bus_outs2$irdy (\bus_wires20$irdy )
    , .\bus_outs2$data (\bus_wires20$data )
    , .\bus_outs2$trdy (\bus_wires20$trdy )
    , .\bus_outs3$irdy (\bus_wires21$irdy )
    , .\bus_outs3$data (\bus_wires21$data )
    , .\bus_outs3$trdy (\bus_wires21$trdy )
    , .\bus_outs4$irdy (\bus_wires22$irdy )
    , .\bus_outs4$data (\bus_wires22$data )
    , .\bus_outs4$trdy (\bus_wires22$trdy )
    , .\bus_outs5$irdy (\bus_wires23$irdy )
    , .\bus_outs5$data (\bus_wires23$data )
    , .\bus_outs5$trdy (\bus_wires23$trdy )
    , .\bus_outs6$irdy (\bus_wires24$irdy )
    , .\bus_outs6$data (\bus_wires24$data )
    , .\bus_outs6$trdy (\bus_wires24$trdy )
    , .\bus_outs7$irdy (\bus_wires25$irdy )
    , .\bus_outs7$data (\bus_wires25$data )
    , .\bus_outs7$trdy (\bus_wires25$trdy )
    , .\bus_outs8$irdy (\bus_wires26$irdy )
    , .\bus_outs8$data (\bus_wires26$data )
    , .\bus_outs8$trdy (\bus_wires26$trdy )
    , .\bus_outs9$irdy (\bus_wires27$irdy )
    , .\bus_outs9$data (\bus_wires27$data )
    , .\bus_outs9$trdy (\bus_wires27$trdy )
    , .\BBB1$Sink1$unbound_trdy (\LigeroRouter3$BBB1$Sink1$unbound_trdy )
    , .\BBB1$Sink1$irdy (\LigeroRouter3$BBB1$Sink1$irdy )
    , .\BBB1$Sink1$data (\LigeroRouter3$BBB1$Sink1$data )
    , .\BBB1$RECEPTION1$CreditCounter1$PatientSource1$unbound_irdy (\LigeroRouter3$BBB1$RECEPTION1$CreditCounter1$PatientSource1$unbound_irdy )
    , .\BBB1$RECEPTION1$CreditCounter1$PatientSource1$unbound_data (\LigeroRouter3$BBB1$RECEPTION1$CreditCounter1$PatientSource1$unbound_data )
    , .\BBB1$RECEPTION1$CreditCounter1$PatientSource1$trdy (\LigeroRouter3$BBB1$RECEPTION1$CreditCounter1$PatientSource1$trdy )
    , .\BBB1$RECEPTION1$CreditCounter1$Sink1$unbound_trdy (\LigeroRouter3$BBB1$RECEPTION1$CreditCounter1$Sink1$unbound_trdy )
    , .\BBB1$RECEPTION1$CreditCounter1$Sink1$irdy (\LigeroRouter3$BBB1$RECEPTION1$CreditCounter1$Sink1$irdy )
    , .\BBB1$RECEPTION1$CreditCounter1$Sink1$data (\LigeroRouter3$BBB1$RECEPTION1$CreditCounter1$Sink1$data )
    , .\BBB2$Sink1$unbound_trdy (\LigeroRouter3$BBB2$Sink1$unbound_trdy )
    , .\BBB2$Sink1$irdy (\LigeroRouter3$BBB2$Sink1$irdy )
    , .\BBB2$Sink1$data (\LigeroRouter3$BBB2$Sink1$data )
    , .\BBB2$RECEPTION1$CreditCounter1$PatientSource1$unbound_irdy (\LigeroRouter3$BBB2$RECEPTION1$CreditCounter1$PatientSource1$unbound_irdy )
    , .\BBB2$RECEPTION1$CreditCounter1$PatientSource1$unbound_data (\LigeroRouter3$BBB2$RECEPTION1$CreditCounter1$PatientSource1$unbound_data )
    , .\BBB2$RECEPTION1$CreditCounter1$PatientSource1$trdy (\LigeroRouter3$BBB2$RECEPTION1$CreditCounter1$PatientSource1$trdy )
    , .\BBB2$RECEPTION1$CreditCounter1$Sink1$unbound_trdy (\LigeroRouter3$BBB2$RECEPTION1$CreditCounter1$Sink1$unbound_trdy )
    , .\BBB2$RECEPTION1$CreditCounter1$Sink1$irdy (\LigeroRouter3$BBB2$RECEPTION1$CreditCounter1$Sink1$irdy )
    , .\BBB2$RECEPTION1$CreditCounter1$Sink1$data (\LigeroRouter3$BBB2$RECEPTION1$CreditCounter1$Sink1$data )
    , .\BBB3$Sink1$unbound_trdy (\LigeroRouter3$BBB3$Sink1$unbound_trdy )
    , .\BBB3$Sink1$irdy (\LigeroRouter3$BBB3$Sink1$irdy )
    , .\BBB3$Sink1$data (\LigeroRouter3$BBB3$Sink1$data )
    , .\BBB3$RECEPTION1$CreditCounter1$PatientSource1$unbound_irdy (\LigeroRouter3$BBB3$RECEPTION1$CreditCounter1$PatientSource1$unbound_irdy )
    , .\BBB3$RECEPTION1$CreditCounter1$PatientSource1$unbound_data (\LigeroRouter3$BBB3$RECEPTION1$CreditCounter1$PatientSource1$unbound_data )
    , .\BBB3$RECEPTION1$CreditCounter1$PatientSource1$trdy (\LigeroRouter3$BBB3$RECEPTION1$CreditCounter1$PatientSource1$trdy )
    , .\BBB3$RECEPTION1$CreditCounter1$Sink1$unbound_trdy (\LigeroRouter3$BBB3$RECEPTION1$CreditCounter1$Sink1$unbound_trdy )
    , .\BBB3$RECEPTION1$CreditCounter1$Sink1$irdy (\LigeroRouter3$BBB3$RECEPTION1$CreditCounter1$Sink1$irdy )
    , .\BBB3$RECEPTION1$CreditCounter1$Sink1$data (\LigeroRouter3$BBB3$RECEPTION1$CreditCounter1$Sink1$data )
    , .\BBB4$Sink1$unbound_trdy (\LigeroRouter3$BBB4$Sink1$unbound_trdy )
    , .\BBB4$Sink1$irdy (\LigeroRouter3$BBB4$Sink1$irdy )
    , .\BBB4$Sink1$data (\LigeroRouter3$BBB4$Sink1$data )
    , .\BBB4$RECEPTION1$CreditCounter1$PatientSource1$unbound_irdy (\LigeroRouter3$BBB4$RECEPTION1$CreditCounter1$PatientSource1$unbound_irdy )
    , .\BBB4$RECEPTION1$CreditCounter1$PatientSource1$unbound_data (\LigeroRouter3$BBB4$RECEPTION1$CreditCounter1$PatientSource1$unbound_data )
    , .\BBB4$RECEPTION1$CreditCounter1$PatientSource1$trdy (\LigeroRouter3$BBB4$RECEPTION1$CreditCounter1$PatientSource1$trdy )
    , .\BBB4$RECEPTION1$CreditCounter1$Sink1$unbound_trdy (\LigeroRouter3$BBB4$RECEPTION1$CreditCounter1$Sink1$unbound_trdy )
    , .\BBB4$RECEPTION1$CreditCounter1$Sink1$irdy (\LigeroRouter3$BBB4$RECEPTION1$CreditCounter1$Sink1$irdy )
    , .\BBB4$RECEPTION1$CreditCounter1$Sink1$data (\LigeroRouter3$BBB4$RECEPTION1$CreditCounter1$Sink1$data )
  );
  
  \LigeroRouter_1_1_2_2_2  \LigeroRouter4  (
      .\clk (\clk ), .\rst (\rst ), .\t (\t )
    , .\bus_ins1$irdy (\bus_locals4$irdy )
    , .\bus_ins1$data (\bus_locals4$data )
    , .\bus_ins1$trdy (\bus_locals4$trdy )
    , .\bus_ins2$irdy (\bus_wires21$irdy )
    , .\bus_ins2$data (\bus_wires21$data )
    , .\bus_ins2$trdy (\bus_wires21$trdy )
    , .\bus_ins3$irdy (\bus_wires20$irdy )
    , .\bus_ins3$data (\bus_wires20$data )
    , .\bus_ins3$trdy (\bus_wires20$trdy )
    , .\bus_ins4$irdy (\bus_wires13$irdy )
    , .\bus_ins4$data (\bus_wires13$data )
    , .\bus_ins4$trdy (\bus_wires13$trdy )
    , .\bus_ins5$irdy (\bus_wires14$irdy )
    , .\bus_ins5$data (\bus_wires14$data )
    , .\bus_ins5$trdy (\bus_wires14$trdy )
    , .\bus_ins6$irdy (\bus_wires25$irdy )
    , .\bus_ins6$data (\bus_wires25$data )
    , .\bus_ins6$trdy (\bus_wires25$trdy )
    , .\bus_ins7$irdy (\bus_wires24$irdy )
    , .\bus_ins7$data (\bus_wires24$data )
    , .\bus_ins7$trdy (\bus_wires24$trdy )
    , .\bus_ins8$irdy (\bus_wires17$irdy )
    , .\bus_ins8$data (\bus_wires17$data )
    , .\bus_ins8$trdy (\bus_wires17$trdy )
    , .\bus_ins9$irdy (\bus_wires18$irdy )
    , .\bus_ins9$data (\bus_wires18$data )
    , .\bus_ins9$trdy (\bus_wires18$trdy )
    , .\bus_outs1$irdy (\bus_wires28$irdy )
    , .\bus_outs1$data (\bus_wires28$data )
    , .\bus_outs1$trdy (\bus_wires28$trdy )
    , .\bus_outs2$irdy (\bus_wires29$irdy )
    , .\bus_outs2$data (\bus_wires29$data )
    , .\bus_outs2$trdy (\bus_wires29$trdy )
    , .\bus_outs3$irdy (\bus_wires30$irdy )
    , .\bus_outs3$data (\bus_wires30$data )
    , .\bus_outs3$trdy (\bus_wires30$trdy )
    , .\bus_outs4$irdy (\bus_wires31$irdy )
    , .\bus_outs4$data (\bus_wires31$data )
    , .\bus_outs4$trdy (\bus_wires31$trdy )
    , .\bus_outs5$irdy (\bus_wires32$irdy )
    , .\bus_outs5$data (\bus_wires32$data )
    , .\bus_outs5$trdy (\bus_wires32$trdy )
    , .\bus_outs6$irdy (\bus_wires33$irdy )
    , .\bus_outs6$data (\bus_wires33$data )
    , .\bus_outs6$trdy (\bus_wires33$trdy )
    , .\bus_outs7$irdy (\bus_wires34$irdy )
    , .\bus_outs7$data (\bus_wires34$data )
    , .\bus_outs7$trdy (\bus_wires34$trdy )
    , .\bus_outs8$irdy (\bus_wires35$irdy )
    , .\bus_outs8$data (\bus_wires35$data )
    , .\bus_outs8$trdy (\bus_wires35$trdy )
    , .\bus_outs9$irdy (\bus_wires36$irdy )
    , .\bus_outs9$data (\bus_wires36$data )
    , .\bus_outs9$trdy (\bus_wires36$trdy )
    , .\BBB1$Sink1$unbound_trdy (\LigeroRouter4$BBB1$Sink1$unbound_trdy )
    , .\BBB1$Sink1$irdy (\LigeroRouter4$BBB1$Sink1$irdy )
    , .\BBB1$Sink1$data (\LigeroRouter4$BBB1$Sink1$data )
    , .\BBB1$RECEPTION1$CreditCounter1$PatientSource1$unbound_irdy (\LigeroRouter4$BBB1$RECEPTION1$CreditCounter1$PatientSource1$unbound_irdy )
    , .\BBB1$RECEPTION1$CreditCounter1$PatientSource1$unbound_data (\LigeroRouter4$BBB1$RECEPTION1$CreditCounter1$PatientSource1$unbound_data )
    , .\BBB1$RECEPTION1$CreditCounter1$PatientSource1$trdy (\LigeroRouter4$BBB1$RECEPTION1$CreditCounter1$PatientSource1$trdy )
    , .\BBB1$RECEPTION1$CreditCounter1$Sink1$unbound_trdy (\LigeroRouter4$BBB1$RECEPTION1$CreditCounter1$Sink1$unbound_trdy )
    , .\BBB1$RECEPTION1$CreditCounter1$Sink1$irdy (\LigeroRouter4$BBB1$RECEPTION1$CreditCounter1$Sink1$irdy )
    , .\BBB1$RECEPTION1$CreditCounter1$Sink1$data (\LigeroRouter4$BBB1$RECEPTION1$CreditCounter1$Sink1$data )
    , .\BBB2$Sink1$unbound_trdy (\LigeroRouter4$BBB2$Sink1$unbound_trdy )
    , .\BBB2$Sink1$irdy (\LigeroRouter4$BBB2$Sink1$irdy )
    , .\BBB2$Sink1$data (\LigeroRouter4$BBB2$Sink1$data )
    , .\BBB2$RECEPTION1$CreditCounter1$PatientSource1$unbound_irdy (\LigeroRouter4$BBB2$RECEPTION1$CreditCounter1$PatientSource1$unbound_irdy )
    , .\BBB2$RECEPTION1$CreditCounter1$PatientSource1$unbound_data (\LigeroRouter4$BBB2$RECEPTION1$CreditCounter1$PatientSource1$unbound_data )
    , .\BBB2$RECEPTION1$CreditCounter1$PatientSource1$trdy (\LigeroRouter4$BBB2$RECEPTION1$CreditCounter1$PatientSource1$trdy )
    , .\BBB2$RECEPTION1$CreditCounter1$Sink1$unbound_trdy (\LigeroRouter4$BBB2$RECEPTION1$CreditCounter1$Sink1$unbound_trdy )
    , .\BBB2$RECEPTION1$CreditCounter1$Sink1$irdy (\LigeroRouter4$BBB2$RECEPTION1$CreditCounter1$Sink1$irdy )
    , .\BBB2$RECEPTION1$CreditCounter1$Sink1$data (\LigeroRouter4$BBB2$RECEPTION1$CreditCounter1$Sink1$data )
    , .\BBB3$Sink1$unbound_trdy (\LigeroRouter4$BBB3$Sink1$unbound_trdy )
    , .\BBB3$Sink1$irdy (\LigeroRouter4$BBB3$Sink1$irdy )
    , .\BBB3$Sink1$data (\LigeroRouter4$BBB3$Sink1$data )
    , .\BBB3$RECEPTION1$CreditCounter1$PatientSource1$unbound_irdy (\LigeroRouter4$BBB3$RECEPTION1$CreditCounter1$PatientSource1$unbound_irdy )
    , .\BBB3$RECEPTION1$CreditCounter1$PatientSource1$unbound_data (\LigeroRouter4$BBB3$RECEPTION1$CreditCounter1$PatientSource1$unbound_data )
    , .\BBB3$RECEPTION1$CreditCounter1$PatientSource1$trdy (\LigeroRouter4$BBB3$RECEPTION1$CreditCounter1$PatientSource1$trdy )
    , .\BBB3$RECEPTION1$CreditCounter1$Sink1$unbound_trdy (\LigeroRouter4$BBB3$RECEPTION1$CreditCounter1$Sink1$unbound_trdy )
    , .\BBB3$RECEPTION1$CreditCounter1$Sink1$irdy (\LigeroRouter4$BBB3$RECEPTION1$CreditCounter1$Sink1$irdy )
    , .\BBB3$RECEPTION1$CreditCounter1$Sink1$data (\LigeroRouter4$BBB3$RECEPTION1$CreditCounter1$Sink1$data )
    , .\BBB4$Sink1$unbound_trdy (\LigeroRouter4$BBB4$Sink1$unbound_trdy )
    , .\BBB4$Sink1$irdy (\LigeroRouter4$BBB4$Sink1$irdy )
    , .\BBB4$Sink1$data (\LigeroRouter4$BBB4$Sink1$data )
    , .\BBB4$RECEPTION1$CreditCounter1$PatientSource1$unbound_irdy (\LigeroRouter4$BBB4$RECEPTION1$CreditCounter1$PatientSource1$unbound_irdy )
    , .\BBB4$RECEPTION1$CreditCounter1$PatientSource1$unbound_data (\LigeroRouter4$BBB4$RECEPTION1$CreditCounter1$PatientSource1$unbound_data )
    , .\BBB4$RECEPTION1$CreditCounter1$PatientSource1$trdy (\LigeroRouter4$BBB4$RECEPTION1$CreditCounter1$PatientSource1$trdy )
    , .\BBB4$RECEPTION1$CreditCounter1$Sink1$unbound_trdy (\LigeroRouter4$BBB4$RECEPTION1$CreditCounter1$Sink1$unbound_trdy )
    , .\BBB4$RECEPTION1$CreditCounter1$Sink1$irdy (\LigeroRouter4$BBB4$RECEPTION1$CreditCounter1$Sink1$irdy )
    , .\BBB4$RECEPTION1$CreditCounter1$Sink1$data (\LigeroRouter4$BBB4$RECEPTION1$CreditCounter1$Sink1$data )
  );
  
endmodule


